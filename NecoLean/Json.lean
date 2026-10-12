set_option autoImplicit false

namespace NecoLean.Json

inductive Number where
  | private make (text : String)
  deriving Repr, BEq

protected def Number.toString (number : Number) : String :=
  match number with
  | .make text => text

protected def Number.zero : Number := .make "0"

private def digit (character : Char) : Bool := character >= '0' && character <= '9'

private def validNumberText (text : String) : Bool :=
  let characters := text.toList
  let rec digits : List Char → Nat × List Char
    | character :: rest => if digit character then let result := digits rest; (result.1 + 1, result.2) else (0, character :: rest)
    | [] => (0, [])
  let afterSign := match characters with | '-' :: rest => rest | _ => characters
  let (integerCount, afterInteger) :=
    match afterSign with
    | '0' :: rest => (1, rest)
    | character :: rest => if character >= '1' && character <= '9' then let result := digits rest; (result.1 + 1, result.2) else (0, afterSign)
    | [] => (0, afterSign)
  if integerCount == 0 then false
  else
    let (fractionValid, afterFraction) :=
      match afterInteger with
      | '.' :: rest => let result := digits rest; (decide (result.1 > 0), result.2)
      | _ => (true, afterInteger)
    if !fractionValid then false
    else
      match afterFraction with
      | ('e' :: rest) | ('E' :: rest) =>
        let exponentRest := match rest with | ('+' :: tail) | ('-' :: tail) => tail | _ => rest
        let result := digits exponentRest
        result.1 > 0 && result.2.isEmpty
      | [] => true
      | _ => false

protected def Number.create (text : String) : Except String Number :=
  if validNumberText text then .ok (.make text) else .error text

inductive Value where
  | null
  | bool (value : Bool)
  | number (value : Number)
  | string (value : String)
  | array (values : List Value)
  | object (fields : List (String × Value))
  deriving Repr, BEq

inductive Failure where
  | invalid (offset : Nat) (message : String)
  | invalidUtf8 (offset : Nat)
  | unexpectedEnd (offset : Nat)
  | trailing (offset : Nat)
  | duplicateKey (offset : Nat) (key : String)
  deriving Repr, BEq

private structure Parser where
  bytes : ByteArray
  position : Nat

private def byteAt (bytes : ByteArray) (position : Nat) : UInt8 :=
  if h : position < bytes.size then bytes[position] else 0

private def Parser.peek (parser : Parser) : Option UInt8 :=
  if parser.position < parser.bytes.size then some (byteAt parser.bytes parser.position) else none

private def Parser.advance (parser : Parser) : Option (UInt8 × Parser) :=
  match parser.peek with
  | none => none
  | some byte => some (byte, { parser with position := parser.position + 1 })

private def isSpace (byte : UInt8) : Bool :=
  byte == 32 || byte == 9 || byte == 10 || byte == 13

private def spaceEnd (bytes : ByteArray) (position : Nat) : Nat :=
  if h : position < bytes.size then
    if isSpace bytes[position] then spaceEnd bytes (position + 1) else position
  else position
termination_by bytes.size - position

private def skipSpace (parser : Parser) : Parser :=
  { parser with position := spaceEnd parser.bytes parser.position }

private def digitsEnd (bytes : ByteArray) (position : Nat) : Nat :=
  if h : position < bytes.size then
    if bytes[position] >= 48 && bytes[position] <= 57 then digitsEnd bytes (position + 1) else position
  else position
termination_by bytes.size - position

private def parseToken (parser : Parser) (token : List UInt8) (value : Value) : Except Failure (Value × Parser) :=
  let rec loop (remaining : List UInt8) (state : Parser) : Except Failure (Value × Parser) :=
    match remaining with
    | [] => .ok (value, state)
    | expected :: rest =>
      match state.advance with
      | none => .error (.unexpectedEnd state.position)
      | some (actual, next) =>
        if actual == expected then loop rest next else .error (.invalid state.position "invalid token")
  loop token parser

private def hexValue (byte : UInt8) : Option Nat :=
  if byte >= 48 && byte <= 57 then some (byte.toNat - 48)
  else if byte >= 65 && byte <= 70 then some (byte.toNat - 55)
  else if byte >= 97 && byte <= 102 then some (byte.toNat - 87)
  else none

private def utf8Width (bytes : ByteArray) (position : Nat) : Option Nat :=
  if position >= bytes.size then none
  else
    let first := byteAt bytes position
    let second := byteAt bytes (position + 1)
    let third := byteAt bytes (position + 2)
    let fourth := byteAt bytes (position + 3)
    if first <= 127 then some 1
    else if first >= 194 && first <= 223 && second >= 128 && second <= 191 then some 2
    else if first == 224 && second >= 160 && second <= 191 && third >= 128 && third <= 191 then some 3
    else if first >= 225 && first <= 236 && second >= 128 && second <= 191 && third >= 128 && third <= 191 then some 3
    else if first == 237 && second >= 128 && second <= 159 && third >= 128 && third <= 191 then some 3
    else if first >= 238 && first <= 239 && second >= 128 && second <= 191 && third >= 128 && third <= 191 then some 3
    else if first == 240 && second >= 144 && second <= 191 && third >= 128 && third <= 191 && fourth >= 128 && fourth <= 191 then some 4
    else if first >= 241 && first <= 243 && second >= 128 && second <= 191 && third >= 128 && third <= 191 && fourth >= 128 && fourth <= 191 then some 4
    else if first == 244 && second >= 128 && second <= 143 && third >= 128 && third <= 191 && fourth >= 128 && fourth <= 191 then some 4
    else none

private def utf8Code (width : Nat) (bytes : ByteArray) (position : Nat) : Nat :=
  let first := (byteAt bytes position).toNat
  let second := (byteAt bytes (position + 1)).toNat
  let third := (byteAt bytes (position + 2)).toNat
  let fourth := (byteAt bytes (position + 3)).toNat
  match width with
  | 1 => first
  | 2 => (first - 192) * 64 + (second - 128)
  | 3 => (first - 224) * 4096 + (second - 128) * 64 + (third - 128)
  | 4 => (first - 240) * 262144 + (second - 128) * 4096 + (third - 128) * 64 + (fourth - 128)
  | _ => 0

private def utf8Char (bytes : ByteArray) (position : Nat) : Option (Char × Nat) :=
  match utf8Width bytes position with
  | some width => some (Char.ofNat (utf8Code width bytes position), width)
  | none => none

private def validateUtf8 (bytes : ByteArray) : Except Failure Unit :=
  let rec loop (position : Nat) (fuel : Nat) : Except Failure Unit :=
    match fuel with
    | 0 => .error (.invalidUtf8 position)
    | fuel + 1 =>
      if position >= bytes.size then .ok ()
      else
        match utf8Width bytes position with
        | some width => loop (position + width) fuel
        | none => .error (.invalidUtf8 position)
  loop 0 (bytes.size + 1)

private def parseUnicodeEscape (bytes : ByteArray) (position : Nat) : Option Nat :=
  if position + 4 > bytes.size then none
  else
    match hexValue (byteAt bytes position), hexValue (byteAt bytes (position + 1)),
      hexValue (byteAt bytes (position + 2)), hexValue (byteAt bytes (position + 3)) with
    | some a, some b, some c, some d => some (((a * 16 + b) * 16 + c) * 16 + d)
    | _, _, _, _ => none

private def simpleEscape (escaped : UInt8) : Option Char :=
  if escaped == 34 then some '"'
  else if escaped == 92 then some '\\'
  else if escaped == 47 then some '/'
  else if escaped == 98 then some '\x08'
  else if escaped == 102 then some '\x0c'
  else if escaped == 110 then some '\n'
  else if escaped == 114 then some '\r'
  else if escaped == 116 then some '\t'
  else none

private def parseStringLoop (bytes : ByteArray) (position : Nat) (fuel : Nat) (text : String) : Except Failure (String × Parser) :=
  match fuel with
  | 0 => .error (.unexpectedEnd position)
  | fuel + 1 =>
    if position >= bytes.size then .error (.unexpectedEnd position)
    else
      let byte := byteAt bytes position
      if byte == 34 then .ok (text, { bytes := bytes, position := position + 1 })
      else if byte < 32 then .error (.invalid position "control character in string")
      else if byte == 92 then
        if position + 1 >= bytes.size then .error (.unexpectedEnd (position + 1))
        else
          let escaped := byteAt bytes (position + 1)
          let nextPosition := position + 2
          match simpleEscape escaped with
          | some value => parseStringLoop bytes nextPosition fuel (text.push value)
          | none =>
            if escaped == 117 then
              match parseUnicodeEscape bytes nextPosition with
              | none => .error (.invalid nextPosition "invalid unicode escape")
              | some code =>
                if code >= 0xD800 && code <= 0xDBFF then
                  if byteAt bytes (nextPosition + 4) == 92 && byteAt bytes (nextPosition + 5) == 117 then
                    match parseUnicodeEscape bytes (nextPosition + 6) with
                    | some lowCode =>
                      if lowCode >= 0xDC00 && lowCode <= 0xDFFF then
                        let scalar := 0x10000 + (code - 0xD800) * 0x400 + (lowCode - 0xDC00)
                        parseStringLoop bytes (nextPosition + 10) fuel (text.push (Char.ofNat scalar))
                      else .error (.invalid nextPosition "invalid surrogate pair")
                    | none => .error (.invalid nextPosition "invalid surrogate pair")
                  else .error (.invalid nextPosition "lone surrogate")
                else if code >= 0xDC00 && code <= 0xDFFF then
                  .error (.invalid nextPosition "lone surrogate")
                else
                  parseStringLoop bytes (nextPosition + 4) fuel (text.push (Char.ofNat code))
            else .error (.invalid position "invalid escape")
      else
        match utf8Char bytes position with
        | some (character, width) => parseStringLoop bytes (position + width) fuel (text.push character)
        | none => .error (.invalidUtf8 position)

private def parseString (parser : Parser) : Except Failure (String × Parser) :=
  match parser.advance with
  | some (34, state) => parseStringLoop state.bytes state.position (state.bytes.size + 1 - state.position) ""
  | some (_, state) => .error (.invalid state.position "expected string")
  | none => .error (.unexpectedEnd parser.position)

private def parseNumber (parser : Parser) : Except Failure (Value × Parser) :=
  let bytes := parser.bytes
  let start := parser.position
  let signCount := if byteAt bytes start == 45 then 1 else 0
  let afterSign := start + signCount
  let first := byteAt bytes afterSign
  let integerEnd :=
    if first == 48 then afterSign + 1
    else if first >= 49 && first <= 57 then digitsEnd bytes (afterSign + 1)
    else afterSign
  if integerEnd == afterSign then .error (.invalid start "invalid number")
  else
    let fractionResult : Option Nat :=
      if byteAt bytes integerEnd == 46 then
        let digitsStop := digitsEnd bytes (integerEnd + 1)
        if digitsStop == integerEnd + 1 then none else some digitsStop
      else some integerEnd
    match fractionResult with
    | none => .error (.invalid integerEnd "invalid number")
    | some fractionEnd =>
      let exponentResult : Option Nat :=
        let exponent := byteAt bytes fractionEnd
        if exponent == 101 || exponent == 69 then
          let sign := byteAt bytes (fractionEnd + 1)
          let digitsStart := if sign == 43 || sign == 45 then fractionEnd + 2 else fractionEnd + 1
          let digitsStop := digitsEnd bytes digitsStart
          if digitsStop == digitsStart then none else some digitsStop
        else some fractionEnd
      match exponentResult with
      | none => .error (.invalid fractionEnd "invalid number")
      | some stop =>
        let text := String.ofList ((bytes.extract start stop).toList.map (fun byte => Char.ofNat byte.toNat))
        match Number.create text with
        | .ok number => .ok (.number number, { parser with position := stop })
        | .error _ => .error (.invalid start "invalid number")

private def nestingDepthLimit : Nat := 128

@[instance_reducible] private def parsedValueDefault : Inhabited (Value × Parser) :=
  ⟨(.null, { bytes := ByteArray.empty, position := 0 })⟩

attribute [local instance] parsedValueDefault

mutual
  private partial def parseValue (depth : Nat) (parser : Parser) : Except Failure (Value × Parser) :=
    let current := skipSpace parser
    match current.peek with
    | none => .error (.unexpectedEnd current.position)
    | some 110 => parseToken current [110,117,108,108] .null
    | some 116 => parseToken current [116,114,117,101] (.bool true)
    | some 102 => parseToken current [102,97,108,115,101] (.bool false)
    | some 34 =>
      match parseString current with | .ok (value, next) => .ok (.string value, next) | .error error => .error error
    | some 91 =>
      match depth with
      | 0 => .error (.invalid current.position "nesting limit")
      | depth + 1 => parseArray depth current
    | some 123 =>
      match depth with
      | 0 => .error (.invalid current.position "nesting limit")
      | depth + 1 => parseObject depth current
    | some 45 => parseNumber current
    | some byte => if byte >= 48 && byte <= 57 then parseNumber current else .error (.invalid current.position "unexpected byte")

  private partial def parseArray (depth : Nat) (parser : Parser) : Except Failure (Value × Parser) :=
    let afterOpen := { parser with position := parser.position + 1 } |> skipSpace
    if afterOpen.peek == some 93 then
      .ok (.array [], { afterOpen with position := afterOpen.position + 1 })
    else
      let rec loop (state : Parser) (values : List Value) : Except Failure (Value × Parser) :=
        match parseValue depth state with
        | .error failure => .error failure
        | .ok (value, afterValue) =>
          let next := skipSpace afterValue
          if next.peek == some 44 then loop ({ next with position := next.position + 1 } |> skipSpace) (value :: values)
          else if next.peek == some 93 then .ok (.array (values.reverse ++ [value]), { next with position := next.position + 1 })
          else .error (.invalid next.position "expected comma or closing array")
      loop afterOpen []

  private partial def parseObject (depth : Nat) (parser : Parser) : Except Failure (Value × Parser) :=
    let afterOpen := { parser with position := parser.position + 1 } |> skipSpace
    if afterOpen.peek == some 125 then
      .ok (.object [], { afterOpen with position := afterOpen.position + 1 })
    else
      let rec loop (state : Parser) (fields : List (String × Value)) : Except Failure (Value × Parser) :=
        match parseString state with
        | .error failure => .error failure
        | .ok (key, afterKey) =>
          let colon := skipSpace afterKey
          if colon.peek != some 58 then .error (.invalid colon.position "expected colon")
          else
            match parseValue depth ({ colon with position := colon.position + 1 } |> skipSpace) with
            | .error failure => .error failure
            | .ok (value, afterValue) =>
              if fields.any (fun field => field.1 == key) then .error (.duplicateKey state.position key)
              else
                let next := skipSpace afterValue
                if next.peek == some 44 then loop ({ next with position := next.position + 1 } |> skipSpace) ((key, value) :: fields)
                else if next.peek == some 125 then .ok (.object ((key, value) :: fields).reverse, { next with position := next.position + 1 })
                else .error (.invalid next.position "expected comma or closing object")
      loop afterOpen []
end

private def compareCodepoints : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | left :: leftRest, right :: rightRest =>
    if left < right then .lt
    else if left > right then .gt
    else compareCodepoints leftRest rightRest

private def compareKeys (left right : String) : Ordering :=
  compareCodepoints
    (left.toList.map (fun character => character.toNat))
    (right.toList.map (fun character => character.toNat))

private def canonicalFields (fields : List (String × Value)) : List (String × Value) :=
  fields.mergeSort (fun left right => compareKeys left.1 right.1 != .gt)

partial def canonicalize : Value → Value
  | .null => .null
  | .bool value => .bool value
  | .number value => .number value
  | .string value => .string value
  | .array values => .array (values.map canonicalize)
  | .object fields => .object ((canonicalFields fields).map (fun (key, value) => (key, canonicalize value)))

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat (48 + value) else Char.ofNat (87 + value)

private def unicodeEscape (character : Char) : String :=
  let value := character.toNat
  String.ofList ['\\', 'u', hexDigit ((value / 4096) % 16), hexDigit ((value / 256) % 16), hexDigit ((value / 16) % 16), hexDigit (value % 16)]

private def escapeStringCharacter (character : Char) : String :=
  if character == '"' then "\\\""
  else if character == '\\' then "\\\\"
  else if character.toNat == 8 then "\\b"
  else if character.toNat == 12 then "\\f"
  else if character.toNat == 10 then "\\n"
  else if character.toNat == 13 then "\\r"
  else if character.toNat == 9 then "\\t"
  else if character.toNat < 32 then unicodeEscape character
  else String.ofList [character]

private def duplicateField? (fields : List (String × Value)) : Option String :=
  let rec loop (remaining : List (String × Value)) : Option String :=
    match remaining with
    | [] => none
    | (key, _) :: rest => if rest.any (fun field => field.1 == key) then some key else loop rest
  loop fields

partial def encodeText : Value → Except Failure String
  | .null => .ok "null"
  | .bool true => .ok "true"
  | .bool false => .ok "false"
  | .number number => .ok (Number.toString number)
  | .string text =>
    let escaped := text.toList.foldl (fun result character => result ++ escapeStringCharacter character) ""
    .ok ("\"" ++ escaped ++ "\"")
  | .array values =>
    match values.mapM encodeText with
    | .ok items => .ok ("[" ++ String.intercalate "," items ++ "]")
    | .error failure => .error failure
  | .object fields =>
    match duplicateField? fields with
    | some key => .error (.duplicateKey 0 key)
    | none =>
      match (canonicalFields fields).mapM (fun (key, item) =>
        match encodeText (.string key), encodeText item with
        | .ok encodedKey, .ok encodedItem => Except.ok (encodedKey ++ ":" ++ encodedItem)
        | .error failure, _ => Except.error failure
        | _, .error failure => Except.error failure) with
      | .ok items => Except.ok ("{" ++ String.intercalate "," items ++ "}")
      | .error failure => Except.error failure

protected def encode (value : Value) : Except Failure ByteArray :=
  match encodeText (canonicalize value) with
  | .ok text => .ok text.toUTF8
  | .error failure => .error failure

protected def decode (bytes : ByteArray) : Except Failure Value :=
  match validateUtf8 bytes with
  | .error failure => .error failure
  | .ok () =>
    match parseValue nestingDepthLimit { bytes := bytes, position := 0 } with
    | .error failure => .error failure
    | .ok (value, parser) =>
      let final := skipSpace parser
      if final.position == bytes.size then .ok (canonicalize value)
      else .error (.trailing final.position)

end NecoLean.Json
