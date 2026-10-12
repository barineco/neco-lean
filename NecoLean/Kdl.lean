set_option autoImplicit false

namespace NecoLean.Kdl

structure Position where
  line : Nat
  column : Nat
  byteOffset : Nat
  deriving Repr, BEq, DecidableEq

structure Span where
  start : Position
  «end» : Position
  deriving Repr, BEq, DecidableEq

inductive ErrorKind where
  | unexpectedChar (character : Char)
  | unexpectedEof
  | bareKeyword
  | invalidNumber
  | invalidEscape
  | invalidUnicodeEscape
  | unclosedString
  | unclosedBlockComment
  | disallowedCodePoint (character : Char)
  | inconsistentIndentation
  | invalidSlashdash
  | invalidNode
  deriving Repr, BEq, DecidableEq

inductive DocumentFailure where
  | invalidUtf8 (byteOffset : Nat)
  | parseFailure (position : Position) (kind : ErrorKind)
  deriving Repr, BEq, DecidableEq

structure Number where
  private mk ::
  raw : String
  asInt : Option Int
  asFloat : Option Float
  deriving Repr, BEq

inductive BuilderFailure where
  | emptyNumber
  | invalidNumber (raw : String)
  deriving Repr, BEq, DecidableEq

inductive Value where
  | string (value : String)
  | number (value : Number)
  | boolean (value : Bool)
  | null
  deriving Repr, BEq

structure Argument where
  typeAnnotation : Option String
  value : Value
  deriving Repr, BEq

structure Property where
  typeAnnotation : Option String
  name : String
  value : Value
  deriving Repr, BEq

inductive Entry where
  | argument (value : Argument)
  | property (value : Property)
  deriving Repr, BEq

mutual
  inductive Node where
    | make (typeAnnotation : Option String) (name : String) (entries : List Entry)
        (children : Option Document)
    deriving Repr, BEq

  inductive Document where
    | make (nodes : List Node)
    deriving Repr, BEq
end

instance : Inhabited Node := ⟨.make none "" [] none⟩
instance : Inhabited Document := ⟨.make []⟩

structure PositionedArgument where
  typeAnnotation : Option String
  value : Value
  span : Span
  deriving Repr, BEq

structure PositionedProperty where
  typeAnnotation : Option String
  name : String
  value : Value
  span : Span
  deriving Repr, BEq

inductive PositionedEntry where
  | argument (value : PositionedArgument)
  | property (value : PositionedProperty)
  deriving Repr, BEq

mutual
  inductive PositionedNode where
    | make (typeAnnotation : Option String) (name : String)
        (entries : List PositionedEntry) (children : Option PositionedDocument) (span : Span)
    deriving Repr, BEq

  inductive PositionedDocument where
    | make (nodes : List PositionedNode)
    deriving Repr, BEq
end

instance : Inhabited PositionedNode :=
  ⟨.make none "" [] none { start := { line := 1, column := 1, byteOffset := 0 }, «end» := { line := 1, column := 1, byteOffset := 0 } }⟩
instance : Inhabited PositionedDocument := ⟨.make []⟩

structure ParseResult where
  positioned : PositionedDocument
  plain : Document
  deriving Repr, BEq

private def PositionedArgument.toPlain (value : PositionedArgument) : Argument :=
  { typeAnnotation := value.typeAnnotation, value := value.value }

private def PositionedProperty.toPlain (value : PositionedProperty) : Property :=
  { typeAnnotation := value.typeAnnotation, name := value.name, value := value.value }

private def PositionedEntry.toPlain : PositionedEntry → Entry
  | .argument value => .argument value.toPlain
  | .property value => .property value.toPlain

mutual
  private partial def positionedNodeToPlain : PositionedNode → Node
    | .make typeAnnotation name entries children _ =>
      .make typeAnnotation name (entries.map PositionedEntry.toPlain)
        (children.map positionedDocumentToPlain)

  private partial def positionedDocumentToPlain : PositionedDocument → Document
    | .make nodes => .make (nodes.map positionedNodeToPlain)
end

protected def PositionedDocument.toPlain (value : PositionedDocument) : Document :=
  positionedDocumentToPlain value

private structure ValidatedUtf8Text where
  input : ByteArray
  text : String

private structure Utf8ParseState where
  input : ByteArray
  position : Position
  text : ValidatedUtf8Text

private structure Parser where
  remaining : List Char
  position : Position

private def initialPosition : Position := { line := 1, column := 1, byteOffset := 0 }

private def charWidth (character : Char) : Nat :=
  (String.singleton character).toUTF8.size

private def advancePosition (position : Position) (character : Char) : Position :=
  if character == '\n' || character == '\r' then
    { line := position.line + 1, column := 1, byteOffset := position.byteOffset + charWidth character }
  else
    { line := position.line, column := position.column + 1, byteOffset := position.byteOffset + charWidth character }

private def Parser.peek (parser : Parser) : Option Char := parser.remaining.head?

private def Parser.peekSecond (parser : Parser) : Option Char :=
  match parser.remaining with
  | _ :: second :: _ => some second
  | _ => none

private def Parser.advance (parser : Parser) : Option (Char × Parser) :=
  match parser.remaining with
  | [] => none
  | '\r' :: '\n' :: rest =>
    some ('\n', { remaining := rest, position := { line := parser.position.line + 1, column := 1, byteOffset := parser.position.byteOffset + 2 } })
  | character :: rest =>
    some (character, { remaining := rest, position := advancePosition parser.position character })

private def Parser.consume (parser : Parser) (expected : Char) : Except DocumentFailure Parser :=
  match parser.advance with
  | none => .error (.parseFailure parser.position .unexpectedEof)
  | some (actual, next) =>
    if actual == expected then .ok next
    else .error (.parseFailure parser.position (.unexpectedChar actual))

private def Parser.consumeToken (parser : Parser) (token : String) : Option Parser :=
  let rec loop (state : Parser) : List Char → Option Parser
    | [] => some state
    | expected :: rest =>
      match state.advance with
      | some (actual, next) => if actual == expected then loop next rest else none
      | none => none
  loop parser token.toList

private def failure (parser : Parser) (kind : ErrorKind) : DocumentFailure :=
  .parseFailure parser.position kind

private def isNewline (character : Char) : Bool :=
  character == '\n' || character == '\r' || character == '\x0b' ||
    character == '\x0c' || character == '\u0085' || character == '\u2028' ||
    character == '\u2029'

private def isHorizontalSpace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\u00a0' ||
    character == '\u1680' || character == '\u202f' || character == '\u205f' ||
    character == '\u3000' ||
    (character.val >= 0x2000 && character.val <= 0x200a)

private def isDisallowed (character : Char) : Bool :=
  character.val <= 8 ||
    (character.val >= 0x0e && character.val <= 0x1f) ||
    character.val == 0x7f ||
    (character.val >= 0x200e && character.val <= 0x200f) ||
    (character.val >= 0x202a && character.val <= 0x202e) ||
    (character.val >= 0x2066 && character.val <= 0x2069) ||
    character.val == 0xfeff

private def isIdentifierCharacter (character : Char) : Bool :=
  !isHorizontalSpace character && !isNewline character && !isDisallowed character &&
    !['\\', '/', '(', ')', '{', '}', ';', '[', ']', '"', '#', '='].contains character

private def isDecimalDigit (character : Char) : Bool :=
  character >= '0' && character <= '9'

private def isHexDigit (character : Char) : Bool :=
  isDecimalDigit character || (character >= 'a' && character <= 'f') ||
    (character >= 'A' && character <= 'F')

private partial def skipHorizontal (parser : Parser) : Parser :=
  let rec loop (state : Parser) : Parser :=
    match state.peek with
    | some character =>
      if isHorizontalSpace character then
        match state.advance with
        | some (_, next) => loop next
        | none => state
      else state
    | none => state
  loop parser

private partial def skipBlockComment (parser : Parser) : Except DocumentFailure Parser :=
  match parser.remaining with
  | '/' :: '*' :: _ =>
    let afterOpen := (parser.consume '/').bind (fun state => state.consume '*')
    afterOpen.bind fun opened =>
      let rec loop (state : Parser) (depth : Nat) : Except DocumentFailure Parser :=
        match state.remaining with
        | [] => .error (failure state .unclosedBlockComment)
        | '/' :: '*' :: _ =>
          (state.consume '/').bind fun s1 =>
            (s1.consume '*').bind fun s2 => loop s2 (depth + 1)
        | '*' :: '/' :: _ =>
          (state.consume '*').bind fun s1 =>
            (s1.consume '/').bind fun s2 =>
              if depth == 1 then .ok s2 else loop s2 (depth - 1)
        | _ =>
          match state.advance with
          | some (_, next) => loop next depth
          | none => .error (failure state .unclosedBlockComment)
      loop opened 1
  | _ => .ok parser

private partial def skipLineComment (parser : Parser) : Parser :=
  match parser.remaining with
  | '/' :: '/' :: _ =>
    let rec loop (state : Parser) : Parser :=
      match state.peek with
      | some character =>
        if isNewline character then state
        else match state.advance with
          | some (_, next) => loop next
          | none => state
      | none => state
    match (parser.consume '/').bind (fun state => state.consume '/') with
    | .ok state => loop state
    | .error _ => parser
  | _ => parser

private partial def skipNodeSpace (parser : Parser) : Except DocumentFailure (Bool × Parser) :=
  let rec loop (state : Parser) (consumed : Bool) : Except DocumentFailure (Bool × Parser) :=
    let horizontal := skipHorizontal state
    let consumed := consumed || horizontal.position.byteOffset != state.position.byteOffset
    match horizontal.remaining with
    | '/' :: '*' :: _ =>
      (skipBlockComment horizontal).bind fun next => loop next true
    | '\\' :: _ =>
      match horizontal.advance with
      | none => .error (failure horizontal .unexpectedEof)
      | some (_, afterSlash) =>
        let afterSpace := skipHorizontal afterSlash
        match afterSpace.remaining with
        | '/' :: '/' :: _ =>
          let afterComment := skipLineComment afterSpace
          match afterComment.advance with
          | some (_, next) => loop next true
          | none => .error (failure afterComment .unexpectedEof)
        | '/' :: '*' :: _ =>
          (skipBlockComment afterSpace).bind fun afterComment =>
            let nextSpace := skipHorizontal afterComment
            match nextSpace.peek with
            | some newline =>
              if isNewline newline then
                match nextSpace.advance with
                | some (_, next) => loop next true
                | none => .error (failure nextSpace .unexpectedEof)
              else .error (failure nextSpace (.unexpectedChar newline))
            | none => .error (failure nextSpace .unexpectedEof)
        | _ =>
          match afterSpace.peek with
          | some newline =>
            if isNewline newline then
              match afterSpace.advance with
              | some (_, next) => loop next true
              | none => .error (failure afterSpace .unexpectedEof)
            else .error (failure afterSpace (.unexpectedChar newline))
          | none => .ok (true, afterSpace)
    | _ => .ok (consumed, horizontal)
  loop parser false

private partial def skipLineSpace (parser : Parser) : Except DocumentFailure Parser :=
  let rec loop (state : Parser) : Except DocumentFailure Parser :=
    (skipNodeSpace state).bind fun (_, spaced) =>
      match spaced.remaining with
      | '/' :: '/' :: _ =>
        let commented := skipLineComment spaced
        match commented.advance with
        | some (_, next) => loop next
        | none => .ok commented
      | _ =>
        match spaced.peek with
        | some character =>
          if isNewline character then
            match spaced.advance with
            | some (_, next) => loop next
            | none => .ok spaced
          else .ok spaced
        | none => .ok spaced
  loop parser

private partial def collectWhile (parser : Parser) (predicate : Char → Bool) : String × Parser :=
  let rec loop (state : Parser) (acc : List Char) : String × Parser :=
    match state.peek with
    | some character =>
      if predicate character then
        match state.advance with
        | some (_, next) => loop next (character :: acc)
        | none => (String.ofList acc.reverse, state)
      else (String.ofList acc.reverse, state)
    | none => (String.ofList acc.reverse, state)
  loop parser []

private def reservedBareKeyword (value : String) : Bool :=
  ["true", "false", "null", "inf", "-inf", "nan"].contains value

private def takeIdentifier (parser : Parser) : Except DocumentFailure (String × Parser) :=
  let (value, next) := collectWhile parser isIdentifierCharacter
  if value.isEmpty then
    match parser.peek with
    | some character => .error (failure parser (.unexpectedChar character))
    | none => .error (failure parser .unexpectedEof)
  else if reservedBareKeyword value then .error (failure parser .bareKeyword)
  else if isDecimalDigit value.front then .error (failure parser .invalidNumber)
  else .ok (value, next)

private def hexValue (character : Char) : Option Nat :=
  if character >= '0' && character <= '9' then some (character.val - '0'.val).toNat
  else if character >= 'a' && character <= 'f' then some ((character.val - 'a'.val).toNat + 10)
  else if character >= 'A' && character <= 'F' then some ((character.val - 'A'.val).toNat + 10)
  else none

private def decodeUnicodeScalar (digits : List Char) : Option Char :=
  if digits.isEmpty || digits.length > 6 then none
  else
    let value? := digits.foldl (fun acc character =>
      acc.bind fun value => (hexValue character).map fun digit => value * 16 + digit) (some 0)
    value?.bind fun value =>
      if value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff) then none
      else Char.ofNat value

private partial def consumeEscapedWhitespace (parser : Parser) : Parser :=
  match parser.peek with
  | some character =>
    if isHorizontalSpace character || isNewline character then
      match parser.advance with
      | some (_, next) => consumeEscapedWhitespace next
      | none => parser
    else parser
  | none => parser

private partial def takeSingleQuotedString (parser : Parser) : Except DocumentFailure (String × Parser) := do
  let state ← parser.consume '"'
  let rec loop (state : Parser) (acc : List Char) : Except DocumentFailure (String × Parser) := do
    match state.peek with
    | none => .error (failure state .unclosedString)
    | some '"' =>
      let next ← state.consume '"'
      .ok (String.ofList acc.reverse, next)
    | some '\\' =>
      let afterSlash ← state.consume '\\'
      match afterSlash.peek with
      | none => .error (failure afterSlash .unclosedString)
      | some 'u' =>
        let afterU ← afterSlash.consume 'u'
        let afterOpen ← afterU.consume '{'
        let (digits, beforeClose) := collectWhile afterOpen isHexDigit
        let afterClose ← beforeClose.consume '}'
        match decodeUnicodeScalar digits.toList with
        | some scalar => loop afterClose (scalar :: acc)
        | none => .error (failure afterU .invalidUnicodeEscape)
      | some escaped =>
        if isHorizontalSpace escaped || isNewline escaped then
          loop (consumeEscapedWhitespace afterSlash) acc
        else
          let next ← afterSlash.consume escaped
          let decoded? :=
            match escaped with
            | 'n' => some '\n' | 'r' => some '\r' | 't' => some '\t'
            | 'b' => some '\x08' | 'f' => some '\x0c' | 's' => some ' '
            | '\\' => some '\\' | '"' => some '"' | _ => none
          match decoded? with
          | some decoded => loop next (decoded :: acc)
          | none => .error (failure afterSlash .invalidEscape)
    | some character =>
      if isNewline character then .error (failure state .unclosedString)
      else if isDisallowed character then .error (failure state (.disallowedCodePoint character))
      else
        match state.advance with
        | some (_, next) => loop next (character :: acc)
        | none => .error (failure state .unclosedString)
  loop state []

private structure QuotedMultilineCharacter where
  value : Char
  isLiteral : Bool

private def stripQuotedIndent (lines : List (List QuotedMultilineCharacter)) : Except ErrorKind String :=
  match lines.reverse with
  | [] => .ok ""
  | closingIndent :: reversedBody =>
    if !closingIndent.all (fun character => character.isLiteral && isHorizontalSpace character.value) then
      .error .inconsistentIndentation
    else
      let body := reversedBody.reverse
      let rec removePrefix (indentation line : List QuotedMultilineCharacter) : Option (List QuotedMultilineCharacter) :=
        match indentation, line with
        | [], rest => some rest
        | expected :: expectedRest, actual :: actualRest =>
          if actual.isLiteral && expected.value == actual.value then
            removePrefix expectedRest actualRest
          else none
        | _ :: _, [] => none
      let decoded? := body.map fun line =>
        if line.all (fun character => character.isLiteral && isHorizontalSpace character.value) then
          some ""
        else
          (removePrefix closingIndent line).map fun rest => String.ofList (rest.map (·.value))
      if decoded?.all Option.isSome then
        .ok (String.intercalate "\n" (decoded?.filterMap id))
      else .error .inconsistentIndentation

private def stripIndent (lines : List String) : Except ErrorKind String :=
  match lines.reverse with
  | [] => .ok ""
  | closingIndent :: reversedBody =>
    if !closingIndent.toList.all isHorizontalSpace then .error .inconsistentIndentation
    else
      let body := reversedBody.reverse
      let rec removePrefix (pre chars : List Char) : Option (List Char) :=
        match pre, chars with
        | [], rest => some rest
        | p :: ps, c :: cs => if p == c then removePrefix ps cs else none
        | _ :: _, [] => none
      let trimmed? := body.map fun line =>
        if line.toList.all isHorizontalSpace then some ""
        else (removePrefix closingIndent.toList line.toList).map String.ofList
      if trimmed?.all Option.isSome then
        .ok (String.intercalate "\n" (trimmed?.filterMap id))
      else .error .inconsistentIndentation

private partial def takeMultilineQuotedString (parser : Parser) : Except DocumentFailure (String × Parser) := do
  let s1 ← parser.consume '"'
  let s2 ← s1.consume '"'
  let s3 ← s2.consume '"'
  match s3.peek with
  | some newline => if !isNewline newline then .error (failure s3 .unclosedString)
  | none => throw (failure s3 .unclosedString)
  let afterNewline := (s3.advance.getD ('\n', s3)).2
  let rec loop (state : Parser) (lines : List (List QuotedMultilineCharacter))
      (current : List QuotedMultilineCharacter) : Except DocumentFailure (String × Parser) := do
    match state.remaining with
    | '"' :: '"' :: '"' :: _ =>
      let s1 ← state.consume '"'
      let s2 ← s1.consume '"'
      let s3 ← s2.consume '"'
      match stripQuotedIndent (lines.reverse ++ [current.reverse]) with
      | .ok value => .ok (value, s3)
      | .error kind => .error (failure state kind)
    | _ =>
      match state.peek with
      | none => .error (failure state .unclosedString)
      | some '\\' =>
        let afterSlash ← state.consume '\\'
        match afterSlash.peek with
        | none => .error (failure afterSlash .invalidEscape)
        | some escaped =>
          if isHorizontalSpace escaped || isNewline escaped then
            loop (consumeEscapedWhitespace afterSlash) lines current
          else if escaped == 'u' then
            let afterU ← afterSlash.consume 'u'
            let afterOpen ← afterU.consume '{'
            let (digits, beforeClose) := collectWhile afterOpen isHexDigit
            let afterClose ← beforeClose.consume '}'
            match decodeUnicodeScalar digits.toList with
            | some scalar => loop afterClose lines ({ value := scalar, isLiteral := false } :: current)
            | none => .error (failure afterU .invalidUnicodeEscape)
          else
            let next ← afterSlash.consume escaped
            let decoded? :=
              match escaped with
              | 'n' => some '\n' | 'r' => some '\r' | 't' => some '\t'
              | 'b' => some '\x08' | 'f' => some '\x0c' | 's' => some ' '
              | '\\' => some '\\' | '"' => some '"' | _ => none
            match decoded? with
            | some decoded => loop next lines ({ value := decoded, isLiteral := false } :: current)
            | none => .error (failure afterSlash .invalidEscape)
      | some character =>
        if isNewline character then
          match state.advance with
          | some (_, next) => loop next (current.reverse :: lines) []
          | none => .error (failure state .unclosedString)
        else if isDisallowed character then .error (failure state (.disallowedCodePoint character))
        else match state.advance with
          | some (_, next) => loop next lines ({ value := character, isLiteral := true } :: current)
          | none => .error (failure state .unclosedString)
  loop afterNewline [] []

private def startsWithChars (remaining pre : List Char) : Bool :=
  match pre, remaining with
  | [], _ => true
  | _, [] => false
  | p :: ps, r :: rs => p == r && startsWithChars rs ps

private partial def takeRawString (parser : Parser) : Except DocumentFailure (String × Parser) := do
  let (hashes, afterHashes) := collectWhile parser (fun character => character == '#')
  if hashes.isEmpty then .error (failure parser .invalidNode) else
  let availableQuotes := afterHashes.remaining.takeWhile (fun character => character == '"') |>.length
  let quoteCount := if availableQuotes >= 3 then 3 else 1
  if availableQuotes == 0 then .error (failure parser .unclosedString) else
  let rec consumeQuotes (state : Parser) : Nat → Except DocumentFailure Parser
    | 0 => .ok state
    | count + 1 => (state.consume '"').bind fun next => consumeQuotes next count
  let bodyStart ← consumeQuotes afterHashes quoteCount
  let multiline := quoteCount == 3
  let bodyStart ←
    if multiline then
      match bodyStart.peek with
      | some newline =>
        if isNewline newline then .ok ((bodyStart.advance.getD ('\n', bodyStart)).2)
        else .error (failure bodyStart .unclosedString)
      | none => .error (failure bodyStart .unclosedString)
    else .ok bodyStart
  let closer := List.replicate quoteCount '"' ++ hashes.toList
  let rec loop (state : Parser) (lines : List String) (current : List Char) : Except DocumentFailure (String × Parser) := do
    if startsWithChars state.remaining closer then
      let rec consumeCloser (s : Parser) : List Char → Except DocumentFailure Parser
        | [] => .ok s
        | character :: rest => (s.consume character).bind fun next => consumeCloser next rest
      let next ← consumeCloser state closer
      if multiline then
        match stripIndent (lines.reverse ++ [String.ofList current.reverse]) with
        | .ok value => .ok (value, next)
        | .error kind => .error (failure state kind)
      else .ok (String.ofList current.reverse, next)
    else
      match state.peek with
      | none => .error (failure state .unclosedString)
      | some character =>
        if isNewline character then
          if multiline then
            match state.advance with
            | some (_, next) => loop next (String.ofList current.reverse :: lines) []
            | none => .error (failure state .unclosedString)
          else .error (failure state .unclosedString)
        else if isDisallowed character then .error (failure state (.disallowedCodePoint character))
        else match state.advance with
          | some (_, next) => loop next lines (character :: current)
          | none => .error (failure state .unclosedString)
  loop bodyStart [] []

private def takeString (parser : Parser) : Except DocumentFailure (String × Parser) :=
  match parser.remaining with
  | '"' :: '"' :: '"' :: _ => takeMultilineQuotedString parser
  | '"' :: _ => takeSingleQuotedString parser
  | '#' :: _ => takeRawString parser
  | _ => takeIdentifier parser

private def cleanUnderscores (value : String) : String :=
  String.ofList (value.toList.filter fun character => character != '_')

private def numberStart (parser : Parser) : Bool :=
  match parser.remaining with
  | sign :: second :: third :: _ =>
    if sign == '+' || sign == '-' then isDecimalDigit second || (second == '.' && isDecimalDigit third)
    else if sign == '.' then isDecimalDigit second
    else isDecimalDigit sign
  | sign :: second :: _ =>
    if sign == '+' || sign == '-' then isDecimalDigit second
    else if sign == '.' then isDecimalDigit second
    else isDecimalDigit sign
  | character :: _ => isDecimalDigit character
  | [] => false

private def validateDigits (digits : List Char) (predicate : Char → Bool) : Bool :=
  match digits with
  | first :: _ => predicate first && digits.all (fun character => character == '_' || predicate character)
  | [] => false

private def validDecimalNumber (chars : List Char) : Bool :=
  let unsigned := match chars with | sign :: rest => if sign == '+' || sign == '-' then rest else chars | _ => chars
  let rec takeDigits : List Char → List Char × List Char
    | [] => ([], [])
    | character :: rest =>
      if isDecimalDigit character || character == '_' then
        let (taken, remaining) := takeDigits rest
        (character :: taken, remaining)
      else ([], character :: rest)
  let (integer, afterInteger) := takeDigits unsigned
  if !validateDigits integer isDecimalDigit then false else
  let (fractionValid, afterFraction) :=
    match afterInteger with
    | '.' :: rest =>
      let (fraction, remaining) := takeDigits rest
      (validateDigits fraction isDecimalDigit, remaining)
    | rest => (true, rest)
  if !fractionValid then false else
  match afterFraction with
  | [] => true
  | marker :: rest =>
    if marker == 'e' || marker == 'E' then
      let exponent := match rest with | sign :: digits => if sign == '+' || sign == '-' then digits else rest | [] => []
      validateDigits exponent isDecimalDigit
    else false

private def validNumberRaw (raw : String) : Bool :=
  if raw == "#inf" || raw == "#-inf" || raw == "#nan" then true
  else
    let chars := raw.toList
    let unsigned := match chars with | sign :: rest => if sign == '+' || sign == '-' then rest else chars | _ => chars
    match unsigned with
    | '0' :: marker :: digits =>
      if marker == 'x' || marker == 'X' then validateDigits digits isHexDigit
      else if marker == 'o' || marker == 'O' then validateDigits digits (fun c => c >= '0' && c <= '7')
      else if marker == 'b' || marker == 'B' then validateDigits digits (fun c => c == '0' || c == '1')
      else
        let allowed c := isDecimalDigit c || c == '_' || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'
        !chars.isEmpty && chars.all allowed && chars.any isDecimalDigit
    | _ => validDecimalNumber chars

private partial def decimalFloat? (raw : String) : Option Float :=
  let clean := cleanUnderscores raw
  let (negative, unsigned) :=
    match clean.toList with
    | '-' :: rest => (true, String.ofList rest)
    | '+' :: rest => (false, String.ofList rest)
    | _ => (false, clean)
  let exponentParts := unsigned.splitOn "e"
  let exponentParts := if exponentParts.length == 1 then unsigned.splitOn "E" else exponentParts
  match exponentParts with
  | [mantissa] | [mantissa, ""] =>
    let mantissaParts := mantissa.splitOn "."
    match mantissaParts with
    | [whole] => whole.toNat?.map fun value => if negative then Float.neg (Float.ofNat value) else Float.ofNat value
    | [whole, fraction] => do
      let wholeValue ← whole.toNat?
      let fractionValue ← fraction.toNat?
      let value := Float.ofScientific (wholeValue * 10 ^ fraction.length + fractionValue) true fraction.length
      some (if negative then Float.neg value else value)
    | _ => none
  | [mantissa, exponent] => do
    let mantissaValue ← decimalFloat? (if negative then "-" ++ mantissa else mantissa)
    let exponentValue ← exponent.toInt?
    let scale := Float.ofScientific 1 false exponentValue.natAbs
    some (if exponentValue < 0 then Float.div mantissaValue scale else Float.mul mantissaValue scale)
  | _ => none

private def numberProjections (raw : String) : Option Int × Option Float :=
  let clean := cleanUnderscores raw
  let radix := clean.startsWith "0x" || clean.startsWith "0X" || clean.startsWith "0o" ||
    clean.startsWith "0O" || clean.startsWith "0b" || clean.startsWith "0B"
  let asInt := if clean.contains "." || clean.contains "e" || clean.contains "E" || radix then none else clean.toInt?
  let asFloat := if radix || raw.startsWith "#" then none else decimalFloat? raw
  (asInt, asFloat)

private def numberFromRaw (raw : String) : Except BuilderFailure Number :=
  if raw.isEmpty then .error .emptyNumber
  else if !validNumberRaw raw then .error (.invalidNumber raw)
  else
    let (asInt, asFloat) := numberProjections raw
    .ok (.mk raw asInt asFloat)

private def parseNumber (parser : Parser) : Except DocumentFailure (Number × Parser) :=
  let (raw, next) := collectWhile parser isIdentifierCharacter
  match numberFromRaw raw with
  | .ok number => .ok (number, next)
  | .error _ => .error (failure parser .invalidNumber)

private def parseValue (parser : Parser) : Except DocumentFailure (Value × Parser) :=
  let keyword (token : String) (value : Value) : Option (Value × Parser) :=
    (parser.consumeToken token).map fun next => (value, next)
  let keywordNumber (token : String) : Option (Value × Parser) :=
    match numberFromRaw token with
    | .ok number => keyword token (.number number)
    | .error _ => none
  match keyword "#true" (.boolean true) with
  | some result => .ok result
  | none => match keyword "#false" (.boolean false) with
    | some result => .ok result
    | none => match keyword "#null" .null with
      | some result => .ok result
      | none => match keywordNumber "#-inf" with
        | some result => .ok result
        | none => match keywordNumber "#inf" with
          | some result => .ok result
          | none => match keywordNumber "#nan" with
            | some result => .ok result
            | none =>
              if numberStart parser then (parseNumber parser).map fun (value, next) => (.number value, next)
              else (takeString parser).map fun (value, next) => (.string value, next)

private def parseTypeAnnotation (parser : Parser) : Except DocumentFailure (Option String × Parser) :=
  match parser.peek with
  | some '(' => do
    let afterOpen ← parser.consume '('
    let (_, spaced) ← skipNodeSpace afterOpen
    let (annotation, afterName) ← takeString spaced
    let (_, beforeClose) ← skipNodeSpace afterName
    let afterClose ← beforeClose.consume ')'
    .ok (some annotation, afterClose)
  | _ => .ok (none, parser)

private def parseEntry (parser : Parser) : Except DocumentFailure (PositionedEntry × Parser) := do
  let start := parser.position
  let (annotation, afterAnnotation) ← parseTypeAnnotation parser
  let (_, valueStart) ← if annotation.isSome then skipNodeSpace afterAnnotation else .ok (false, afterAnnotation)
  let (first, afterFirst) ← parseValue valueStart
  let afterKeySpace := skipHorizontal afterFirst
  match afterKeySpace.peek, annotation, first with
  | some '=', none, .string name =>
    let afterEq ← afterKeySpace.consume '='
    let valueSpace := skipHorizontal afterEq
    let (valueAnnotation, afterValueAnnotation) ← parseTypeAnnotation valueSpace
    let (_, actualValueStart) ← if valueAnnotation.isSome then skipNodeSpace afterValueAnnotation else .ok (false, afterValueAnnotation)
    let (value, next) ← parseValue actualValueStart
    .ok (.property { typeAnnotation := valueAnnotation, name := name, value := value, span := { start := start, «end» := next.position } }, next)
  | some '=', some _, _ => .error (failure afterKeySpace (.unexpectedChar '='))
  | _, _, value =>
    .ok (.argument { typeAnnotation := annotation, value := value, span := { start := start, «end» := afterFirst.position } }, afterFirst)

mutual
  private partial def parseNode (parser : Parser) : Except DocumentFailure (PositionedNode × Parser) := do
    let start := parser.position
    let (annotation, afterAnnotation) ← parseTypeAnnotation parser
    let (_, nameStart) ← if annotation.isSome then skipNodeSpace afterAnnotation else .ok (false, afterAnnotation)
    let (name, afterName) ← takeString nameStart
    let rec loop (state : Parser) (entries : List PositionedEntry)
        (children : Option PositionedDocument) : Except DocumentFailure
          (List PositionedEntry × Option PositionedDocument × Parser) := do
      let (hadSpace, spaced) ← skipNodeSpace state
      match spaced.remaining with
      | '/' :: '/' :: _ => .ok (entries.reverse, children, spaced)
      | '/' :: '-' :: _ =>
        let afterSlash ← spaced.consume '/'
        let afterDash ← afterSlash.consume '-'
        let afterDiscardSpace ← skipLineSpace afterDash
        match afterDiscardSpace.peek with
        | none | some ';' | some '}' => .error (failure afterDiscardSpace .invalidSlashdash)
        | some '{' =>
          let childStart ← afterDiscardSpace.consume '{'
          let (_, afterDiscarded) ← parseDocument childStart true
          let (_, afterDiscardSpace) ← skipNodeSpace afterDiscarded
          match afterDiscardSpace.peek with
          | none | some ';' | some '}' => .ok (entries.reverse, children, afterDiscardSpace)
          | some character =>
            if isNewline character then .ok (entries.reverse, children, afterDiscardSpace)
            else if afterDiscardSpace.remaining.take 2 == ['/', '-'] then loop afterDiscardSpace entries children
            else if character == '{' && children.isNone then loop afterDiscardSpace entries children
            else .error (failure afterDiscardSpace .invalidSlashdash)
        | _ =>
          let (_, afterDiscarded) ← parseEntry afterDiscardSpace
          loop afterDiscarded entries children
      | '{' :: _ =>
        if children.isSome then .error (failure spaced .invalidNode) else
          let childStart ← spaced.consume '{'
          let (parsedChildren, afterChildren) ← parseDocument childStart true
          loop afterChildren entries (some parsedChildren)
      | _ =>
        match spaced.peek with
        | none | some ';' | some '}' => .ok (entries.reverse, children, spaced)
        | some character =>
          if isNewline character then .ok (entries.reverse, children, spaced)
          else if hadSpace then
            let (entry, next) ← parseEntry spaced
            loop next (entry :: entries) children
          else .ok (entries.reverse, children, spaced)
    let (entries, children, after) ← loop afterName [] none
    .ok (.make annotation name entries children { start := start, «end» := after.position }, after)

  private partial def parseDocument (parser : Parser) (inside : Bool) : Except DocumentFailure (PositionedDocument × Parser) := do
    let rec loop (state : Parser) (nodes : List PositionedNode) : Except DocumentFailure (PositionedDocument × Parser) := do
      let state ← skipLineSpace state
      match state.remaining with
      | [] => if inside then .error (failure state .unexpectedEof) else .ok (.make nodes.reverse, state)
      | '}' :: _ =>
        if inside then
          let afterClose ← state.consume '}'
          .ok (.make nodes.reverse, afterClose)
        else .error (failure state (.unexpectedChar '}'))
      | '/' :: '-' :: _ =>
        let afterSlash ← state.consume '/'
        let afterDash ← afterSlash.consume '-'
        let discardedStart ← skipLineSpace afterDash
        match discardedStart.peek with
        | none | some '}' => .error (failure discardedStart .invalidSlashdash)
        | _ =>
          let (_, afterDiscarded) ← parseNode discardedStart
          let afterTerminator ← consumeNodeTerminator afterDiscarded inside
          loop afterTerminator nodes
      | _ =>
        let (node, afterNode) ← parseNode state
        let afterTerminator ← consumeNodeTerminator afterNode inside
        loop afterTerminator (node :: nodes)
    loop parser []

  private partial def consumeNodeTerminator (parser : Parser) (inside : Bool) : Except DocumentFailure Parser := do
    let (_, state) ← skipNodeSpace parser
    match state.remaining with
    | [] => .ok state
    | ';' :: _ => state.consume ';'
    | '/' :: '/' :: _ =>
      let afterComment := skipLineComment state
      match afterComment.advance with
      | some (_, next) => .ok next
      | none => .ok afterComment
    | '}' :: _ => if inside then .ok state else .error (failure state (.unexpectedChar '}'))
    | _ =>
      match state.peek with
      | some character =>
        if isNewline character then
          match state.advance with
          | some (_, next) => .ok next
          | none => .ok state
        else .error (failure state (.unexpectedChar character))
      | none => .ok state
end

private def validUtf8Width (bytes : List UInt8) : Option Nat :=
  match bytes with
  | first :: second :: third :: fourth :: _ =>
    if first ≤ 127 then some 1
    else if first >= 194 && first ≤ 223 && second >= 128 && second ≤ 191 then some 2
    else if first == 224 && second >= 160 && second ≤ 191 && third >= 128 && third ≤ 191 then some 3
    else if first >= 225 && first ≤ 236 && second >= 128 && second ≤ 191 && third >= 128 && third ≤ 191 then some 3
    else if first == 237 && second >= 128 && second ≤ 159 && third >= 128 && third ≤ 191 then some 3
    else if first >= 238 && first ≤ 239 && second >= 128 && second ≤ 191 && third >= 128 && third ≤ 191 then some 3
    else if first >= 240 && first ≤ 243 && second >= 128 && second ≤ 191 && third >= 128 && third ≤ 191 && fourth >= 128 && fourth ≤ 191 then some 4
    else if first == 244 && second >= 128 && second ≤ 143 && third >= 128 && third ≤ 191 && fourth >= 128 && fourth ≤ 191 then some 4
    else none
  | first :: second :: third :: _ =>
    if first ≤ 127 then some 1
    else if first >= 194 && first ≤ 223 && second >= 128 && second ≤ 191 then some 2
    else if first == 224 && second >= 160 && second ≤ 191 && third >= 128 && third ≤ 191 then some 3
    else if first >= 225 && first ≤ 236 && second >= 128 && second ≤ 191 && third >= 128 && third ≤ 191 then some 3
    else if first == 237 && second >= 128 && second ≤ 159 && third >= 128 && third ≤ 191 then some 3
    else if first >= 238 && first ≤ 239 && second >= 128 && second ≤ 191 && third >= 128 && third ≤ 191 then some 3
    else none
  | first :: second :: _ =>
    if first ≤ 127 then some 1
    else if first >= 194 && first ≤ 223 && second >= 128 && second ≤ 191 then some 2
    else none
  | first :: [] => if first ≤ 127 then some 1 else none
  | [] => none

private def decodeUtf8 (bytes : ByteArray) : Except DocumentFailure ValidatedUtf8Text :=
  let input := bytes.toList
  let rec loop (remaining : List UInt8) (offset fuel : Nat) : Except DocumentFailure Unit :=
    match fuel with
    | 0 => .error (.invalidUtf8 offset)
    | fuel + 1 =>
      match remaining with
      | [] => .ok ()
      | _ =>
        match validUtf8Width remaining with
        | none => .error (.invalidUtf8 offset)
        | some width => loop (remaining.drop width) (offset + width) fuel
  match loop input 0 (input.length + 1), String.fromUTF8? bytes with
  | .ok (), some text => .ok { input := bytes, text := text }
  | .error error, _ => .error error
  | .ok (), none => .error (.invalidUtf8 0)

private def skipBom (parser : Parser) : Parser :=
  match parser.remaining with
  | '\ufeff' :: rest =>
    { remaining := rest, position := { line := parser.position.line, column := 1, byteOffset := 3 } }
  | _ => parser

private def skipVersionMarker (parser : Parser) : Except DocumentFailure Parser := do
  match parser.remaining with
  | '/' :: '-' :: _ =>
    let afterSlash ← parser.consume '/'
    let afterDash ← afterSlash.consume '-'
    let afterSpace := skipHorizontal afterDash
    let afterMarker? := afterSpace.consumeToken "kdl-version"
    if afterMarker?.isNone then .ok parser else
    let afterMarker := afterMarker?.getD afterSpace
    let (hadSpace, versionStart) ← skipNodeSpace afterMarker
    if !hadSpace then .ok parser else
    match versionStart.remaining with
    | '2' :: rest =>
      let afterVersion := { remaining := rest, position := advancePosition versionStart.position '2' }
      let afterWhitespace := skipHorizontal afterVersion
      match afterWhitespace.peek with
      | none => .ok afterWhitespace
      | some character =>
        if isNewline character then .ok ((afterWhitespace.advance.getD (character, afterWhitespace)).2)
        else .error (failure afterWhitespace (.unexpectedChar character))
    | character :: _ => .error (failure versionStart (.unexpectedChar character))
    | [] => .error (failure versionStart .unexpectedEof)
  | _ => .ok parser

private def parseV2 (value : ValidatedUtf8Text) : Except DocumentFailure ParseResult := do
  let state : Utf8ParseState := { input := value.input, position := initialPosition, text := value }
  let parser := skipBom { remaining := value.text.toList, position := state.position }
  let parser ← skipVersionMarker parser
  let (positioned, after) ← parseDocument parser false
  let after ← skipLineSpace after
  match after.peek with
  | none => .ok { positioned := positioned, plain := positioned.toPlain }
  | some character => .error (failure after (.unexpectedChar character))

def parse (bytes : ByteArray) : Except DocumentFailure ParseResult := do
  let text ← decodeUtf8 bytes
  parseV2 text

def documentNodes : Document → List Node
  | .make nodes => nodes

def firstNode (document : Document) : Option Node := (documentNodes document).head?

def nodeName : Node → String
  | .make _ name _ _ => name

def nodeTypeAnnotation : Node → Option String
  | .make typeAnnotation _ _ _ => typeAnnotation

def nodeEntries : Node → List Entry
  | .make _ _ entries _ => entries

def nodeChildren : Node → Option Document
  | .make _ _ _ children => children

def entryValue : Entry → Value
  | .argument argument => argument.value
  | .property property => property.value

def entryTypeAnnotation : Entry → Option String
  | .argument argument => argument.typeAnnotation
  | .property property => property.typeAnnotation

def propertyValue? (node : Node) (name : String) : Option Value :=
  (nodeEntries node).findSome? fun
    | .property property => if property.name == name then some property.value else none
    | .argument _ => none

def firstArgument? (node : Node) : Option Value :=
  (nodeEntries node).findSome? fun
    | .argument argument => some argument.value
    | .property _ => none

def Value.asString? : Value → Option String
  | .string value => some value
  | _ => none

def Value.asBool? : Value → Option Bool
  | .boolean value => some value
  | _ => none

def Value.asInt? : Value → Option Int
  | .number value => value.asInt
  | _ => none

def Value.asFloat? : Value → Option Float
  | .number value => value.asFloat
  | _ => none

def Value.rawNumber? : Value → Option String
  | .number value => some value.raw
  | _ => none

def findChild? (node : Node) (name : String) : Option Node :=
  (nodeChildren node).bind fun document =>
    (documentNodes document).find? fun child => nodeName child == name

def findChildren (node : Node) (name : String) : List Node :=
  match nodeChildren node with
  | none => []
  | some document => (documentNodes document).filter fun child => nodeName child == name

inductive EncodingFailure where
  | invalidString (value : String)
  | invalidNumber (raw : String)
  deriving Repr, BEq, DecidableEq

private def validBareIdentifier (value : String) : Bool :=
  if value.isEmpty || reservedBareKeyword value then false
  else
    let characters := value.toList
    let startsLikeNumber :=
      match characters with
      | first :: second :: third :: _ =>
        if first == '+' || first == '-' then
          isDecimalDigit second || (second == '.' && isDecimalDigit third)
        else if first == '.' then isDecimalDigit second
        else isDecimalDigit first
      | first :: second :: _ =>
        if first == '+' || first == '-' then isDecimalDigit second
        else if first == '.' then isDecimalDigit second
        else isDecimalDigit first
      | [first] => isDecimalDigit first
      | [] => false
    !startsLikeNumber && characters.all isIdentifierCharacter

private def escapeStringCharacter (character : Char) : Except EncodingFailure String :=
  match character with
  | '"' => .ok "\\\""
  | '\\' => .ok "\\\\"
  | '\n' => .ok "\\n"
  | '\r' => .ok "\\r"
  | '\t' => .ok "\\t"
  | '\x08' => .ok "\\b"
  | '\x0c' => .ok "\\f"
  | character =>
    if isDisallowed character || isNewline character then .error (.invalidString (String.singleton character))
    else .ok (String.singleton character)

private def encodeQuotedString (value : String) : Except EncodingFailure String := do
  let encoded ← value.toList.mapM escapeStringCharacter
  .ok ("\"" ++ String.join encoded ++ "\"")

private def encodeIdentifier (value : String) : Except EncodingFailure String :=
  if validBareIdentifier value then .ok value else encodeQuotedString value

private def encodeNumber (number : Number) : Except EncodingFailure String :=
  .ok number.raw

private def encodeTypeAnnotation : Option String → Except EncodingFailure String
  | none => .ok ""
  | some value => do
    let encoded ← encodeIdentifier value
    .ok ("(" ++ encoded ++ ")")

private def encodeValue : Value → Except EncodingFailure String
  | .string value => encodeQuotedString value
  | .number value => encodeNumber value
  | .boolean true => .ok "#true"
  | .boolean false => .ok "#false"
  | .null => .ok "#null"

private def encodeEntry : Entry → Except EncodingFailure String
  | .argument argument => do
    let annotation ← encodeTypeAnnotation argument.typeAnnotation
    let value ← encodeValue argument.value
    .ok (annotation ++ value)
  | .property property => do
    let name ← encodeIdentifier property.name
    let annotation ← encodeTypeAnnotation property.typeAnnotation
    let value ← encodeValue property.value
    .ok (name ++ "=" ++ annotation ++ value)

private def indent (depth : Nat) : String := String.join (List.replicate depth "    ")

mutual
  private partial def encodeNodeAt (depth : Nat) : Node → Except EncodingFailure String
    | .make typeAnnotation name entries children => do
      let annotation ← encodeTypeAnnotation typeAnnotation
      let name ← encodeIdentifier name
      let entries ← entries.mapM fun entry => do
        let encoded ← encodeEntry entry
        .ok (" " ++ encoded)
      match children with
      | none => .ok (indent depth ++ annotation ++ name ++ String.join entries ++ "\n")
      | some children => do
        let encodedChildren ← encodeDocumentAt (depth + 1) children
        .ok (indent depth ++ annotation ++ name ++ String.join entries ++ " {\n" ++
          encodedChildren ++ indent depth ++ "}\n")

  private partial def encodeDocumentAt (depth : Nat) : Document → Except EncodingFailure String
    | .make nodes => do
      let encoded ← nodes.mapM (encodeNodeAt depth)
      .ok (String.join encoded)
end

def encode (document : Document) : Except EncodingFailure String := encodeDocumentAt 0 document

private def propertyName : Entry → Option String
  | .property property => some property.name
  | .argument _ => none

private def normalizeEntries (entries : List Entry) : List Entry :=
  let arguments := entries.filter fun entry => (propertyName entry).isNone
  let properties := entries.filter fun entry => (propertyName entry).isSome
  let deduplicated := properties.foldl (fun kept entry =>
    match propertyName entry with
    | none => kept
    | some name => (kept.filter fun candidate => propertyName candidate != some name) ++ [entry]) []
  arguments ++ deduplicated.mergeSort (fun left right =>
    match propertyName left, propertyName right with
    | some left, some right => decide (left ≤ right)
    | _, _ => true)

private def radixDigitValue (character : Char) : Option Nat :=
  hexValue character

private def radixToNat (digits : String) (base : Nat) : Option Nat :=
  (cleanUnderscores digits).toList.foldl (fun acc character => do
    let value ← acc
    let digit ← radixDigitValue character
    if digit < base then some (value * base + digit) else none) (some 0)

private def stripLeadingZeros (value : String) : String :=
  let stripped := value.toList.dropWhile fun character => character == '0'
  if stripped.isEmpty then "0" else String.ofList stripped

private def normalizeDecimalRaw (raw : String) : String :=
  let clean := cleanUnderscores raw
  let (sign, unsigned) :=
    match clean.toList with
    | '-' :: rest => ("-", String.ofList rest)
    | '+' :: rest => ("", String.ofList rest)
    | _ => ("", clean)
  let exponentParts := unsigned.splitOn "e"
  let exponentParts := if exponentParts.length == 1 then unsigned.splitOn "E" else exponentParts
  let mantissa := exponentParts.head?.getD unsigned
  let exponent := exponentParts.tail.head?
  let mantissaParts := mantissa.splitOn "."
  let integer := stripLeadingZeros (mantissaParts.head?.getD mantissa)
  let normalizedMantissa :=
    match mantissaParts.tail.head? with
    | none => integer
    | some fraction => integer ++ "." ++ fraction
  let normalizedSign := if normalizedMantissa == "0" then "" else sign
  match exponent with
  | none => normalizedSign ++ normalizedMantissa
  | some exponent =>
    let exponent :=
      match exponent.toList with
      | '+' :: _ | '-' :: _ => exponent
      | _ => "+" ++ exponent
    normalizedSign ++ normalizedMantissa ++ "E" ++ exponent

private def normalizeNumberRaw (raw : String) : String :=
  if raw.startsWith "#" then raw else
  let (sign, unsigned) :=
    match raw.toList with
    | '-' :: rest => ("-", String.ofList rest)
    | '+' :: rest => ("", String.ofList rest)
    | _ => ("", raw)
  let radix? :=
    if unsigned.startsWith "0x" || unsigned.startsWith "0X" then some (16, (unsigned.drop 2).toString)
    else if unsigned.startsWith "0o" || unsigned.startsWith "0O" then some (8, (unsigned.drop 2).toString)
    else if unsigned.startsWith "0b" || unsigned.startsWith "0B" then some (2, (unsigned.drop 2).toString)
    else none
  match radix? with
  | some (base, digits) =>
    match radixToNat digits base with
    | some 0 => "0"
    | some value => sign ++ toString value
    | none => normalizeDecimalRaw raw
  | none => normalizeDecimalRaw raw

private def encodeNormalizedValue : Value → Except EncodingFailure String
  | .string value => encodeIdentifier value
  | .number value => .ok (normalizeNumberRaw value.raw)
  | .boolean true => .ok "#true"
  | .boolean false => .ok "#false"
  | .null => .ok "#null"

private def encodeNormalizedEntry : Entry → Except EncodingFailure String
  | .argument argument => do
    let annotation ← encodeTypeAnnotation argument.typeAnnotation
    let value ← encodeNormalizedValue argument.value
    .ok (annotation ++ value)
  | .property property => do
    let name ← encodeIdentifier property.name
    let annotation ← encodeTypeAnnotation property.typeAnnotation
    let value ← encodeNormalizedValue property.value
    .ok (name ++ "=" ++ annotation ++ value)

mutual
  private partial def normalizeNode : Node → Node
    | .make typeAnnotation name entries children =>
      .make typeAnnotation name (normalizeEntries entries) (children.map normalizeDocument)

  private partial def normalizeDocument : Document → Document
    | .make nodes => .make (nodes.map normalizeNode)
end

def normalize (document : Document) : Except EncodingFailure String :=
  let normalized := normalizeDocument document
  let rec encodeNode (depth : Nat) : Node → Except EncodingFailure String
    | .make typeAnnotation name entries children => do
      let annotation ← encodeTypeAnnotation typeAnnotation
      let name ← encodeIdentifier name
      let entries ← entries.mapM fun entry => do
        let encoded ← encodeNormalizedEntry entry
        .ok (" " ++ encoded)
      match children with
      | some (.make childNodes) =>
        if childNodes.isEmpty then .ok (indent depth ++ annotation ++ name ++ String.join entries ++ "\n")
        else do
          let children ← childNodes.mapM (encodeNode (depth + 1))
          .ok (indent depth ++ annotation ++ name ++ String.join entries ++ " {\n" ++
            String.join children ++ indent depth ++ "}\n")
      | _ => .ok (indent depth ++ annotation ++ name ++ String.join entries ++ "\n")
  match normalized with
  | .make [] => .ok "\n"
  | .make nodes => do
    let encoded ← nodes.mapM (encodeNode 0)
    .ok (String.join encoded)

inductive GenericValue where
  | null
  | boolean (value : Bool)
  | integer (value : Int)
  | float (value : Float)
  | string (value : String)
  | array (values : List GenericValue)
  | object (fields : List (String × GenericValue))
  deriving Repr, BEq

instance : Inhabited GenericValue := ⟨.null⟩

inductive ValueErrorKind where
  | topLevelMustBeObject
  | nestedCollectionInArray
  | emptyArrayCannotBeConverted
  | propertyCannotBeConverted
  | mixedArgumentsAndChildren
  | unsupportedTypeAnnotation (value : String)
  | numberCannotBeConverted (raw : String)
  deriving Repr, BEq, DecidableEq

structure ValueFailure where
  kind : ValueErrorKind
  deriving Repr, BEq, DecidableEq

instance : Inhabited ValueFailure := ⟨{ kind := .topLevelMustBeObject }⟩

private def valueFailure {α : Type} (kind : ValueErrorKind) : Except ValueFailure α := .error { kind := kind }

private def genericNumber (raw : String) : Except ValueFailure Value :=
  match numberFromRaw raw with
  | .ok number => .ok (.number number)
  | .error _ => valueFailure (.numberCannotBeConverted raw)

private def genericScalarToValue : GenericValue → Except ValueFailure Value
  | .null => .ok .null
  | .boolean value => .ok (.boolean value)
  | .integer value => genericNumber (toString value)
  | .float value => genericNumber value.toString
  | .string value => .ok (.string value)
  | .array _ | .object _ => valueFailure .nestedCollectionInArray

private partial def genericValueToNode (name : String) : GenericValue → Except ValueFailure Node
  | .null => .ok (.make none name [] none)
  | .boolean value => .ok (.make none name [.argument { typeAnnotation := none, value := .boolean value }] none)
  | .integer value => do
    let number ← genericNumber (toString value)
    .ok (.make none name [.argument { typeAnnotation := none, value := number }] none)
  | .float value => do
    let number ← genericNumber value.toString
    .ok (.make none name [.argument { typeAnnotation := some "f64", value := number }] none)
  | .string value => .ok (.make none name [.argument { typeAnnotation := none, value := .string value }] none)
  | .array [] => valueFailure .emptyArrayCannotBeConverted
  | .array values => do
    let values ← values.mapM genericScalarToValue
    .ok (.make none name (values.map fun value => .argument { typeAnnotation := none, value := value }) none)
  | .object fields => do
    let nodes ← fields.mapM fun (name, value) => genericValueToNode name value
    .ok (.make none name [] (some (.make nodes)))

def valueToDocument : GenericValue → Except ValueFailure Document
  | .object fields => do
    let nodes ← fields.mapM fun (name, value) => genericValueToNode name value
    .ok (.make nodes)
  | _ => valueFailure .topLevelMustBeObject

private def valueToGeneric (annotation : Option String) : Value → Except ValueFailure GenericValue
  | .null =>
    match annotation with
    | none => .ok .null
    | some value => valueFailure (.unsupportedTypeAnnotation value)
  | .boolean value =>
    match annotation with
    | none => .ok (.boolean value)
    | some annotation => valueFailure (.unsupportedTypeAnnotation annotation)
  | .string value =>
    match annotation with
    | none => .ok (.string value)
    | some annotation => valueFailure (.unsupportedTypeAnnotation annotation)
  | .number value =>
    match annotation, value.asInt, value.asFloat with
    | none, some integer, _ => .ok (.integer integer)
    | some "f64", _, some float => .ok (.float float)
    | none, none, some float => .ok (.float float)
    | some annotation, _, _ => valueFailure (.unsupportedTypeAnnotation annotation)
    | none, none, none => valueFailure (.numberCannotBeConverted value.raw)

private partial def nodeToGeneric : Node → Except ValueFailure GenericValue
  | .make (some annotation) _ _ _ => valueFailure (.unsupportedTypeAnnotation annotation)
  | .make none _ entries children =>
    if entries.any fun entry => match entry with | .property _ => true | _ => false then
      valueFailure .propertyCannotBeConverted
    else
      let arguments := entries.filterMap fun
        | .argument argument => some argument
        | .property _ => none
      match children, arguments with
      | some _, _ :: _ => valueFailure .mixedArgumentsAndChildren
      | some (.make nodes), [] => do
        let fields ← nodes.mapM fun node => do
          let value ← nodeToGeneric node
          .ok (nodeName node, value)
        .ok (.object fields)
      | none, [] => .ok .null
      | none, [argument] => valueToGeneric argument.typeAnnotation argument.value
      | none, arguments => do
        let values ← arguments.mapM fun argument => valueToGeneric argument.typeAnnotation argument.value
        .ok (.array values)

def documentToValue : Document → Except ValueFailure GenericValue
  | .make nodes => do
    let fields ← nodes.mapM fun node => do
      let value ← nodeToGeneric node
      .ok (nodeName node, value)
    .ok (.object fields)

def makeNumber (raw : String) : Except BuilderFailure Number := numberFromRaw raw

def emptyDocument : Document := .make []

def makeNode (name : String) : Node := .make none name [] none

def Node.withTypeAnnotation : Node → String → Node
  | .make _ name entries children, annotation => .make (some annotation) name entries children

def Node.addArgument : Node → Value → Node
  | .make annotation name entries children, value =>
    .make annotation name (entries ++ [.argument { typeAnnotation := none, value := value }]) children

def Node.addTypedArgument : Node → String → Value → Node
  | .make annotation name entries children, typeAnnotation, value =>
    .make annotation name (entries ++ [.argument { typeAnnotation := some typeAnnotation, value := value }]) children

def Node.addProperty : Node → String → Value → Node
  | .make annotation name entries children, key, value =>
    .make annotation name (entries ++ [.property { typeAnnotation := none, name := key, value := value }]) children

def Node.addTypedProperty : Node → String → String → Value → Node
  | .make annotation name entries children, key, typeAnnotation, value =>
    .make annotation name (entries ++ [.property { typeAnnotation := some typeAnnotation, name := key, value := value }]) children

def Node.addChild : Node → Node → Node
  | .make annotation name entries none, child =>
    .make annotation name entries (some (.make [child]))
  | .make annotation name entries (some (.make children)), child =>
    .make annotation name entries (some (.make (children ++ [child])))

def Document.addNode : Document → Node → Document
  | .make nodes, node => .make (nodes ++ [node])

end NecoLean.Kdl
