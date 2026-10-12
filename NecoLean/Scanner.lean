import NecoLean.System

namespace NecoLean

structure Scanner where
  bytes : ByteArray
  position : Nat
  deriving BEq

instance : Repr Scanner where
  reprPrec scanner _ :=
    Std.Format.text s!"NecoLean.Scanner.mk (size := {scanner.bytes.size}, position := {scanner.position})"

namespace Scanner

inductive Failure where
  | invalidInteger
  | invalidUtf8
  | unexpectedEnd
  deriving BEq

private def isDelimiter (byte : UInt8) : Bool :=
  byte == 0x09 || byte == 0x0A || byte == 0x0B || byte == 0x0C || byte == 0x0D || byte == 0x20

private def skipDelimiters (bytes : ByteArray) (position : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => position
  | fuel + 1 =>
    if position < bytes.size && isDelimiter (bytes.get! position) then
      skipDelimiters bytes (position + 1) fuel
    else
      position

private def scanTokenEnd (bytes : ByteArray) (position : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => position
  | fuel + 1 =>
    if position < bytes.size && !isDelimiter (bytes.get! position) then
      scanTokenEnd bytes (position + 1) fuel
    else
      position

private def isAsciiDigit (byte : UInt8) : Bool :=
  0x30 <= byte && byte <= 0x39

private def hasAsciiDigits (bytes : ByteArray) (start finish : Nat) : Bool :=
  start < finish && (bytes.extract start finish).toList.all isAsciiDigit

def create (bytes : ByteArray) : Scanner :=
  { bytes, position := 0 }

def scanToken (scanner : Scanner) : Except Failure (String × Scanner) :=
  let start := skipDelimiters scanner.bytes scanner.position (scanner.bytes.size - scanner.position)
  let finish := scanTokenEnd scanner.bytes start (scanner.bytes.size - start)
  if start == finish then
    .error .unexpectedEnd
  else
    match String.fromUTF8? (scanner.bytes.extract start finish) with
    | some token => .ok (token, { scanner with position := finish })
    | none => .error .invalidUtf8

def scanInt (scanner : Scanner) : Except Failure (Int × Scanner) :=
  match scanToken scanner with
  | .error failure => .error failure
  | .ok (token, successor) =>
    let start := skipDelimiters scanner.bytes scanner.position (scanner.bytes.size - scanner.position)
    if hasAsciiDigits scanner.bytes start successor.position then
      match token.toInt? with
      | some value => .ok (value, successor)
      | none => .error .invalidInteger
    else
      .error .invalidInteger

def scanSignedInt (scanner : Scanner) : Except Failure (Int × Scanner) :=
  match scanToken scanner with
  | .error failure => .error failure
  | .ok (token, successor) =>
    let start := skipDelimiters scanner.bytes scanner.position (scanner.bytes.size - scanner.position)
    let tokenBytes := scanner.bytes.extract start successor.position
    let digitStart := if tokenBytes.get! 0 == 0x2D then start + 1 else start
    if hasAsciiDigits scanner.bytes digitStart successor.position then
      match token.toInt? with
      | some value => .ok (value, successor)
      | none => .error .invalidInteger
    else
      .error .invalidInteger

def scanLine (scanner : Scanner) : Except Failure (String × Scanner) :=
  let rec findTerminator (position fuel : Nat) : Nat :=
    match fuel with
    | 0 => scanner.bytes.size
    | fuel + 1 =>
      if position < scanner.bytes.size &&
          (scanner.bytes.get! position == 0x0A || scanner.bytes.get! position == 0x0D) then
        position
      else if position < scanner.bytes.size then
        findTerminator (position + 1) fuel
      else
        scanner.bytes.size
  let finish := findTerminator scanner.position (scanner.bytes.size - scanner.position)
  if finish == scanner.bytes.size then
    .error .unexpectedEnd
  else
    let next := if scanner.bytes.get! finish == 0x0D && finish + 1 < scanner.bytes.size && scanner.bytes.get! (finish + 1) == 0x0A then finish + 2 else finish + 1
    match String.fromUTF8? (scanner.bytes.extract scanner.position finish) with
    | some line => .ok (line, { scanner with position := next })
    | none => .error .invalidUtf8

end Scanner
end NecoLean
