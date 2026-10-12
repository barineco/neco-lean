set_option autoImplicit false

namespace NecoLean.Diagnostic

inductive Failure where
  | invalidSpan (startByte : Nat) (endByte : Nat)
  deriving Repr, BEq, DecidableEq

inductive Span where
  | private make (startByte : Nat) (endByte : Nat)
  deriving Repr, BEq, DecidableEq

protected def Span.startByte (span : Span) : Nat :=
  match span with
  | .make startByte _ => startByte

protected def Span.endByte (span : Span) : Nat :=
  match span with
  | .make _ endByte => endByte

protected def Span.zero : Span := .make 0 0

protected def Span.create (startByte endByte : Nat) : Except Failure Span :=
  if startByte ≤ endByte then
    .ok (.make startByte endByte)
  else
    .error (.invalidSpan startByte endByte)

inductive Severity where
  | error
  | warning
  | information
  deriving Repr, BEq, DecidableEq

structure Message where
  path : String
  span : Span
  severity : Severity
  text : String
  deriving Repr, BEq

end NecoLean.Diagnostic
