import NecoLean.System

namespace NecoLean

structure Printer where
  bytes : ByteArray
  deriving BEq

instance : Repr Printer where
  reprPrec printer _ :=
    Std.Format.text s!"NecoLean.Printer.mk (size := {printer.bytes.size})"

namespace Printer

def empty : Printer :=
  { bytes := ByteArray.empty }

def append (printer : Printer) (bytes : ByteArray) : Printer :=
  { bytes := printer.bytes ++ bytes }

def finish (printer : Printer) : ByteArray :=
  printer.bytes

def writeTo (path : NecoLean.System.FilePath) (printer : Printer) : IO (Except NecoLean.System.Failure ByteArray) := do
  match ← NecoLean.System.writeBytes path printer.finish with
  | .ok () => return .ok printer.finish
  | .error failure => return .error failure

end Printer
end NecoLean
