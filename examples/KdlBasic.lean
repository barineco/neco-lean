import NecoLean.Kdl
import NecoLean.System

set_option autoImplicit false

private def printNodeNames (document : NecoLean.Kdl.Document) : IO Unit := do
  for node in NecoLean.Kdl.documentNodes document do
    IO.println (NecoLean.Kdl.nodeName node)

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
    match ← NecoLean.System.readBytes path with
    | .error _ =>
      IO.eprintln s!"cannot read: {path}"
      return 1
    | .ok bytes =>
      match NecoLean.Kdl.parse bytes with
      | .error _ =>
        IO.eprintln s!"cannot parse KDL: {path}"
        return 1
      | .ok result =>
        let nodes := NecoLean.Kdl.documentNodes result.plain
        IO.println s!"nodes: {nodes.length}"
        printNodeNames result.plain
        return 0
  | _ =>
    IO.eprintln "usage: neco-lean-example-kdl <document-path>"
    return 2
