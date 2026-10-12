import NecoLean.Kdl
import NecoLean.System
import NecoLean.Tui.Posix

set_option autoImplicit false

private def valueText : NecoLean.Kdl.Value → String
  | .string value => value
  | .number value => value.raw
  | .boolean true => "true"
  | .boolean false => "false"
  | .null => "null"

private def nodeLabel (node : NecoLean.Kdl.Node) : String :=
  match NecoLean.Kdl.firstArgument? node with
  | some value => NecoLean.Kdl.nodeName node ++ " " ++ valueText value
  | none => NecoLean.Kdl.nodeName node

private def nodeId (pathPrefix : String) (index : Nat) : String :=
  if pathPrefix.isEmpty then toString index else pathPrefix ++ "." ++ toString index

mutual
  private partial def nodeToUi (id : String) (node : NecoLean.Kdl.Node) : NecoLean.Tui.UiNode :=
    let children := match NecoLean.Kdl.nodeChildren node with
      | some document => documentToUi id document
      | none => []
    { id, label := nodeLabel node, children }

  private partial def nodesToUi (pathPrefix : String) : List NecoLean.Kdl.Node → Nat → List NecoLean.Tui.UiNode
    | [], _ => []
    | node :: rest, index =>
      let id := nodeId pathPrefix index
      nodeToUi id node :: nodesToUi pathPrefix rest (index + 1)

  private partial def documentToUi (pathPrefix : String) (document : NecoLean.Kdl.Document) : List NecoLean.Tui.UiNode :=
    nodesToUi pathPrefix (NecoLean.Kdl.documentNodes document) 0
end

private partial def expandedNodeIds : List NecoLean.Tui.UiNode → List String
  | [] => []
  | node :: rest =>
    let current := if node.children.isEmpty then [] else [node.id]
    current ++ expandedNodeIds node.children ++ expandedNodeIds rest

private def runDocument (document : NecoLean.Kdl.Document) : IO UInt32 := do
  let nodes := documentToUi "" document
  match nodes with
  | [] =>
    IO.eprintln "the KDL document has no nodes"
    return 1
  | first :: _ =>
    let tree : NecoLean.Tui.Tree := {
      nodes
      expanded := expandedNodeIds nodes
      selected := first.id
    }
    match NecoLean.Tui.initializeModel tree with
    | .error _ =>
      IO.eprintln "cannot construct the terminal tree"
      return 1
    | .ok model =>
      match ← NecoLean.Tui.Posix.runModel model with
      | .ok () => return 0
      | .error _ =>
        IO.eprintln "terminal interface failed"
        return 1

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
      | .ok result => runDocument result.plain
  | _ =>
    IO.eprintln "usage: neco-lean-example-kdl-tui <document-path>"
    return 2
