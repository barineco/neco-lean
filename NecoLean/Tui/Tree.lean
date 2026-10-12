import NecoLean.Tui.Types
import NecoLean.Tui.Surface

set_option autoImplicit false

namespace NecoLean.Tui

structure TreeRow where
  id : String
  label : String
  depth : Int
  selected : Bool
  expandable : Bool
  expanded : Bool
  linePrefix : Prefix
  deriving Repr, BEq, DecidableEq

structure TreeDrawingLine where
  id : String
  line : DrawingLine
  deriving Repr, BEq, DecidableEq

structure Tree where
  nodes : List UiNode
  expanded : List String := []
  selected : String := ""
  deriving Repr, BEq

private partial def nodeIds (nodes : List UiNode) : List String :=
  nodes.flatMap fun node => node.id :: nodeIds node.children

private partial def findNode? (id : String) (nodes : List UiNode) : Option UiNode :=
  match nodes with
  | [] => none
  | node :: rest =>
    if node.id == id then some node else
      match findNode? id node.children with
      | some found => some found
      | none => findNode? id rest

def validateTree (tree : Tree) : Except TreeFailure Unit :=
  let ids := nodeIds tree.nodes
  if ids.eraseDups.length != ids.length then
    .error (.duplicateTreeId (ids.find? (fun id => ids.count id > 1) |>.getD ""))
  else if !tree.selected.isEmpty && !(ids.contains tree.selected) then
    .error (.invalidSelection tree.selected)
  else if tree.nodes.isEmpty then .error (.disconnectedTree "root")
  else .ok ()

private def indent (depth : Int) : String :=
  String.ofList (List.replicate (max 0 (depth * 2)).toNat ' ')

private partial def flattenNodes (tree : Tree) (depth : Int) : List UiNode → List TreeRow
  | [] => []
  | node :: rest =>
    let expanded := tree.expanded.contains node.id
    let marker := if node.children.isEmpty then "  " else if expanded then "- " else "+ "
    let first := indent depth ++ marker
    let row : TreeRow := {
      id := node.id
      label := node.label
      depth
      selected := node.id == tree.selected
      expandable := !node.children.isEmpty
      expanded
      linePrefix := { first, continuation := String.ofList (List.replicate ((cellsForString first).length) ' ') }
    }
    row :: (if expanded then flattenNodes tree (depth + 1) node.children else []) ++ flattenNodes tree depth rest

def flatten (tree : Tree) : List TreeRow := flattenNodes tree 0 tree.nodes

def toggleExpanded (tree : Tree) : Tree :=
  if tree.expanded.contains tree.selected then
    { tree with expanded := tree.expanded.filter (· != tree.selected) }
  else if (findNode? tree.selected tree.nodes).map (fun node => !node.children.isEmpty) |>.getD false then
    { tree with expanded := tree.selected :: tree.expanded }
  else tree

def selectPrevious (tree : Tree) : Tree :=
  let rows := flatten tree
  match rows.findIdx? (·.id == tree.selected) with
  | some 0 => tree
  | some index => { tree with selected := rows[index - 1]?.map (·.id) |>.getD tree.selected }
  | none => tree

def selectNext (tree : Tree) : Tree :=
  let rows := flatten tree
  match rows.findIdx? (·.id == tree.selected) with
  | some index => { tree with selected := rows[index + 1]?.map (·.id) |>.getD tree.selected }
  | none => tree

def selectById (tree : Tree) (id : String) : Except TreeFailure Tree :=
  if (nodeIds tree.nodes).contains id then .ok { tree with selected := id }
  else .error (.missingTreeNode id)

def treeLogicalLine (row : TreeRow) : LogicalLine :=
  { linePrefix := row.linePrefix, text := (if row.selected then "> " else "  ") ++ row.label }

def treeDrawingLines (width : Int) (rows : List TreeRow) : List TreeDrawingLine :=
  rows.flatMap (fun row =>
    (layoutLogicalLine width (treeLogicalLine row)).map (fun line => { id := row.id, line }))

end NecoLean.Tui
