import NecoLean.Tui.Types
import NecoLean.Tui.Layout
import NecoLean.Tui.Surface
import NecoLean.Tui.Tree
import NecoLean.Tui.Overlay
import NecoLean.Tui.Viewport

set_option autoImplicit false

namespace NecoLean.Tui

structure Model where
  tree : Tree
  overlays : OverlayState := {}
  viewport : ViewportState := { top := 0, anchor := "", selected := "", size := 0 }
  detailLines : List LogicalLine := []
  width : Int := 80
  height : Int := 24
  error : String := ""
  quit : Bool := false
  placement : DetailPlacement := .right
  detailColumns : Int := 32
  detailRows : Int := 8
  deriving Repr, BEq

abbrev helpOverlayId : String := "help"

private def spaces (count : Int) : String :=
  String.ofList (List.replicate (max 0 count).toNat ' ')

def detailLinesFor (tree : Tree) : List LogicalLine :=
  match (flatten tree).find? (fun row => row.id == tree.selected) with
  | some row =>
    [ { linePrefix := { first := "selected: " }, text := row.label }
    , { linePrefix := { first := "id: " }, text := row.id }
    ]
  | none => [{ linePrefix := { first := "" }, text := "no selection" }]

def helpLines : List LogicalLine :=
  [ { linePrefix := { first := "escape " }, text := "close help" }
  , { linePrefix := { first := "↑/↓ " }, text := "select" }
  , { linePrefix := { first := "enter " }, text := "expand or collapse" }
  , { linePrefix := { first := "t " }, text := "move detail" }
  , { linePrefix := { first := "+/- " }, text := "resize detail" }
  , { linePrefix := { first := "mouse " }, text := "select" }
  , { linePrefix := { first := "wheel " }, text := "scroll" }
  , { linePrefix := { first := "q " }, text := "quit" }
  , { linePrefix := { first := "ctrl-c " }, text := "interrupt and quit" }
  ]

def defaultOverlayState : OverlayState :=
  { entries := [{ id := helpOverlayId, area := rect 4 3 48 12, capture := true }] }

def initializeModel (tree : Tree) (error : String := "") : Except TuiFailure Model := do
  validateTree tree |>.mapError TuiFailure.tree
  let viewport : ViewportState := { top := 0, anchor := tree.selected, selected := tree.selected, size := 0 }
  return { tree, overlays := defaultOverlayState, viewport, detailLines := detailLinesFor tree, error }

def screenFor (model : Model) : Rect := rect 0 0 model.width model.height

def areasFor (model : Model) : FrameAreas :=
  frameAreas (screenFor model) model.placement model.detailColumns model.detailRows

private def viewportItemsFor (model : Model) : List ViewportItem :=
  let width := (areasFor model).main.size.width
  (flatten model.tree).map (fun row =>
    { id := row.id, extent := (layoutLogicalLine width (treeLogicalLine row)).length })

def synchronizedViewport (model : Model) : Model :=
  let items := viewportItemsFor model
  let viewport := resize model.viewport (areasFor model).main.size.height items
  let viewport := refresh viewport items
  { model with viewport }

private def synchronizeSelection (model : Model) : Model :=
  let model := synchronizedViewport model
  match select model.viewport model.tree.selected (viewportItemsFor model) with
  | .ok viewport => { model with viewport }
  | .error _ => model

def selectTree (model : Model) (selected : String) : Except TuiFailure Model := do
  let tree ← (selectById model.tree selected).mapError TuiFailure.tree
  let selectedModel := { model with tree, detailLines := detailLinesFor tree }
  let viewport ← (select model.viewport selected (viewportItemsFor selectedModel)).mapError TuiFailure.viewport
  return synchronizedViewport { selectedModel with viewport }

def resizeModel (model : Model) (size : TerminalSize) : Except TuiFailure Model :=
  if size.width < 0 || size.height < 0 then
    .error (.geometry (.invalidSize size.width size.height))
  else
    .ok (synchronizeSelection { model with width := size.width, height := size.height })

private def applyKeyAction (model : Model) (action : KeyAction) : Except TuiFailure Model :=
  match action with
  | .selectPrevious =>
    let tree := selectPrevious model.tree
    selectTree { model with tree } tree.selected
  | .selectNext =>
    let tree := selectNext model.tree
    selectTree { model with tree } tree.selected
  | .toggleExpansion =>
    let tree := toggleExpanded model.tree
    return synchronizeSelection { model with tree, detailLines := detailLinesFor tree }
  | .togglePlacement => return synchronizeSelection { model with placement := match model.placement with | .right => .bottom | .bottom => .right }
  | .growDetail =>
    match model.placement with
    | .right => return synchronizeSelection { model with detailColumns := model.detailColumns + 2 }
    | .bottom => return synchronizeSelection { model with detailRows := model.detailRows + 1 }
  | .shrinkDetail =>
    match model.placement with
    | .right => return synchronizeSelection { model with detailColumns := max 0 (model.detailColumns - 2) }
    | .bottom => return synchronizeSelection { model with detailRows := max 0 (model.detailRows - 1) }
  | .showHelp => do
    let overlays ← (setVisible model.overlays helpOverlayId true).mapError TuiFailure.overlay
    let overlays ← (focus overlays helpOverlayId).mapError TuiFailure.overlay
    return { model with overlays }
  | .closeOverlay => do
    let overlays ← (setVisible model.overlays helpOverlayId false).mapError TuiFailure.overlay
    return { model with overlays := unfocus overlays }
  | .quit => return { model with quit := true }

private def keyAction? (model : Model) (key : String) : Option KeyAction :=
  if key == "ctrl-c" then some .quit
  else if model.overlays.focus == some helpOverlayId then
    if key == "escape" then some .closeOverlay else none
  else
    match key with
    | "up" => some .selectPrevious
    | "down" => some .selectNext
    | "enter" => some .toggleExpansion
    | "t" => some .togglePlacement
    | "+" => some .growDetail
    | "-" => some .shrinkDetail
    | "?" => some .showHelp
    | "q" => some .quit
    | _ => none

def update (event : InputEvent) (model : Model) : Except TuiFailure Model :=
  match event with
  | .keyPress key =>
    match keyAction? model key with
    | some action => applyKeyAction model action
    | none => .ok model
  | .resize size => resizeModel model size
  | .mouseScroll delta =>
    let viewport := scroll model.viewport delta (viewportItemsFor model)
    .ok { model with viewport }
  | .mousePress x y =>
    let main := (areasFor model).main
    if contains main { x, y } then
      let rows := flatten model.tree
      let drawingLines := treeDrawingLines main.size.width (rows.drop model.viewport.top.toNat)
      let index := y - main.position.y
      match drawingLines[index.toNat]? with
      | some line => selectTree model line.id
      | none => .ok model
    else .ok model
  | .tick => .ok model

def helpOverlayArea (model : Model) : Rect :=
  match model.overlays.entries.find? (fun entry => entry.id == helpOverlayId) with
  | some entry => resolvePlacement entry (screenFor model)
  | none => rect 0 0 0 0

end NecoLean.Tui
