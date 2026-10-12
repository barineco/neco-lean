import NecoLean.Tui.Model

set_option autoImplicit false

namespace NecoLean.Tui

private def drawHorizontalDivider (surface : Surface) (screen dividerArea : Rect) (joint : Option Int) : Surface :=
  let dividedSurface := drawDivider surface dividerArea
  if dividerArea.size.height == 0 then dividedSurface else
    let left := screen.position.x
    let rightEdge := right screen - 1
    let withEnds := setText (setText dividedSurface {x := left, y := dividerArea.position.y} "├") {x := rightEdge, y := dividerArea.position.y} "┤"
    match joint with
    | some x => setText withEnds {x, y := dividerArea.position.y} "┴"
    | none => withEnds

private def drawVerticalDivider (surface : Surface) (screen dividerArea : Rect) (joinY : Int) : Surface :=
  let dividedSurface := drawDivider surface dividerArea
  if dividerArea.size.width == 0 || dividerArea.size.height == 0 then dividedSurface
  else
    let x := dividerArea.position.x
    let topY := screen.position.y
    let join := min (bottom dividerArea) joinY
    let withTop := if topY < join then setText dividedSurface {x, y := topY} "┬" else dividedSurface
    if join < bottom dividerArea then withTop else setText withTop {x, y := join} "┴"

private def renderCompositionFrame (surface : Surface) (model : Model) (screen : Rect) (areas : FrameAreas) : Surface :=
  let framed := drawFrame surface
  match model.placement with
  | .right =>
    let divided := drawVerticalDivider framed screen areas.divider areas.hintDivider.position.y
    drawHorizontalDivider divided screen areas.hintDivider (some areas.divider.position.x)
  | .bottom =>
    let divided := drawHorizontalDivider framed screen areas.divider none
    drawHorizontalDivider divided screen areas.hintDivider none

private def renderDrawingLines (surface : Surface) (area : Rect) (lines : List DrawingLine) : Surface :=
  let visible := lines.take area.size.height.toNat
  (List.range visible.length).foldl (fun result offset =>
    match visible[offset]? with
    | some line => writeDrawingLine result {x := area.position.x, y := area.position.y + Int.ofNat offset} area.size.width line
    | none => result) surface

private def renderLogicalLines (surface : Surface) (area : Rect) (lines : List LogicalLine) : Surface :=
  let drawingLines := lines.flatMap (layoutLogicalLine area.size.width)
  renderDrawingLines surface area drawingLines

def renderTree (surface : Surface) (area : Rect) (model : Model) : Surface :=
  let rows := flatten model.tree
  let drawingLines := treeDrawingLines area.size.width (rows.drop model.viewport.top.toNat)
  renderDrawingLines surface area (drawingLines.map (·.line))

def renderDetail (surface : Surface) (area : Rect) (model : Model) : Surface :=
  renderLogicalLines surface area model.detailLines

def renderHint (surface : Surface) (area : Rect) (model : Model) : Surface :=
  let line := if model.error.isEmpty then { linePrefix := { first := "? help  " }, text := "↑/↓ select  enter expand  t layout  q quit" } else { linePrefix := { first := "" }, text := model.error }
  renderLogicalLines surface area [line]

private def helpSurface (model : Model) : OverlaySurface :=
  let area := helpOverlayArea model
  let base := drawFrame (emptySurface area) true
  let inner := inset 1 area
  let surface := renderLogicalLines base inner helpLines
  { id := helpOverlayId, surface }

def renderFrame (model : Model) (screen : Rect) : Surface :=
  let model := synchronizedViewport {model with width := screen.size.width, height := screen.size.height}
  let areas := frameAreas screen model.placement model.detailColumns model.detailRows
  let base := emptySurface screen
  let framed := renderCompositionFrame base model screen areas
  let content := renderHint (renderDetail (renderTree framed areas.main model) areas.detail model) areas.hint model
  compose content model.overlays [helpSurface model]

def renderText (model : Model) (screen : Rect) : String :=
  toAnsi (renderFrame model screen)

end NecoLean.Tui
