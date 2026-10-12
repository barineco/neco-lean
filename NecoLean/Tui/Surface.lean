import NecoLean.Tui.Types
import NecoLean.Tui.Layout
import NecoLean.Tui.Cell

set_option autoImplicit false

namespace NecoLean.Tui

structure Surface where
  private mk ::
  area : Rect
  cells : Array Cell
  deriving Repr, BEq, DecidableEq

structure SurfacePatch where
  position : Position
  cells : List Cell
  deriving Repr, BEq, DecidableEq

inductive RenderOp where
  | move (position : Position)
  | write (text : String)
  | clear
  deriving Repr, BEq, DecidableEq

structure Prefix where
  first : String
  continuation : String := ""
  deriving Repr, BEq, DecidableEq

structure LogicalLine where
  linePrefix : Prefix
  text : String
  deriving Repr, BEq, DecidableEq

structure DrawingLine where
  cells : List Cell
  deriving Repr, BEq, DecidableEq

def surfaceSize (value : Rect) : Nat := value.size.width.toNat * value.size.height.toNat
def emptySurface (value : Rect) : Surface := {area := value, cells := Array.replicate (surfaceSize value) emptyCell}
def indexOf (value : Rect) (position : Position) : Nat := (position.y - value.position.y).toNat * value.size.width.toNat + (position.x - value.position.x).toNat
def getCell (surface : Surface) (position : Position) : Cell := if contains surface.area position then surface.cells.getD (indexOf surface.area position) emptyCell else emptyCell
def setCell (surface : Surface) (position : Position) (cell : Cell) : Surface :=
  if contains surface.area position then
    let index := indexOf surface.area position
    if proof : index < surface.cells.size then {surface with cells := surface.cells.set index cell proof} else surface
  else surface

private def writeCells (surface : Surface) (position : Position) : List Cell → Surface
  | [] => surface
  | first :: second :: rest =>
    if cellContentWidth first == 2 && isContinuation second then
      if contains surface.area position && contains surface.area {x := position.x + 1, y := position.y} then
        writeCells (setCell (setCell surface position first) {x := position.x + 1, y := position.y} second) {x := position.x + 2, y := position.y} rest
      else surface
    else
      writeCells (setCell surface position first) {x := position.x + 1, y := position.y} (second :: rest)
  | [cell] => setCell surface position cell

def setText (surface : Surface) (position : Position) (text : String) : Surface :=
  writeCells surface position (cellsForString text)

def positions (value : Rect) : List Position :=
  (List.range value.size.height.toNat).flatMap (fun y =>
    (List.range value.size.width.toNat).map (fun x => {x := value.position.x + Int.ofNat x, y := value.position.y + Int.ofNat y}))

def clip (surface : Surface) (value : Rect) : Surface :=
  match intersection surface.area value with
  | none => emptySurface rectZero
  | some clipped =>
    (positions clipped).foldl (fun result position =>
      let cell := getCell surface position
      let preserved :=
        if isContinuation cell then
          if contains clipped {x := position.x - 1, y := position.y} then cell else emptyCell
        else if cellContentWidth cell == 2 then
          if contains clipped {x := position.x + 1, y := position.y} then cell else emptyCell
        else cell
      setCell result position preserved) (emptySurface clipped)

def diff (before after : Surface) : List SurfacePatch :=
  (positions after.area).filterMap (fun position =>
    if getCell before position == getCell after position then none else some {position, cells := [getCell after position]})

def patchToAnsi (patch : SurfacePatch) : RenderOp :=
  .write (patch.cells.foldl (fun text cell => text ++ cellSymbol cell) "")

def diffToAnsi (before after : Surface) : List RenderOp :=
  if before.area != after.area then
    .clear :: (positions after.area).flatMap (fun position => [.move position, .write (cellSymbol (getCell after position))])
  else
    (diff before after).flatMap (fun patch => [.move patch.position, patchToAnsi patch])

def renderOpsToAnsi (operations : List RenderOp) : String :=
  operations.foldl (fun output operation =>
    match operation with
    | .move position => output ++ s!"\u001b[{position.y + 1};{position.x + 1}H"
    | .write text => output ++ text
    | .clear => output ++ "\u001b[2J\u001b[H") ""

def toAnsi (surface : Surface) : String :=
  (List.range surface.area.size.height.toNat).foldl (fun output y =>
    let line := (List.range surface.area.size.width.toNat).foldl (fun text x =>
      text ++ cellSymbol (getCell surface {x := surface.area.position.x + Int.ofNat x, y := surface.area.position.y + Int.ofNat y})) ""
    output ++ line ++ if y + 1 < surface.area.size.height.toNat then "\n" else "") ""

def drawFrame (surface : Surface) (rounded : Bool := false) : Surface :=
  let value := surface.area
  if value.size.width < 2 || value.size.height < 2 then surface else
    let (topLeft, topRight, bottomLeft, bottomRight) := if rounded then ("╭", "╮", "╰", "╯") else ("┌", "┐", "└", "┘")
    let horizontal := String.ofList (List.replicate (value.size.width - 2).toNat '─')
    let top := setText surface value.position (topLeft ++ horizontal ++ topRight)
    let sides := (List.range (value.size.height - 2).toNat).foldl (fun current offset =>
      let y := value.position.y + 1 + Int.ofNat offset
      setText (setText current {x := value.position.x, y} "│") {x := right value - 1, y} "│") top
    setText sides {x := value.position.x, y := bottom value - 1} (bottomLeft ++ horizontal ++ bottomRight)

def drawDivider (surface : Surface) (value : Rect) : Surface :=
  if value.size.width == 1 then
    (List.range value.size.height.toNat).foldl (fun current offset =>
      setText current {x := value.position.x, y := value.position.y + Int.ofNat offset} "│") surface
  else if value.size.height == 1 then
    (List.range value.size.width.toNat).foldl (fun current offset =>
      setText current {x := value.position.x + Int.ofNat offset, y := value.position.y} "─") surface
  else surface

private def spaces (count : Nat) : String := String.ofList (List.replicate count ' ')

private def fitCells (width : Nat) : List Cell → List Cell × List Cell
  | [] => ([], [])
  | first :: second :: rest =>
    if cellContentWidth first == 2 && isContinuation second then
      if width < 2 then ([], first :: second :: rest)
      else
        let (fit, remaining) := fitCells (width - 2) rest
        (first :: second :: fit, remaining)
    else if width == 0 then ([], first :: second :: rest)
    else
      let (fit, remaining) := fitCells (width - 1) (second :: rest)
      (first :: fit, remaining)
  | [cell] => if width == 0 then ([], [cell]) else ([cell], [])

private def prefixText (value : Prefix) (continuation : Bool) : String :=
  if continuation then
    if value.continuation.isEmpty then spaces (cellsForString value.first).length else value.continuation
  else value.first

private def rawDrawingLines (width : Nat) : Nat → List Cell → List DrawingLine
  | 0, _ => []
  | _, [] => []
  | fuel + 1, remaining =>
    let (part, rest) := fitCells width remaining
    if part.isEmpty then [] else
      { cells := part } :: rawDrawingLines width fuel rest

private def layoutLogicalLineFrom (line : LogicalLine) (width : Nat) :
    Nat → Bool → List Cell → List DrawingLine
  | 0, _, _ => []
  | fuel + 1, continuation, remaining =>
    let prefixCells := cellsForString (prefixText line.linePrefix continuation)
    if prefixCells.length >= width then
      rawDrawingLines width (prefixCells.length + remaining.length + 1) (prefixCells ++ remaining)
    else
      let (part, rest) := fitCells (width - prefixCells.length) remaining
      let drawing := { cells := prefixCells ++ part }
      if rest.isEmpty then [drawing]
      else if part.isEmpty then
        drawing :: rawDrawingLines width (rest.length + 1) rest
      else drawing :: layoutLogicalLineFrom line width fuel true rest

def layoutLogicalLine (width : Int) (line : LogicalLine) : List DrawingLine :=
  if width <= 0 then [] else
    let textCells := cellsForString line.text
    layoutLogicalLineFrom line width.toNat (textCells.length + 1) false textCells

def writeDrawingLine (surface : Surface) (position : Position) (width : Int) (line : DrawingLine) : Surface :=
  if width <= 0 then surface else
    let (cells, _) := fitCells width.toNat line.cells
    writeCells surface position cells

end NecoLean.Tui
