import NecoLean.Tui.Types

set_option autoImplicit false

namespace NecoLean.Tui

structure Position where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq

structure Size where
  private mk ::
  width : Int
  height : Int
  deriving Repr, BEq, DecidableEq

structure Rect where
  private mk ::
  position : Position
  size : Size
  deriving Repr, BEq, DecidableEq

structure FrameAreas where
  main : Rect
  detail : Rect
  divider : Rect
  hintDivider : Rect
  hint : Rect
  deriving Repr, BEq, DecidableEq

structure SharedEdge where
  first : Rect
  second : Rect
  orientation : DetailPlacement
  deriving Repr, BEq, DecidableEq

structure EdgeDelta where
  amount : Int
  deriving Repr, BEq, DecidableEq

inductive Constraint where
  | length (value : Int)
  | min (value : Int)
  | max (value : Int)
  | percentage (value : Int)
  | ratio (numerator denominator : Int)
  | fill
  deriving Repr, BEq, DecidableEq

def nonNegative (value : Int) : Int := max 0 value
def rect (x y width height : Int) : Rect := { position := {x, y}, size := {width := nonNegative width, height := nonNegative height} }
def rectZero : Rect := rect 0 0 0 0
def right (value : Rect) : Int := value.position.x + value.size.width
def bottom (value : Rect) : Int := value.position.y + value.size.height
def area (value : Rect) : Int := value.size.width * value.size.height
def contains (value : Rect) (position : Position) : Bool := position.x >= value.position.x && position.x < right value && position.y >= value.position.y && position.y < bottom value
def hitTest (value : Rect) (x y : Int) : Bool := contains value {x, y}

def inset (amount : Int) (value : Rect) : Rect :=
  let n := nonNegative amount
  rect (value.position.x + n) (value.position.y + n) (value.size.width - n * 2) (value.size.height - n * 2)

def intersection (left rightArea : Rect) : Option Rect :=
  let x := max left.position.x rightArea.position.x
  let y := max left.position.y rightArea.position.y
  let r := min (right left) (right rightArea)
  let b := min (bottom left) (bottom rightArea)
  if r <= x || b <= y then none else some (rect x y (r - x) (b - y))

def union (left rightArea : Rect) : Rect :=
  let x := min left.position.x rightArea.position.x
  let y := min left.position.y rightArea.position.y
  rect x y (max (right left) (right rightArea) - x) (max (bottom left) (bottom rightArea) - y)

def splitH (value : Rect) (width : Int) : Rect × Rect :=
  let w := min value.size.width (nonNegative width)
  (rect value.position.x value.position.y w value.size.height,
    rect (value.position.x + w) value.position.y (value.size.width - w) value.size.height)

def splitV (value : Rect) (height : Int) : Rect × Rect :=
  let h := min value.size.height (nonNegative height)
  (rect value.position.x value.position.y value.size.width h,
    rect value.position.x (value.position.y + h) value.size.width (value.size.height - h))

def splitWithDivider (value : Rect) (placement : DetailPlacement) (extent : Int) : Rect × Rect × Rect :=
  match placement with
  | .right =>
    let dividerWidth := if value.size.width == 0 then 0 else 1
    let detailWidth := min (nonNegative extent) (max 0 (value.size.width - dividerWidth))
    let mainWidth := value.size.width - dividerWidth - detailWidth
    let main := rect value.position.x value.position.y mainWidth value.size.height
    let divider := rect (right main) value.position.y dividerWidth value.size.height
    let detail := rect (right divider) value.position.y detailWidth value.size.height
    (main, divider, detail)
  | .bottom =>
    let dividerHeight := if value.size.height == 0 then 0 else 1
    let detailHeight := min (nonNegative extent) (max 0 (value.size.height - dividerHeight))
    let mainHeight := value.size.height - dividerHeight - detailHeight
    let main := rect value.position.x value.position.y value.size.width mainHeight
    let divider := rect value.position.x (bottom main) value.size.width dividerHeight
    let detail := rect value.position.x (bottom divider) value.size.width detailHeight
    (main, divider, detail)

def sharedEdge (first second : Rect) : Option SharedEdge :=
  if right first == second.position.x && first.position.y == second.position.y && first.size.height == second.size.height then
    some {first, second, orientation := .right}
  else if bottom first == second.position.y && first.position.x == second.position.x && first.size.width == second.size.width then
    some {first, second, orientation := .bottom}
  else none

def applyEdgeDelta (edge : SharedEdge) (delta : EdgeDelta) (minimum : Int) : Except GeometryFailure SharedEdge :=
  let minimum := nonNegative minimum
  match edge.orientation with
  | .right =>
    let firstWidth := edge.first.size.width + delta.amount
    let secondWidth := edge.second.size.width - delta.amount
    if firstWidth < minimum || secondWidth < minimum then .error .edgeDeltaOutOfRange
    else .ok { edge with
      first := rect edge.first.position.x edge.first.position.y firstWidth edge.first.size.height
      second := rect (edge.second.position.x + delta.amount) edge.second.position.y secondWidth edge.second.size.height }
  | .bottom =>
    let firstHeight := edge.first.size.height + delta.amount
    let secondHeight := edge.second.size.height - delta.amount
    if firstHeight < minimum || secondHeight < minimum then .error .edgeDeltaOutOfRange
    else .ok { edge with
      first := rect edge.first.position.x edge.first.position.y edge.first.size.width firstHeight
      second := rect edge.second.position.x (edge.second.position.y + delta.amount) edge.second.size.width secondHeight }

private def requestedSize (total : Int) : Constraint → Int
  | .length value => nonNegative value
  | .percentage value => total * min 100 (nonNegative value) / 100
  | .ratio numerator denominator => if denominator <= 0 then 0 else total * nonNegative numerator / denominator
  | .min value => nonNegative value
  | .max _ | .fill => 0

private def isProportional : Constraint → Bool
  | .percentage _ | .ratio _ _ => true
  | _ => false

private def isMinimum : Constraint → Bool
  | .min _ => true
  | _ => false

private def isFill : Constraint → Bool
  | .fill => true
  | _ => false

private def distributeEven (remaining : Int) (constraints : List Constraint) (sizes : List Int)
    (accept : Constraint → Bool) : List Int :=
  let receivers := constraints.countP accept
  if remaining <= 0 || receivers == 0 then sizes else
    let share := remaining / receivers
    let excess := remaining % receivers
    let rec loop : Nat → List Constraint → List Int → List Int
      | _, [], [] => []
      | index, constraint :: restConstraints, size :: restSizes =>
        if accept constraint then
          let added := share + if index < excess.toNat then 1 else 0
          (size + added) :: loop (index + 1) restConstraints restSizes
        else size :: loop index restConstraints restSizes
      | _, _, _ => []
    loop 0 constraints sizes

private def distributeMaximum (remaining : Int) : List Constraint → List Int → List Int
  | [], [] => []
  | constraint :: restConstraints, size :: restSizes =>
    match constraint with
    | .max limit =>
      let added := min (nonNegative limit) (max 0 remaining)
      (size + added) :: distributeMaximum (remaining - added) restConstraints restSizes
    | _ => size :: distributeMaximum remaining restConstraints restSizes
  | _, _ => []

private def distribute (remaining : Int) (constraints : List Constraint) (sizes : List Int) : List Int :=
  if constraints.any isFill then distributeEven remaining constraints sizes isFill
  else if constraints.any isMinimum then distributeEven remaining constraints sizes isMinimum
  else if constraints.any isProportional then distributeEven remaining constraints sizes isProportional
  else distributeMaximum remaining constraints sizes

def resolveSizes (total : Int) (constraints : List Constraint) : Except GeometryFailure (List Int) :=
  if total < 0 then .error (.invalidSize total 0)
  else
    let initial := constraints.map (requestedSize total)
    let occupied := initial.foldl (· + ·) 0
    if occupied > total then .error .constraintResolutionFailure
    else
      let resolved := distribute (total - occupied) constraints initial
      if resolved.length != constraints.length || resolved.foldl (· + ·) 0 != total then .error .constraintResolutionFailure
      else .ok resolved

def layout (body : Rect) (placement : DetailPlacement) (detailColumns detailRows : Int) : Rect × Rect :=
  let extent := match placement with | .right => detailColumns | .bottom => detailRows
  let (main, _, detail) := splitWithDivider body placement extent
  (main, detail)

def frameAreas (screen : Rect) (placement : DetailPlacement) (detailColumns detailRows : Int) : FrameAreas :=
  let inner := inset 1 screen
  let hintHeight := if inner.size.height == 0 then 0 else 1
  let hintDividerHeight := if inner.size.height <= 1 then 0 else 1
  let hint := rect inner.position.x (bottom inner - hintHeight) inner.size.width hintHeight
  let hintDivider := rect inner.position.x (hint.position.y - hintDividerHeight) inner.size.width hintDividerHeight
  let panel := rect inner.position.x inner.position.y inner.size.width (inner.size.height - hintHeight - hintDividerHeight)
  let extent := match placement with | .right => detailColumns | .bottom => detailRows
  let (main, divider, detail) := splitWithDivider panel placement extent
  {main, detail, divider, hintDivider, hint}

end NecoLean.Tui
