import NecoLean.Tui.Types

set_option autoImplicit false

namespace NecoLean.Tui

structure ViewportState where
  top : Int
  anchor : String
  selected : String
  size : Int
  deriving Repr, BEq, DecidableEq

structure ViewportItem where
  id : String
  extent : Int
  deriving Repr, BEq, DecidableEq

structure ViewportObservation where
  width : Int
  height : Int
  top : Int
  rows : List String
  selectedIndex : Int
  selectionVisible : Bool
  deriving Repr, BEq, DecidableEq

structure ViewportWindow (α : Type) where
  top : Int
  visible : List α
  deriving Repr, BEq

abbrev Window := ViewportWindow

private def itemExtent (item : ViewportItem) : Int := max 1 item.extent

private def extentSum (items : List ViewportItem) : Int :=
  items.foldl (fun total item => total + itemExtent item) 0

def clampTop (itemCount requested : Int) : Int :=
  min (max 0 requested) (max 0 (itemCount - 1))

private def takeVisible : Nat → Int → List ViewportItem → List ViewportItem
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, remaining, item :: rest =>
    if remaining <= 0 then []
    else item :: takeVisible fuel (remaining - itemExtent item) rest

def window (items : List ViewportItem) (requestedTop visibleRows : Int) : ViewportWindow ViewportItem :=
  let top := clampTop items.length requestedTop
  {top, visible := takeVisible items.length (max 0 visibleRows) (items.drop top.toNat)}

private def topForSelection (items : List ViewportItem) (visibleRows selectedIndex : Int) : Int :=
  if visibleRows <= 0 then selectedIndex else
    let candidates := List.range (selectedIndex.toNat + 1)
    match candidates.find? (fun candidate =>
      let preceding := items.drop candidate |>.take (selectedIndex.toNat - candidate)
      extentSum preceding < visibleRows) with
    | some candidate => Int.ofNat candidate
    | none => selectedIndex

def ensureVisible (items : List ViewportItem) (visibleRows selectedIndex requestedTop : Int) : Int :=
  let top := clampTop items.length requestedTop
  if selectedIndex < top then selectedIndex
  else
    let preceding := items.drop top.toNat |>.take (selectedIndex - top).toNat
    if visibleRows > 0 && extentSum preceding < visibleRows then top
    else clampTop items.length (topForSelection items visibleRows selectedIndex)

def select (state : ViewportState) (selected : String) (items : List ViewportItem) : Except ViewportFailure ViewportState :=
  match items.findIdx? (·.id == selected) with
  | none => .error (.selectedUnavailable selected)
  | some index =>
    let top := ensureVisible items state.size (Int.ofNat index) state.top
    .ok {state with selected, top, anchor := items[top.toNat]?.map (·.id) |>.getD state.anchor}

def scroll (state : ViewportState) (delta : Int) (items : List ViewportItem) : ViewportState :=
  let top := clampTop items.length (state.top + delta)
  {state with top, anchor := items[top.toNat]?.map (·.id) |>.getD state.anchor}

def refresh (state : ViewportState) (items : List ViewportItem) : ViewportState :=
  match items.findIdx? (·.id == state.anchor) with
  | some index => {state with top := clampTop items.length (Int.ofNat index)}
  | none =>
    let top := clampTop items.length state.top
    {state with top, anchor := items[top.toNat]?.map (·.id) |>.getD ""}

def resize (state : ViewportState) (size : Int) (items : List ViewportItem) : ViewportState :=
  let size := max 0 size
  {state with size, top := clampTop items.length state.top}

def observe (state : ViewportState) (width : Int) (items : List ViewportItem) : Except ViewportFailure ViewportObservation :=
  if state.size < 0 then .error (.invalidViewportSize state.size)
  else
    match items.findIdx? (·.id == state.selected) with
    | none => .error (.selectedUnavailable state.selected)
    | some selectedIndex =>
      let visible := window items state.top state.size
      .ok {
        width := max 0 width
        height := state.size
        top := visible.top
        rows := visible.visible.map (·.id)
        selectedIndex := Int.ofNat selectedIndex
        selectionVisible := visible.visible.any (·.id == state.selected)
      }

end NecoLean.Tui
