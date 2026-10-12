import NecoLean.Tui.Types
import NecoLean.Tui.Layout
import NecoLean.Tui.Surface

set_option autoImplicit false

namespace NecoLean.Tui

structure OverlayEntry where
  id : String
  area : Rect
  visible : Bool := false
  capture : Bool := false
  order : Int := 0
  deriving Repr, BEq, DecidableEq

structure OverlayState where
  entries : List OverlayEntry := []
  focus : Option String := none
  restore : Option String := none
  deriving Repr, BEq, DecidableEq

structure OverlaySurface where
  id : String
  surface : Surface
  deriving Repr, BEq, DecidableEq

private def entry? (state : OverlayState) (id : String) : Option OverlayEntry :=
  state.entries.find? (fun entry => entry.id == id)

private def visibleEntry? (state : OverlayState) (id : String) : Option OverlayEntry :=
  state.entries.find? (fun entry => entry.id == id && entry.visible)

def register (state : OverlayState) (entry : OverlayEntry) : Except OverlayFailure OverlayState :=
  if entry.id.isEmpty then .error (.invalidOverlayRect entry.id)
  else if entry.area.size.width == 0 || entry.area.size.height == 0 then .error (.invalidOverlayRect entry.id)
  else if state.entries.any (fun current => current.id == entry.id) then .error (.duplicateOverlayId entry.id)
  else .ok {state with entries := state.entries ++ [entry]}

def captureTarget (state : OverlayState) : Option String :=
  state.entries.foldl (fun best entry =>
    if entry.visible && entry.capture then
      match best with
      | none => some entry
      | some current => if entry.order > current.order then some entry else some current
    else best) none |>.map (·.id)

private def restoreFocus (state : OverlayState) : OverlayState :=
  match captureTarget state with
  | some id => {state with focus := some id}
  | none =>
    match state.restore with
    | some id => if (visibleEntry? state id).isSome then {state with focus := some id, restore := none} else {state with focus := none, restore := none}
    | none => {state with focus := none}

def remove (state : OverlayState) (id : String) : Except OverlayFailure OverlayState :=
  if (entry? state id).isNone then .error (.missingOverlayId id)
  else .ok (restoreFocus {state with entries := state.entries.filter (fun entry => entry.id != id), focus := if state.focus == some id then none else state.focus})

def setVisible (state : OverlayState) (id : String) (visible : Bool) : Except OverlayFailure OverlayState :=
  if (entry? state id).isNone then .error (.missingOverlayId id)
  else
    let next := {state with entries := state.entries.map (fun entry => if entry.id == id then {entry with visible} else entry)}
    if visible then .ok next else .ok (restoreFocus {next with focus := if next.focus == some id then none else next.focus})

def raise (state : OverlayState) (id : String) : Except OverlayFailure OverlayState :=
  if (entry? state id).isNone then .error (.missingOverlayId id)
  else
    let order := state.entries.foldl (fun current entry => max current entry.order) 0 + 1
    .ok {state with entries := state.entries.map (fun entry => if entry.id == id then {entry with order} else entry)}

def resolvePlacement (entry : OverlayEntry) (screen : Rect) : Rect :=
  (intersection entry.area screen).getD rectZero

def focus (state : OverlayState) (id : String) : Except OverlayFailure OverlayState :=
  match visibleEntry? state id with
  | none => .error (.invalidFocusTarget id)
  | some entry =>
    if !entry.capture then .error (.invalidFocusTarget id)
    else .ok {state with restore := state.focus, focus := some id}

def unfocus (state : OverlayState) : OverlayState :=
  restoreFocus {state with focus := none}

private def blit (base : Surface) (layer : Surface) : Surface :=
  (positions layer.area).foldl (fun result position => setCell result position (getCell layer position)) base

private def insertByOrder (entry : OverlayEntry) : List OverlayEntry → List OverlayEntry
  | [] => [entry]
  | current :: rest => if entry.order <= current.order then entry :: current :: rest else current :: insertByOrder entry rest

private def orderedEntries (entries : List OverlayEntry) : List OverlayEntry :=
  entries.foldr insertByOrder []

def compose (base : Surface) (state : OverlayState) (overlays : List OverlaySurface) : Surface :=
  (orderedEntries (state.entries.filter (·.visible))).foldl (fun result entry =>
    match overlays.find? (fun layer => layer.id == entry.id) with
    | some layer => blit result (clip layer.surface (resolvePlacement entry base.area))
    | none => result) base


end NecoLean.Tui
