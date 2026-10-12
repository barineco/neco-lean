import NecoLean.Tui.Types
import NecoLean.Tui.Event
import NecoLean.Tui.Surface

set_option autoImplicit false

namespace NecoLean.Tui

structure TerminalBackend (σ : Type) where
  init : IO (Except TerminalFailure σ)
  render : σ → List RenderOp → IO (Except TerminalFailure σ)
  poll : σ → Int → IO (Except TerminalFailure (RawChunk × σ))
  nextSize : σ → IO (Except TerminalFailure (TerminalSize × σ))
  cleanup : σ → IO Unit

structure TerminalState (σ : Type) where
  backend : σ
  pending : List InputEvent := []
  remainder : InputRemainder := {}
  size : TerminalSize := { width := 0, height := 0 }

def init {σ : Type} (backend : TerminalBackend σ) : IO (Except TerminalFailure (TerminalState σ)) := do
  match ← backend.init with
  | .error failure => return .error failure
  | .ok state => return .ok { backend := state }

def nextSize {σ : Type} (backend : TerminalBackend σ) (state : TerminalState σ) :
    IO (Except TerminalFailure (TerminalSize × TerminalState σ)) := do
  match ← backend.nextSize state.backend with
  | .error failure => return .error failure
  | .ok (size, nextBackend) =>
    let nextState := { state with backend := nextBackend, size := size }
    return .ok (size, nextState)

def poll {σ : Type} (backend : TerminalBackend σ) (state : TerminalState σ) (timeoutMs : Int) :
    IO (Except TerminalFailure (InputEvent × TerminalState σ)) := do
  match state.pending with
  | event :: rest => return .ok (event, { state with pending := rest })
  | [] =>
    match ← backend.poll state.backend timeoutMs with
    | .error failure => return .error failure
    | .ok (chunk, nextBackend) =>
      let decoded := decodeChunk chunk.text state.remainder
      let sizedState := { state with backend := nextBackend, remainder := decoded.remainder }
      match decoded.events with
      | event :: rest => return .ok (event, { sizedState with pending := rest })
      | [] =>
        match ← nextSize backend sizedState with
        | .error failure => return .error failure
        | .ok (size, nextState) =>
          if size == state.size then return .ok (.tick, nextState)
          else return .ok (.resize size, nextState)

def render {σ : Type} (backend : TerminalBackend σ) (state : TerminalState σ) (operations : List RenderOp) :
    IO (Except TerminalFailure (TerminalState σ)) := do
  match ← backend.render state.backend operations with
  | .error failure => return .error failure
  | .ok nextBackend => return .ok { state with backend := nextBackend }

def cleanup {σ : Type} (backend : TerminalBackend σ) (state : TerminalState σ) : IO Unit :=
  backend.cleanup state.backend

end NecoLean.Tui
