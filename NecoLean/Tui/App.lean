import NecoLean.Tui.Model
import NecoLean.Tui.Terminal
import NecoLean.Tui.Renderer

set_option autoImplicit false

namespace NecoLean.Tui

structure AppState (σ : Type) where
  terminal : TerminalState σ
  model : Model
  frame : Surface

def withCleanup {ε α : Type} (body : IO (Except ε α)) (cleanupAction : IO Unit) : IO (Except ε α) := do
  try
    body
  finally
    cleanupAction

def appStep {σ : Type} (backend : TerminalBackend σ) (state : AppState σ) (timeoutMs : Int) :
    IO (Except TuiFailure (AppState σ)) := do
  match ← nextSize backend state.terminal with
  | .error failure => return .error (.terminal failure)
  | .ok (size, sizedTerminal) =>
    match resizeModel state.model size with
    | .error failure => return .error failure
    | .ok sizedModel =>
      let nextFrame := renderFrame sizedModel (rect 0 0 size.width size.height)
      let operations := diffToAnsi state.frame nextFrame
      match ← render backend sizedTerminal operations with
      | .error failure => return .error (.terminal failure)
      | .ok renderedTerminal =>
        match ← poll backend renderedTerminal timeoutMs with
        | .error failure => return .error (.terminal failure)
        | .ok (event, polledTerminal) =>
          match update event sizedModel with
          | .error failure => return .error failure
          | .ok nextModel => return .ok { terminal := polledTerminal, model := nextModel, frame := nextFrame }

private partial def runLoop {σ : Type} (backend : TerminalBackend σ)
    (stateRef : IO.Ref (AppState σ)) : IO (Except TuiFailure Unit) := do
  let state ← stateRef.get
  match ← appStep backend state 50 with
  | .error failure => return .error failure
  | .ok next =>
    stateRef.set next
    if next.model.quit then return .ok ()
    runLoop backend stateRef

def runModelWithBackend {σ : Type} (backend : TerminalBackend σ) (model : Model) :
    IO (Except TuiFailure Unit) := do
  match validateTree model.tree with
  | .error failure => return .error (.tree failure)
  | .ok () =>
    match ← init backend with
    | .error failure => return .error (.terminal failure)
    | .ok terminalState =>
      let initial : AppState σ := {
        terminal := terminalState
        model := synchronizedViewport model
        frame := emptySurface (rect 0 0 (-1) (-1))
      }
      let stateRef ← IO.mkRef initial
      withCleanup (runLoop backend stateRef) (cleanup backend (← stateRef.get).terminal)

end NecoLean.Tui
