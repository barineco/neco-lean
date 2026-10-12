import NecoLean.System
import NecoLean.Tui.App
import NecoLean.Tui.Surface

set_option autoImplicit false

namespace NecoLean.Tui

structure PosixTerminalState where
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream
  tty : Bool
  savedModes : Option String
  rawModeStarted : Bool
  alternateScreenStarted : Bool
  cursorHideStarted : Bool
  mouseReportingStarted : Bool
  size : TerminalSize

namespace Posix

private def reasonOfSystemFailure (failure : NecoLean.System.Failure) : String :=
  match failure with
  | .file path message => s!"{path}: {message}"
  | .processStart command message => s!"{command}: {message}"
  | .nonZeroExit command code _ stderr =>
    let text := String.fromUTF8? stderr |>.getD ""
    s!"{command}: exit {code} {text}"

private def streamText (bytes : ByteArray) : Except String String :=
  match String.fromUTF8? bytes with
  | some text => .ok text
  | none => .error "invalid UTF-8"

private def runStty (command : String) : IO (Except String String) := do
  match ← NecoLean.System.run { command := "/bin/sh", arguments := ["-c", command] } with
  | .error failure => return .error (reasonOfSystemFailure failure)
  | .ok output => return streamText output.stdout

private def readTtyModes : IO (Except String String) :=
  runStty "stty -g </dev/tty"

private def configureRawMode : IO (Except String Unit) := do
  match ← runStty "stty raw -echo min 0 time 1 </dev/tty" with
  | .ok _ => return .ok ()
  | .error reason => return .error reason

private def readTtySize : IO (Except String String) :=
  runStty "stty size </dev/tty"

private def writeAnsi (stdout : IO.FS.Stream) (text : String) : IO (Except String Unit) := do
  try
    stdout.putStr text
    return .ok ()
  catch error =>
    return .error (IO.Error.toString error)

private def flush (stdout : IO.FS.Stream) : IO (Except String Unit) := do
  try
    stdout.flush
    return .ok ()
  catch error =>
    return .error (IO.Error.toString error)

private def disableMouse (stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "\u001b[?1000l\u001b[?1002l\u001b[?1006l"

private def showCursor (stdout : IO.FS.Stream) : IO Unit :=
  stdout.putStr "\u001b[?25h"

private def leaveAlternate (stdout : IO.FS.Stream) : IO Unit :=
  stdout.putStr "\u001b[?1049l"

private def enableAlternate (stdout : IO.FS.Stream) : IO Unit :=
  stdout.putStr "\u001b[?1049h"

private def hideCursor (stdout : IO.FS.Stream) : IO Unit :=
  stdout.putStr "\u001b[?25l"

private def enableMouse (stdout : IO.FS.Stream) : IO Unit :=
  stdout.putStr "\u001b[?1000h\u001b[?1002h\u001b[?1006h"

private def restoreTtyModes (savedModes : String) : IO Unit := do
  let request : NecoLean.System.ProcessRequest := {
    command := "/bin/sh"
    arguments := ["-c", "stty \"$(cat)\" </dev/tty"]
    stdin := savedModes.toUTF8
  }
  let _ ← NecoLean.System.run request
  pure ()

private def attempt (action : IO Unit) : IO Unit := do
  try
    action
  catch _ =>
    pure ()

private def restoreTerminal (initial : PosixTerminalState) : IO Unit := do
  let afterMouse ← if initial.mouseReportingStarted then
      let started := { initial with mouseReportingStarted := false }
      let _ ← attempt (disableMouse started.stdout)
      pure started
    else pure initial
  let afterCursor ← if afterMouse.cursorHideStarted then
      let started := { afterMouse with cursorHideStarted := false }
      let _ ← attempt (showCursor started.stdout)
      pure started
    else pure afterMouse
  let afterAlternate ← if afterCursor.alternateScreenStarted then
      let started := { afterCursor with alternateScreenStarted := false }
      let _ ← attempt (leaveAlternate started.stdout)
      pure started
    else pure afterCursor
  let _ ← attempt afterAlternate.stdout.flush
  let afterModes ← match afterAlternate.savedModes with
    | none => pure afterAlternate
    | some savedModes =>
      let started := { afterAlternate with savedModes := none }
      let _ ← attempt (restoreTtyModes savedModes)
      pure started
  let _ ← attempt afterModes.stdout.flush

private def failureReason (label : String) (reason : String) : TerminalFailure :=
  .init s!"{label}: {reason}"

def clampDeciseconds (milliseconds : Int) : Int :=
  if milliseconds <= 0 then 0
  else
    let value := (milliseconds + 99) / 100
    if value > 255 then 255 else value

def parseTtySize (text : String) : Except TerminalFailure TerminalSize :=
  let parts := (text.trimAscii.toString.split (· == ' ')).toList.map String.Slice.toString |>.filter (· != "")
  match parts with
  | [heightText, widthText] =>
    match heightText.toInt?, widthText.toInt? with
    | some height, some width =>
      if width < 0 || height < 0 then .error (.size "negative terminal size")
      else .ok { width, height }
    | _, _ => .error (.size "invalid terminal size")
  | _ => .error (.size "invalid terminal size")

def sttyCommand (milliseconds : Int) : String :=
  s!"stty raw -echo min 0 time {clampDeciseconds milliseconds} </dev/tty"

private def init : IO (Except TerminalFailure PosixTerminalState) := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stdinTty ← stdin.isTty
  let stdoutTty ← stdout.isTty
  if !(stdinTty && stdoutTty) then
    return .error (.unsupported "stdin and stdout must be TTY streams")
  match ← readTtyModes with
  | .error reason => return .error (failureReason "saved mode" reason)
  | .ok savedModes =>
    let initial : PosixTerminalState := {
      stdin, stdout, tty := true, savedModes := some savedModes
      rawModeStarted := false, alternateScreenStarted := false
      cursorHideStarted := false, mouseReportingStarted := false
      size := { width := 0, height := 0 }
    }
    let rawStarted := { initial with rawModeStarted := true }
    match ← configureRawMode with
    | .error reason => restoreTerminal rawStarted; return .error (failureReason "raw mode" reason)
    | .ok () =>
      let alternateStarted := { rawStarted with alternateScreenStarted := true }
      match ← writeAnsi stdout "\u001b[?1049h" with
      | .error reason => restoreTerminal alternateStarted; return .error (failureReason "alternate screen" reason)
      | .ok () =>
        let cursorStarted := { alternateStarted with cursorHideStarted := true }
        match ← writeAnsi stdout "\u001b[?25l" with
        | .error reason => restoreTerminal cursorStarted; return .error (failureReason "cursor" reason)
        | .ok () =>
          let mouseStarted := { cursorStarted with mouseReportingStarted := true }
          match ← writeAnsi stdout "\u001b[?1000h\u001b[?1002h\u001b[?1006h" with
          | .error reason => restoreTerminal mouseStarted; return .error (failureReason "mouse" reason)
          | .ok () =>
            match ← readTtySize with
            | .error reason => restoreTerminal mouseStarted; return .error (.init s!"size: {reason}")
            | .ok text =>
              match parseTtySize text with
              | .error _ => restoreTerminal mouseStarted; return .error (.init "invalid terminal size")
              | .ok size =>
                match ← flush stdout with
                | .error reason => restoreTerminal { mouseStarted with size }; return .error (.init s!"flush: {reason}")
                | .ok () => return .ok { mouseStarted with size }

private def render (state : PosixTerminalState) (operations : List RenderOp) :
    IO (Except TerminalFailure PosixTerminalState) := do
  match ← writeAnsi state.stdout (renderOpsToAnsi operations) with
  | .error reason => return .error (.render reason)
  | .ok () =>
    match ← flush state.stdout with
    | .error reason => return .error (.render reason)
    | .ok () => return .ok state

private def poll (state : PosixTerminalState) (timeoutMs : Int) :
    IO (Except TerminalFailure (RawChunk × PosixTerminalState)) := do
  let command := sttyCommand timeoutMs
  match ← runStty command with
  | .error reason => return .error (.input reason)
  | .ok _ =>
    try
      let bytes ← state.stdin.read 4096
      match String.fromUTF8? bytes with
      | some text => return .ok ({ text }, state)
      | none => return .error (.input "invalid UTF-8 input")
    catch error =>
      return .error (.input (IO.Error.toString error))

private def nextSize (state : PosixTerminalState) :
    IO (Except TerminalFailure (TerminalSize × PosixTerminalState)) := do
  match ← readTtySize with
  | .error reason => return .error (.size reason)
  | .ok text =>
    match parseTtySize text with
    | .error failure => return .error failure
    | .ok size => return .ok (size, { state with size })

def backend : TerminalBackend PosixTerminalState := {
  init
  render
  poll
  nextSize
  cleanup := restoreTerminal
}

def runModel (model : Model) : IO (Except TuiFailure Unit) :=
  runModelWithBackend backend model

end Posix

end NecoLean.Tui
