set_option autoImplicit false

namespace NecoLean.System

abbrev FilePath := _root_.System.FilePath

inductive Failure where
  | file (path : FilePath) (message : String)
  | processStart (command : String) (message : String)
  | nonZeroExit (command : String) (exitCode : UInt32) (stdout : ByteArray) (stderr : ByteArray)
  deriving BEq

instance : BEq FilePath := inferInstance

structure ProcessRequest where
  command : String
  arguments : List String := []
  stdin : ByteArray := ByteArray.empty
  deriving BEq

structure ProcessOutput where
  stdout : ByteArray
  stderr : ByteArray
  exitCode : UInt32
  deriving BEq

private def exceptionText (error : IO.Error) : String := IO.Error.toString error

private def processArgs (request : ProcessRequest) : IO.Process.SpawnArgs :=
  { stdin := .piped
    stdout := .piped
    stderr := .piped
    cmd := request.command
    args := request.arguments.toArray
    cwd := none
    env := #[]
    inheritEnv := true
    setsid := false }

private partial def readAll (handle : IO.FS.Handle) (chunks : ByteArray) : IO ByteArray := do
  let chunk ← handle.read 4096
  if chunk.isEmpty then
    return chunks
  readAll handle (chunks ++ chunk)

private def writeStdin (stdin : ByteArray) (handle : IO.FS.Handle) : IO Unit := do
  handle.write stdin
  handle.flush

private def startsWithBytes (bytes : ByteArray) (prefixBytes : ByteArray) : Bool :=
  prefixBytes.toList == bytes.toList.take prefixBytes.size

protected def readBytes (path : FilePath) : IO (Except Failure ByteArray) := do
  try
    return .ok (← IO.FS.readBinFile path)
  catch error =>
    return .error (.file path (exceptionText error))

protected def writeBytes (path : FilePath) (bytes : ByteArray) : IO (Except Failure Unit) := do
  try
    IO.FS.writeBinFile path bytes
    return .ok ()
  catch error =>
    return .error (.file path (exceptionText error))

protected def run (request : ProcessRequest) : IO (Except Failure ProcessOutput) := do
  try
    let spawned ← IO.Process.spawn (processArgs request)
    let (child, stdinTask) ← do
      let (stdin, child) ← spawned.takeStdin
      let stdinTask ← IO.asTask (writeStdin request.stdin stdin) Task.Priority.dedicated
      pure (child, stdinTask)
    let stdoutTask ← IO.asTask (readAll child.stdout ByteArray.empty) Task.Priority.dedicated
    let stderrTask ← IO.asTask (readAll child.stderr ByteArray.empty) Task.Priority.dedicated
    IO.ofExcept stdinTask.get
    let exitCode ← child.wait
    let stdout ← IO.ofExcept stdoutTask.get
    let stderr ← IO.ofExcept stderrTask.get
    let result : ProcessOutput := { stdout, stderr, exitCode }
    if exitCode == 0 then
      return .ok result
    else if exitCode == 255 && startsWithBytes stderr "could not execute external process".toUTF8 then
      return .error (.processStart request.command (String.fromUTF8? stderr |>.getD "process start failed"))
    else
      return .error (.nonZeroExit request.command exitCode stdout stderr)
  catch error =>
    return .error (.processStart request.command (exceptionText error))

protected def sqliteQuery (database : String) (query : String) : IO (Except Failure ByteArray) := do
  match ← NecoLean.System.run { command := "sqlite3", arguments := ["-noheader", database, query] } with
  | .ok output => return .ok output.stdout
  | .error failure => return .error failure

end NecoLean.System
