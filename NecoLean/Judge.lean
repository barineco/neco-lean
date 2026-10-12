import NecoLean.System

set_option autoImplicit false

namespace NecoLean.Judge

abbrev CaseName := String
abbrev Decimal := Float
abbrev Arguments := List String

structure JudgeRequest where
  executablePath : System.FilePath
  arguments : List String
  testCaseDirectory : System.FilePath
  timeLimitSeconds : Float
  deriving BEq

structure CasePair where
  caseName : CaseName
  inputPath : System.FilePath
  expectedOutputPath : System.FilePath
  inputBytes : ByteArray
  expectedOutput : ByteArray
  deriving BEq

structure CasePairs where
  request : JudgeRequest
  pairs : List CasePair
  deriving BEq

structure MeasuredCase where
  casePair : CasePair
  stdout : ByteArray
  stderr : ByteArray
  exitCode : UInt32
  elapsedSeconds : Float
  maximumResidentMemoryBytes : Nat
  timeLimitSeconds : Float
  timedOut : Bool := false
  deriving BEq

structure MeasuredProcess where
  measurements : List MeasuredCase
  deriving BEq

inductive CaseVerdict where
  | TimeLimitExceeded (measurement : MeasuredCase)
  | RuntimeError (measurement : MeasuredCase)
  | WrongAnswer (measurement : MeasuredCase)
  | Accepted (measurement : MeasuredCase)
  deriving BEq

structure JudgeReport where
  verdict : CaseVerdict
  selectedMeasurement : MeasuredCase
  measurements : List MeasuredCase
  deriving BEq

inductive JudgeFailure where
  | File (path : System.FilePath) (message : String)
  | ProcessStart (command : String) (message : String)
  | TemporaryStderrFile (message : String)
  | DirectoryEnumerationFailure
      (command : String) (exitCode : UInt32) (stdout : ByteArray) (stderr : ByteArray)
  | MalformedDirectoryEnumeration (text : String)
  | NonregularCaseFile (path : System.FilePath)
  | InvalidCaseFileName (path : System.FilePath)
  | DuplicateCaseSuffix (caseName : CaseName) (suffix : String)
  | MissingCaseCounterpart (caseName : CaseName) (missingSuffix : String)
  | MeasurementUnavailable (caseName : CaseName) (field : String)
  | MalformedMeasurement (caseName : CaseName) (field : String) (text : String)
  deriving BEq

structure MeasurementRequest where
  platform : String
  childStderrPath : System.FilePath
  casePair : CasePair
  request : JudgeRequest

structure JudgeRuntime where
  enumerateCaseFiles : JudgeRequest -> IO (Except JudgeFailure ByteArray)
  readBytes : System.FilePath -> IO (Except JudgeFailure ByteArray)
  platformName : CaseName -> IO (Except JudgeFailure String)
  runMeasurement : MeasurementRequest -> IO (Except JudgeFailure System.ProcessOutput)
  withTemporaryStderrFile :
    ((System.FilePath -> IO (Except JudgeFailure MeasuredCase)) ->
      IO (Except JudgeFailure MeasuredCase))

private def mapSystemFailure (failure : System.Failure) : JudgeFailure :=
  match failure with
  | .file path message => .File path message
  | .processStart command message => .ProcessStart command message
  | .nonZeroExit command exitCode stdout stderr =>
    .DirectoryEnumerationFailure command exitCode stdout stderr

private def splitNulFields (bytes : ByteArray) : List ByteArray :=
  let step (fields : List ByteArray × ByteArray) (byte : UInt8) : List ByteArray × ByteArray :=
    if byte == 0 then
      (fields.1 ++ [fields.2], ByteArray.empty)
    else
      (fields.1, fields.2.push byte)
  let fields := bytes.toList.foldl step ([], ByteArray.empty)
  fields.1 ++ [fields.2]

private def directoryText (bytes : ByteArray) : String :=
  String.fromUTF8? bytes |>.getD "<non-UTF-8 directory enumeration>"

private def parseDirectoryEntries (stdout : ByteArray) : Except JudgeFailure (List (String × System.FilePath)) :=
  let fields := splitNulFields stdout
  if fields.isEmpty || !fields.getLast!.isEmpty then
    .error (.MalformedDirectoryEnumeration (directoryText stdout))
  else
    let rec go (remaining : List ByteArray) (entries : List (String × System.FilePath)) :
        Except JudgeFailure (List (String × System.FilePath)) :=
      match remaining with
      | [] => .ok entries
      | markerBytes :: pathBytes :: rest =>
        match String.fromUTF8? markerBytes, String.fromUTF8? pathBytes with
        | some marker, some pathText =>
          if marker == "F" || marker == "N" then
            go rest (entries ++ [(marker, (pathText : System.FilePath))])
          else
            .error (.MalformedDirectoryEnumeration (directoryText stdout))
        | _, _ => .error (.MalformedDirectoryEnumeration (directoryText stdout))
      | _ => .error (.MalformedDirectoryEnumeration (directoryText stdout))
    go fields.dropLast []

private def caseFileName (path : System.FilePath) : Except JudgeFailure (CaseName × String) :=
  let text := (path.toString.splitOn "/").getLastD ""
  if text.endsWith ".in" then
    let name := String.ofList (text.toList.reverse.drop 3 |>.reverse)
    if name.isEmpty then .error (.InvalidCaseFileName path) else .ok (name, ".in")
  else if text.endsWith ".out" then
    let name := String.ofList (text.toList.reverse.drop 4 |>.reverse)
    if name.isEmpty then .error (.InvalidCaseFileName path) else .ok (name, ".out")
  else
    .error (.InvalidCaseFileName path)

private def appendCaseFile
    (files : List (CaseName × Option System.FilePath × Option System.FilePath))
    (path : System.FilePath) : Except JudgeFailure (List (CaseName × Option System.FilePath × Option System.FilePath)) :=
  match caseFileName path with
  | .error failure => .error failure
  | .ok (caseName, suffix) =>
    let rec go (remaining : List (CaseName × Option System.FilePath × Option System.FilePath)) :
        Except JudgeFailure (List (CaseName × Option System.FilePath × Option System.FilePath)) :=
      match remaining with
      | [] =>
        if suffix == ".in" then .ok [(caseName, some path, none)] else .ok [(caseName, none, some path)]
      | (name, inputPath, outputPath) :: rest =>
        if name != caseName then
          match go rest with
          | .ok updated => .ok ((name, inputPath, outputPath) :: updated)
          | .error failure => .error failure
        else if suffix == ".in" then
          match inputPath with
          | some _ => .error (.DuplicateCaseSuffix caseName suffix)
          | none => .ok ((name, some path, outputPath) :: rest)
        else
          match outputPath with
          | some _ => .error (.DuplicateCaseSuffix caseName suffix)
          | none => .ok ((name, inputPath, some path) :: rest)
    go files

private def sortCasePairs (pairs : List CasePair) : List CasePair :=
  pairs.mergeSort (fun left right => left.caseName < right.caseName)

private def collectCaseFiles (stdout : ByteArray) : Except JudgeFailure (List (CaseName × Option System.FilePath × Option System.FilePath)) :=
  match parseDirectoryEntries stdout with
  | .error failure => .error failure
  | .ok entries =>
    let rec collect (remaining : List (String × System.FilePath))
        (files : List (CaseName × Option System.FilePath × Option System.FilePath)) :
        Except JudgeFailure (List (CaseName × Option System.FilePath × Option System.FilePath)) :=
      match remaining with
      | [] => .ok files
      | (marker, path) :: rest =>
        if marker == "N" then
          .error (.NonregularCaseFile path)
        else
          match appendCaseFile files path with
          | .error failure => .error failure
          | .ok updated => collect rest updated
    collect entries []

private def readCasePairs (runtime : JudgeRuntime) (request : JudgeRequest)
    (files : List (CaseName × Option System.FilePath × Option System.FilePath)) : IO (Except JudgeFailure CasePairs) := do
  let rec go (remaining : List (CaseName × Option System.FilePath × Option System.FilePath))
      (pairs : List CasePair) : IO (Except JudgeFailure (List CasePair)) := do
    match remaining with
    | [] => return .ok (sortCasePairs pairs)
    | (caseName, some inputPath, some expectedOutputPath) :: rest =>
      match ← runtime.readBytes inputPath, ← runtime.readBytes expectedOutputPath with
      | .ok inputBytes, .ok expectedOutput =>
        go rest (pairs ++ [{ caseName, inputPath, expectedOutputPath, inputBytes, expectedOutput }])
      | .error failure, _ => return .error failure
      | _, .error failure => return .error failure
    | (caseName, none, _) :: _ => return .error (.MissingCaseCounterpart caseName ".in")
    | (caseName, _, none) :: _ => return .error (.MissingCaseCounterpart caseName ".out")
  match ← go files [] with
  | .ok pairs => return .ok { request, pairs }
  | .error failure => return .error failure

private def asciiHorizontalWhitespace (character : Char) : Bool :=
  character == ' ' || character == '\t'

private def horizontalFields (line : String) : List String :=
  let fields := line.toList.foldl (fun fields character =>
    if asciiHorizontalWhitespace character then
      if fields.2.isEmpty then fields else (fields.1 ++ [fields.2], [])
    else
      (fields.1, fields.2 ++ [character])) ([], [])
  let allFields := if fields.2.isEmpty then fields.1 else fields.1 ++ [fields.2]
  allFields.map String.ofList

private def asciiDigit (character : Char) : Bool :=
  character >= '0' && character <= '9'

private def decimalDigits (characters : List Char) : Option Nat :=
  if characters.isEmpty || !characters.all asciiDigit then
    none
  else
    some (characters.foldl (fun value character => value * 10 + (character.toNat - '0'.toNat)) 0)

private def parseDecimal (text : String) : Option Decimal :=
  match text.splitOn "." with
  | [whole, fraction] =>
    match decimalDigits whole.toList, decimalDigits fraction.toList with
    | some wholeValue, some fractionValue =>
      let mantissa := wholeValue * (10 ^ fraction.length) + fractionValue
      let value := Float.ofScientific mantissa true fraction.length
      if value.isFinite then some value else none
    | _, _ => none
  | _ => none

private def parseNatDecimal (text : String) : Option Nat :=
  decimalDigits text.toList

private def onlyLineWithPrefix (prefixText : String) (lines : List String) : Option String :=
  match lines.filterMap (fun line =>
    if line.startsWith prefixText then some (String.ofList (line.toList.drop prefixText.length)) else none) with
  | [value] => some value
  | _ => none

private def timeoutMarker (caseName : CaseName) (lines : List String) : Except JudgeFailure Bool :=
  match onlyLineWithPrefix "__NECO_JUDGE_TIMED_OUT__=" lines with
  | none => .ok false
  | some "0" => .ok false
  | some "1" => .ok true
  | some text => .error (.MalformedMeasurement caseName "timedOut" text)

private def parseDarwinMeasurement (caseName : CaseName) (stderr : ByteArray) : Except JudgeFailure (Decimal × Nat × Bool) :=
  match String.fromUTF8? stderr with
  | none => .error (.MeasurementUnavailable caseName "measurementStream")
  | some text =>
    let lines := text.splitOn "\n"
    let elapsedValues := lines.flatMap (fun line =>
      let fields := horizontalFields line
      fields.zipWith (fun left right => (left, right)) fields.tail
        |>.filterMap (fun (left, right) => if right == "real" then some left else none))
    let rssLines := lines.filter (fun line =>
      let fields := horizontalFields line
      fields.length >= 5 && fields.drop (fields.length - 4) == ["maximum", "resident", "set", "size"])
    match elapsedValues, rssLines, timeoutMarker caseName lines with
    | [elapsedText], [rssLine], .ok timedOut =>
      let rssFields := horizontalFields rssLine
      match rssFields.reverse with
      | "size" :: "set" :: "resident" :: "maximum" :: rssText :: _ =>
        match parseDecimal elapsedText, parseNatDecimal rssText with
        | some elapsed, some rss => .ok (elapsed, rss, timedOut)
        | none, _ => .error (.MalformedMeasurement caseName "elapsedSeconds" elapsedText)
        | _, none => .error (.MalformedMeasurement caseName "maximumResidentMemoryBytes" rssText)
      | _ => .error (.MeasurementUnavailable caseName "maximumResidentMemoryBytes")
    | _, _, .error failure => .error failure
    | _, _, _ =>
      if elapsedValues.length != 1 then .error (.MeasurementUnavailable caseName "elapsedSeconds")
      else .error (.MeasurementUnavailable caseName "maximumResidentMemoryBytes")

private def parseLinuxMeasurement (caseName : CaseName) (stderr : ByteArray) : Except JudgeFailure (Decimal × Nat × Bool) :=
  match String.fromUTF8? stderr with
  | none => .error (.MeasurementUnavailable caseName "measurementStream")
  | some text =>
    let lines := text.splitOn "\n"
    match onlyLineWithPrefix "__NECO_JUDGE_ELAPSED__=" lines, onlyLineWithPrefix "__NECO_JUDGE_RSS_KIB__=" lines,
        timeoutMarker caseName lines with
    | some elapsedText, some rssText, .ok timedOut =>
      match parseDecimal elapsedText, parseNatDecimal rssText with
      | some elapsed, some rss => .ok (elapsed, rss * 1024, timedOut)
      | none, _ => .error (.MalformedMeasurement caseName "elapsedSeconds" elapsedText)
      | _, none => .error (.MalformedMeasurement caseName "maximumResidentMemoryBytes" rssText)
    | _, _, .error failure => .error failure
    | none, _, _ => .error (.MeasurementUnavailable caseName "elapsedSeconds")
    | _, none, _ => .error (.MeasurementUnavailable caseName "maximumResidentMemoryBytes")

private def supervisorScript : String :=
  "child_stderr=$1; limit=$2; shift 2; ticks=$(awk \"BEGIN { value=$limit * 100; if (value < 1) value = 1; printf \\\"%d\\\", value }\"); \"$@\" 2>\"$child_stderr\" & child=$!; timed_out=0; while kill -0 \"$child\" 2>/dev/null && [ \"$ticks\" -gt 0 ]; do sleep 0.01; ticks=$((ticks - 1)); done; if kill -0 \"$child\" 2>/dev/null; then timed_out=1; kill -TERM \"$child\" 2>/dev/null; grace=10; while kill -0 \"$child\" 2>/dev/null && [ \"$grace\" -gt 0 ]; do sleep 0.01; grace=$((grace - 1)); done; if kill -0 \"$child\" 2>/dev/null; then kill -KILL \"$child\" 2>/dev/null; fi; fi; wait \"$child\"; status=$?; printf '__NECO_JUDGE_TIMED_OUT__=%s\\n' \"$timed_out\" >&2; exit \"$status\""

private def linuxMeasurementScript : String :=
  "child_stderr=$1; limit=$2; shift 2; start=$(date +%s%N); \"$@\" 2>\"$child_stderr\" & child=$!; maximum=0; ticks=$(awk \"BEGIN { value=$limit * 100; if (value < 1) value = 1; printf \\\"%d\\\", value }\"); timed_out=0; while kill -0 \"$child\" 2>/dev/null && [ \"$ticks\" -gt 0 ]; do value=$(awk '/VmHWM:/ { print $2 }' /proc/\"$child\"/status 2>/dev/null); case $value in ''|*[!0-9]*) ;; *) if [ \"$value\" -gt \"$maximum\" ]; then maximum=$value; fi ;; esac; sleep 0.01; ticks=$((ticks - 1)); done; if kill -0 \"$child\" 2>/dev/null; then timed_out=1; kill -TERM \"$child\" 2>/dev/null; sleep 0.1; if kill -0 \"$child\" 2>/dev/null; then kill -KILL \"$child\" 2>/dev/null; fi; fi; wait \"$child\"; status=$?; if [ \"$maximum\" -eq 0 ]; then maximum=1; fi; finish=$(date +%s%N); elapsed_ms=$(( (finish - start) / 1000000 )); printf '__NECO_JUDGE_ELAPSED__=%d.%03d\\n__NECO_JUDGE_RSS_KIB__=%s\\n__NECO_JUDGE_TIMED_OUT__=%s\\n' $((elapsed_ms / 1000)) $((elapsed_ms % 1000)) \"$maximum\" \"$timed_out\" >&2; exit \"$status\""

private def systemMeasurementRequest (request : MeasurementRequest) : System.ProcessRequest :=
  let arguments := [request.childStderrPath.toString, request.request.timeLimitSeconds.toString,
    request.request.executablePath.toString] ++ request.request.arguments
  if request.platform == "Darwin" then
    { command := "/usr/bin/time", arguments := ["-l", "/bin/sh", "-c", supervisorScript, "neco-judge-darwin"] ++ arguments,
      stdin := request.casePair.inputBytes }
  else
    { command := "/bin/sh", arguments := ["-c", linuxMeasurementScript, "neco-judge-linux"] ++ arguments,
      stdin := request.casePair.inputBytes }

private def defaultEnumerateCaseFiles (request : JudgeRequest) : IO (Except JudgeFailure ByteArray) := do
  let script := "for path do if [ -f \"$path\" ] && [ ! -L \"$path\" ]; then printf 'F\\0%s\\0' \"$path\"; else printf 'N\\0%s\\0' \"$path\"; fi; done"
  let processRequest : System.ProcessRequest :=
    { command := "/usr/bin/find"
      arguments := [request.testCaseDirectory.toString, "-mindepth", "1", "-maxdepth", "1", "-exec", "/bin/sh", "-c", script, "sh", "{}", "+"] }
  match ← System.run processRequest with
  | .ok output => return .ok output.stdout
  | .error failure => return .error (mapSystemFailure failure)

private def defaultReadBytes (path : System.FilePath) : IO (Except JudgeFailure ByteArray) := do
  match ← System.readBytes path with
  | .ok bytes => return .ok bytes
  | .error failure => return .error (mapSystemFailure failure)

private def defaultPlatformName (caseName : CaseName) : IO (Except JudgeFailure String) := do
  match ← System.run { command := "/usr/bin/uname", arguments := ["-s"] } with
  | .ok output =>
    match String.fromUTF8? output.stdout with
    | some text =>
      let name := String.ofList (text.toList.filter (fun character => character != '\n' && character != '\r'))
      if name == "Darwin" || name == "Linux" then return .ok name
      else return .error (.MeasurementUnavailable caseName "platform")
    | none => return .error (.MeasurementUnavailable caseName "platform")
  | .error failure => return .error (mapSystemFailure failure)

private def defaultRunMeasurement (request : MeasurementRequest) : IO (Except JudgeFailure System.ProcessOutput) := do
  match ← System.run (systemMeasurementRequest request) with
  | .ok output => return .ok output
  | .error (.nonZeroExit command exitCode stdout stderr) =>
    if command == "/usr/bin/time" || command == "/bin/sh" then
      return .ok { stdout, stderr, exitCode }
    else
      return .error (.ProcessStart command "unexpected process command")
  | .error failure => return .error (mapSystemFailure failure)

private def defaultWithTemporaryStderrFile
    (callback : System.FilePath -> IO (Except JudgeFailure MeasuredCase)) : IO (Except JudgeFailure MeasuredCase) := do
  try
    IO.FS.withTempFile (fun _ path => callback path)
  catch error =>
    return .error (.TemporaryStderrFile error.toString)

def defaultJudgeRuntime : JudgeRuntime :=
  { enumerateCaseFiles := defaultEnumerateCaseFiles
    readBytes := defaultReadBytes
    platformName := defaultPlatformName
    runMeasurement := defaultRunMeasurement
    withTemporaryStderrFile := defaultWithTemporaryStderrFile }

def withRuntimeDiscoverCasePairs (runtime : JudgeRuntime) (request : JudgeRequest) : IO (Except JudgeFailure CasePairs) := do
  match ← runtime.enumerateCaseFiles request with
  | .error failure => return .error failure
  | .ok stdout =>
    match collectCaseFiles stdout with
    | .error failure => return .error failure
    | .ok files => readCasePairs runtime request files

private def executeCase (runtime : JudgeRuntime) (request : JudgeRequest)
    (casePair : CasePair) : IO (Except JudgeFailure MeasuredCase) := do
  match ← runtime.platformName casePair.caseName with
  | .error failure => return .error failure
  | .ok platform =>
    if platform != "Darwin" && platform != "Linux" then
      return .error (.MeasurementUnavailable casePair.caseName "platform")
    runtime.withTemporaryStderrFile (fun childStderrPath => do
      let measurementRequest : MeasurementRequest := { platform, childStderrPath, casePair, request }
      match ← runtime.runMeasurement measurementRequest with
      | .error failure => return .error failure
      | .ok output =>
        match ← runtime.readBytes childStderrPath with
        | .error failure => return .error failure
        | .ok childStderr =>
          let measurement :=
            if platform == "Darwin" then parseDarwinMeasurement casePair.caseName output.stderr
            else parseLinuxMeasurement casePair.caseName output.stderr
          match measurement with
          | .error failure => return .error failure
          | .ok (elapsedSeconds, maximumResidentMemoryBytes, timedOut) =>
            return .ok
              { casePair, stdout := output.stdout, stderr := childStderr, exitCode := output.exitCode,
                elapsedSeconds, maximumResidentMemoryBytes, timeLimitSeconds := request.timeLimitSeconds, timedOut })

def withRuntimeExecuteMeasured (runtime : JudgeRuntime)
    (casePairs : CasePairs) : IO (Except JudgeFailure MeasuredProcess) := do
  let rec go (remaining : List CasePair) (measurements : List MeasuredCase) :
      IO (Except JudgeFailure (List MeasuredCase)) := do
    match remaining with
    | [] => return .ok measurements
    | casePair :: rest =>
      match ← executeCase runtime casePairs.request casePair with
      | .ok measurement => go rest (measurements ++ [measurement])
      | .error failure => return .error failure
  match ← go casePairs.pairs [] with
  | .ok measurements => return .ok { measurements }
  | .error failure => return .error failure

private def caseVerdict (measurement : MeasuredCase) : CaseVerdict :=
  if measurement.timedOut then
    .TimeLimitExceeded measurement
  else if measurement.exitCode != 0 then
    .RuntimeError measurement
  else if measurement.stdout != measurement.casePair.expectedOutput then
    .WrongAnswer measurement
  else
    .Accepted measurement

private def verdictRank (verdict : CaseVerdict) : Nat :=
  match verdict with
  | .TimeLimitExceeded _ => 0
  | .RuntimeError _ => 1
  | .WrongAnswer _ => 2
  | .Accepted _ => 3

private def verdictMeasurement (verdict : CaseVerdict) : MeasuredCase :=
  match verdict with
  | .TimeLimitExceeded measurement => measurement
  | .RuntimeError measurement => measurement
  | .WrongAnswer measurement => measurement
  | .Accepted measurement => measurement

def classifyVerdict (process : MeasuredProcess) : Except JudgeFailure JudgeReport :=
  match process.measurements with
  | [] => .error (.MeasurementUnavailable "" "measurements")
  | first :: rest =>
    let selected := rest.foldl (fun selected measurement =>
      let verdict := caseVerdict measurement
      let verdictCaseName := (verdictMeasurement verdict).casePair.caseName
      let selectedCaseName := (verdictMeasurement selected).casePair.caseName
      if verdictRank verdict < verdictRank selected ||
          (verdictRank verdict == verdictRank selected && verdictCaseName < selectedCaseName) then
        verdict
      else
        selected) (caseVerdict first)
    .ok { verdict := selected, selectedMeasurement := verdictMeasurement selected, measurements := process.measurements }

def withRuntimeJudge (runtime : JudgeRuntime) (request : JudgeRequest) : IO (Except JudgeFailure JudgeReport) := do
  match ← withRuntimeDiscoverCasePairs runtime request with
  | .error failure => return .error failure
  | .ok casePairs =>
    match ← withRuntimeExecuteMeasured runtime casePairs with
    | .error failure => return .error failure
    | .ok process => return classifyVerdict process

def discoverCasePairs (request : JudgeRequest) : IO (Except JudgeFailure CasePairs) :=
  withRuntimeDiscoverCasePairs defaultJudgeRuntime request

def executeMeasured (casePairs : CasePairs) : IO (Except JudgeFailure MeasuredProcess) :=
  withRuntimeExecuteMeasured defaultJudgeRuntime casePairs

def judge (request : JudgeRequest) : IO (Except JudgeFailure JudgeReport) :=
  withRuntimeJudge defaultJudgeRuntime request

end NecoLean.Judge
