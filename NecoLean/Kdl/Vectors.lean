import NecoLean.Kdl

set_option autoImplicit false

namespace NecoLean.Kdl.Vectors

structure ManifestEntry where
  sha256 : String
  relativePath : String
  deriving Repr, BEq, DecidableEq

inductive Expectation where
  | parses (expectedRelativePath : String)
  | rejects
  deriving Repr, BEq, DecidableEq

inductive CaseResult where
  | matched
  | unexpectedSuccess
  | unexpectedFailure (failure : DocumentFailure)
  | normalizationFailure (failure : EncodingFailure)
  | outputMismatch (actual : String) (expected : String)
  | missingManifestEntry (relativePath : String)
  | missingExpectedOutput (relativePath : String)
  | invalidExpectedUtf8 (relativePath : String)
  deriving Repr, BEq

structure CaseEvidence where
  name : String
  inputRelativePath : String
  expectation : Expectation
  result : CaseResult
  deriving Repr, BEq

structure AggregateEvidence where
  manifestEntries : Nat
  inputCases : Nat
  expectedOutputs : Nat
  matchedParse : Nat
  matchedReject : Nat
  mismatches : Nat
  manifestCovered : Bool
  allMatched : Bool
  deriving Repr, BEq, DecidableEq

structure CorpusEvidence where
  manifest : List ManifestEntry
  cases : List CaseEvidence
  aggregate : AggregateEvidence
  deriving Repr, BEq

inductive InspectionFailure where
  | invalidManifestLine (lineNumber : Nat) (line : String)
  | ioFailure (path : String) (message : String)
  deriving Repr, BEq, DecidableEq

private def parseManifestLine (lineNumber : Nat) (line : String) : Except InspectionFailure ManifestEntry :=
  let characters := line.toList
  let digest := String.ofList (characters.take 64)
  let separator := characters.drop 64 |>.take 2
  let relativePath := String.ofList (characters.drop 66)
  if digest.length == 64 && digest.toList.all Char.isHexDigit && separator == [' ', ' '] &&
      !relativePath.isEmpty then
    .ok { sha256 := digest, relativePath := relativePath }
  else .error (.invalidManifestLine lineNumber line)

private def parseManifestLines (lines : List String) : Except InspectionFailure (List ManifestEntry) :=
  let rec loop (remaining : List String) (lineNumber : Nat) (entries : List ManifestEntry) :=
    match remaining with
    | [] => .ok entries.reverse
    | line :: rest =>
      if line.isEmpty then loop rest (lineNumber + 1) entries
      else do
        let entry ← parseManifestLine lineNumber line
        loop rest (lineNumber + 1) (entry :: entries)
  loop lines 1 []

def parseManifest (text : String) : Except InspectionFailure (List ManifestEntry) :=
  parseManifestLines (text.splitOn "\n")

private def manifestContains (manifest : List ManifestEntry) (relativePath : String) : Bool :=
  manifest.any fun entry => entry.relativePath == relativePath

private def kdlFiles (directory : System.FilePath) : IO (List IO.FS.DirEntry) := do
  let entries ← System.FilePath.readDir directory
  return entries.toList
    |>.filter (fun entry => entry.path.extension == some "kdl")
    |>.mergeSort (fun left right => decide (left.fileName ≤ right.fileName))

private def inspectCase (corpusRoot : System.FilePath) (manifest : List ManifestEntry)
    (inputEntry : IO.FS.DirEntry) : IO CaseEvidence := do
  let name := inputEntry.path.fileStem.getD inputEntry.fileName
  let inputRelativePath := "input/" ++ inputEntry.fileName
  let rejects := name.endsWith "_fail"
  let expectation := if rejects then Expectation.rejects else Expectation.parses ("expected_kdl/" ++ inputEntry.fileName)
  let manifestHasInput := manifestContains manifest inputRelativePath
  if !manifestHasInput then
    return { name, inputRelativePath, expectation, result := .missingManifestEntry inputRelativePath }
  let bytes ← IO.FS.readBinFile inputEntry.path
  match expectation with
  | .rejects =>
    match NecoLean.Kdl.parse bytes with
    | .error _ => return { name, inputRelativePath, expectation, result := .matched }
    | .ok _ => return { name, inputRelativePath, expectation, result := .unexpectedSuccess }
  | .parses expectedRelativePath =>
    if !manifestContains manifest expectedRelativePath then
      return { name, inputRelativePath, expectation, result := .missingManifestEntry expectedRelativePath }
    let expectedPath := corpusRoot / expectedRelativePath
    if !(← expectedPath.pathExists) then
      return { name, inputRelativePath, expectation, result := .missingExpectedOutput expectedRelativePath }
    let expectedBytes ← IO.FS.readBinFile expectedPath
    match String.fromUTF8? expectedBytes with
    | none => return { name, inputRelativePath, expectation, result := .invalidExpectedUtf8 expectedRelativePath }
    | some expected =>
      match NecoLean.Kdl.parse bytes with
      | .error failure => return { name, inputRelativePath, expectation, result := .unexpectedFailure failure }
      | .ok parsed =>
        match NecoLean.Kdl.normalize parsed.plain with
        | .error failure => return { name, inputRelativePath, expectation, result := .normalizationFailure failure }
        | .ok actual =>
          if actual == expected then
            return { name, inputRelativePath, expectation, result := .matched }
          else
            return { name, inputRelativePath, expectation, result := .outputMismatch actual expected }

private def aggregateEvidence (manifest : List ManifestEntry) (cases : List CaseEvidence) : AggregateEvidence :=
  let expectedOutputs := cases.countP fun evidence => match evidence.expectation with
    | .parses _ => true
    | .rejects => false
  let matchedParse := cases.countP fun evidence => match evidence.expectation, evidence.result with
    | .parses _, .matched => true
    | _, _ => false
  let matchedReject := cases.countP fun evidence => match evidence.expectation, evidence.result with
    | .rejects, .matched => true
    | _, _ => false
  let mismatches := cases.length - matchedParse - matchedReject
  let manifestCovered := cases.all fun evidence => match evidence.result with
    | .missingManifestEntry _ => false
    | _ => true
  {
    manifestEntries := manifest.length
    inputCases := cases.length
    expectedOutputs
    matchedParse
    matchedReject
    mismatches
    manifestCovered
    allMatched := mismatches == 0 && manifestCovered
  }

def inspectCorpus (corpusRoot : System.FilePath) : IO (Except InspectionFailure CorpusEvidence) := do
  try
    let manifestPath := corpusRoot / "manifest.sha256"
    let manifestText ← IO.FS.readFile manifestPath
    let manifest ← match parseManifest manifestText with
      | .ok entries => pure entries
      | .error failure => return .error failure
    let inputs ← kdlFiles (corpusRoot / "input")
    let cases ← inputs.mapM (inspectCase corpusRoot manifest)
    let aggregate := aggregateEvidence manifest cases
    return .ok { manifest, cases, aggregate }
  catch error =>
    return .error (.ioFailure corpusRoot.toString error.toString)

end NecoLean.Kdl.Vectors
