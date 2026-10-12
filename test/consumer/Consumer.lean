import NecoLean

set_option autoImplicit false

private def publicSignatures : Unit :=
  let _ : NecoLean.Binary64.Decimal → Except NecoLean.Binary64.Failure UInt64 := NecoLean.Binary64.Decimal.toBits
  let _ : NecoLean.Binary64.Decimal → Except NecoLean.Binary64.Failure Float := NecoLean.Binary64.Decimal.toFloat
  let _ : NecoLean.System.FilePath → IO (Except NecoLean.System.Failure ByteArray) := NecoLean.System.readBytes
  let _ : NecoLean.System.FilePath → ByteArray → IO (Except NecoLean.System.Failure Unit) := NecoLean.System.writeBytes
  let _ : NecoLean.System.ProcessRequest → IO (Except NecoLean.System.Failure NecoLean.System.ProcessOutput) := NecoLean.System.run
  let _ : Nat → Nat → Except NecoLean.Diagnostic.Failure NecoLean.Diagnostic.Span := NecoLean.Diagnostic.Span.create
  let _ : String → NecoLean.Diagnostic.Span → NecoLean.Diagnostic.Severity → String → NecoLean.Diagnostic.Message := fun path span severity text => { path, span, severity, text }
  let _ : NecoLean.Cli.Schema Unit → List String → Except NecoLean.Cli.Failure Unit := NecoLean.Cli.decode
  let _ : ByteArray → Except NecoLean.Json.Failure NecoLean.Json.Value := NecoLean.Json.decode
  let _ : ByteArray → NecoLean.Digest.Sha256 := NecoLean.Digest.sha256
  let _ : NecoLean.Llvm.Module → Except NecoLean.Llvm.Failure NecoLean.Llvm.ValidModule := NecoLean.Llvm.validate
  let _ : NecoLean.Llvm.ValidModule → ByteArray := NecoLean.Llvm.encode
  let _ : NecoLean.Llvm.CompileRequest → IO (Except NecoLean.Llvm.Failure NecoLean.Llvm.CompileOutput) := NecoLean.Llvm.compile
  let _ : NecoLean.Json.Value → Except NecoLean.Json.Failure String := NecoLean.Json.encodeText
  let _ : NecoLean.Json.Value → Except NecoLean.Json.Failure ByteArray := NecoLean.Json.encode
  let _ : NecoLean.Fixpoint.ClosureInput → Except NecoLean.Fixpoint.ClosureFailure NecoLean.Fixpoint.ClosureResult := NecoLean.Fixpoint.computeClosure
  let _ : String → NecoLean.System.FilePath → NecoLean.Judge.CasePair → NecoLean.Judge.JudgeRequest → NecoLean.Judge.MeasurementRequest := fun platform childStderrPath casePair request => { platform, childStderrPath, casePair, request }
  let _ : NecoLean.Judge.JudgeRuntime := NecoLean.Judge.defaultJudgeRuntime
  let _ : NecoLean.Judge.JudgeRuntime → NecoLean.Judge.JudgeRequest → IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.CasePairs) := NecoLean.Judge.withRuntimeDiscoverCasePairs
  let _ : NecoLean.Judge.JudgeRuntime → NecoLean.Judge.CasePairs → IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.MeasuredProcess) := NecoLean.Judge.withRuntimeExecuteMeasured
  let _ : NecoLean.Judge.JudgeRuntime → NecoLean.Judge.JudgeRequest → IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.JudgeReport) := NecoLean.Judge.withRuntimeJudge
  let _ : NecoLean.Judge.JudgeRequest → IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.CasePairs) := NecoLean.Judge.discoverCasePairs
  let _ : NecoLean.Judge.CasePairs → IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.MeasuredProcess) := NecoLean.Judge.executeMeasured
  let _ : NecoLean.Judge.MeasuredProcess → Except NecoLean.Judge.JudgeFailure NecoLean.Judge.JudgeReport := NecoLean.Judge.classifyVerdict
  let _ : NecoLean.Judge.JudgeRequest → IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.JudgeReport) := NecoLean.Judge.judge
  let _ : ByteArray → NecoLean.Scanner := NecoLean.Scanner.create
  let _ : NecoLean.Scanner → Except NecoLean.Scanner.Failure (String × NecoLean.Scanner) := NecoLean.Scanner.scanToken
  let _ : NecoLean.Scanner → Except NecoLean.Scanner.Failure (Int × NecoLean.Scanner) := NecoLean.Scanner.scanInt
  let _ : NecoLean.Scanner → Except NecoLean.Scanner.Failure (Int × NecoLean.Scanner) := NecoLean.Scanner.scanSignedInt
  let _ : NecoLean.Scanner → Except NecoLean.Scanner.Failure (String × NecoLean.Scanner) := NecoLean.Scanner.scanLine
  let _ : NecoLean.Printer := NecoLean.Printer.empty
  let _ : NecoLean.Printer → ByteArray → NecoLean.Printer := NecoLean.Printer.append
  let _ : NecoLean.Printer → ByteArray := NecoLean.Printer.finish
  let _ : NecoLean.System.FilePath → NecoLean.Printer → IO (Except NecoLean.System.Failure ByteArray) := NecoLean.Printer.writeTo
  let _ : NecoLean.Llvm.ValueType → Nat → NecoLean.Llvm.ValueType := NecoLean.Llvm.ValueType.array
  let _ : List NecoLean.Llvm.Block → List NecoLean.Llvm.Block := NecoLean.Llvm.blocksReachableFromEntry
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.ValueType → List (String × NecoLean.Llvm.Operand) → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.phi
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → Nat → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.zext
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → Nat → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.sext
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → Nat → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.trunc
  let _ : NecoLean.Llvm.ResultId → Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.bitAnd
  let _ : NecoLean.Llvm.ResultId → Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.bitOr
  let _ : NecoLean.Llvm.ResultId → Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.bitXor
  let _ : NecoLean.Llvm.ResultId → Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.shl
  let _ : NecoLean.Llvm.ResultId → Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.lshr
  let _ : NecoLean.Llvm.ResultId → Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.ashr
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → NecoLean.Llvm.ValueType → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.bitcast
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → List NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.getElementPtr
  let _ : NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction := NecoLean.Llvm.Instruction.icmpPtrEq
  let _ : String → NecoLean.Llvm.RuntimeSourceKind → ByteArray → Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource := NecoLean.Llvm.RuntimeSource.create
  let _ : NecoLean.Llvm.Operand → String → List (NecoLean.Llvm.Operand × String) → NecoLean.Llvm.Terminator := NecoLean.Llvm.Terminator.switch
  let _ : NecoLean.Llvm.ObjectCompileRequest → IO (Except NecoLean.Llvm.ObjectCompileFailure NecoLean.Llvm.ObjectCompileOutput) := NecoLean.Llvm.compileObjects
  let _ : NecoLean.Llvm.ObjectModuleOptimization := .none
  let _ : NecoLean.Llvm.ObjectModuleOptimization := .o1
  let _ : List NecoLean.Llvm.RuntimeSource → List NecoLean.Llvm.RuntimeUnitOptimization → Except NecoLean.Llvm.Failure Unit := NecoLean.Llvm.validateRuntimeUnitOptimizations
  let _ : NecoLean.Llvm.RuntimeUnitOptimization := { runtimeSourceIndex := 1, logicalName := "runtime.c", inputDigest := "digest", optimization := .o2 }
  let _ : NecoLean.Llvm.CompiledObjectArtifact → NecoLean.Llvm.ObjectLinkInput := NecoLean.Llvm.CompiledObjectArtifact.linkInput
  let _ : NecoLean.Llvm.LinkOutputIdentity → String := NecoLean.Llvm.LinkOutputIdentity.recomputeDigest
  let _ : NecoLean.Llvm.ObjectLinkRequest → IO NecoLean.Llvm.ObjectLinkResult := NecoLean.Llvm.linkObjects
  let _ : NecoLean.Llvm.OwnedLinkedOutput → IO NecoLean.Llvm.LinkPublicationResult := NecoLean.Llvm.publishLinkedOutput
  let _ : NecoLean.Llvm.OwnedLinkedOutput → IO NecoLean.Llvm.LinkCleanupResult := NecoLean.Llvm.releaseLinkedOutput
  let _ : NecoLean.Llvm.LinkStagingOwnership → IO NecoLean.Llvm.LinkCleanupResult := NecoLean.Llvm.releaseLinkStaging
  let _ : Option NecoLean.Llvm.ResultId → NecoLean.Llvm.Operand → List NecoLean.Llvm.Operand → NecoLean.Llvm.Terminator := NecoLean.Llvm.Terminator.mustTailCall
  let _ : ByteArray → Except NecoLean.Kdl.DocumentFailure NecoLean.Kdl.ParseResult := NecoLean.Kdl.parse
  let _ : NecoLean.Kdl.Document → Except NecoLean.Kdl.EncodingFailure String := NecoLean.Kdl.encode
  let _ : String → Except NecoLean.Kdl.Ast.PathFailure NecoLean.Kdl.Ast.NamespacePath := NecoLean.Kdl.Ast.NamespacePath.parse
  let _ : String → NecoLean.Tui.InputRemainder → NecoLean.Tui.DecodedChunk := NecoLean.Tui.decodeChunk
  let _ : NecoLean.Tui.Rect → NecoLean.Tui.DetailPlacement → Int → Int → NecoLean.Tui.Rect × NecoLean.Tui.Rect := NecoLean.Tui.layout
  let _ : Int → List NecoLean.Tui.Constraint → Except NecoLean.Tui.GeometryFailure (List Int) := NecoLean.Tui.resolveSizes
  let _ : Int → NecoLean.Tui.LogicalLine → List NecoLean.Tui.DrawingLine := NecoLean.Tui.layoutLogicalLine
  let _ : NecoLean.Tui.Surface → NecoLean.Tui.Position → Int → NecoLean.Tui.DrawingLine → NecoLean.Tui.Surface := NecoLean.Tui.writeDrawingLine
  let _ : NecoLean.Tui.Tree → List NecoLean.Tui.TreeRow := NecoLean.Tui.flatten
  let _ : NecoLean.Tui.Surface → NecoLean.Tui.OverlayState → List NecoLean.Tui.OverlaySurface → NecoLean.Tui.Surface := NecoLean.Tui.compose
  let _ : NecoLean.Tui.ViewportState → Int → List NecoLean.Tui.ViewportItem → Except NecoLean.Tui.ViewportFailure NecoLean.Tui.ViewportObservation := NecoLean.Tui.observe
  let _ : NecoLean.Tui.Tree → Except NecoLean.Tui.TuiFailure NecoLean.Tui.Model := NecoLean.Tui.initializeModel
  let _ : NecoLean.Tui.Model → NecoLean.Tui.Rect → NecoLean.Tui.Surface := NecoLean.Tui.renderFrame
  let _ : NecoLean.Tui.InputEvent → NecoLean.Tui.Model → Except NecoLean.Tui.TuiFailure NecoLean.Tui.Model := NecoLean.Tui.update
  let _ : NecoLean.Tui.TerminalBackend Bool → NecoLean.Tui.Model → IO (Except NecoLean.Tui.TuiFailure Unit) := NecoLean.Tui.runModelWithBackend
  let _ : Int → Int := NecoLean.Tui.Posix.clampDeciseconds
  let _ : String → Except NecoLean.Tui.TerminalFailure NecoLean.Tui.TerminalSize := NecoLean.Tui.Posix.parseTtySize
  let _ : Int → String := NecoLean.Tui.Posix.sttyCommand
  let _ : NecoLean.Tui.TerminalBackend NecoLean.Tui.PosixTerminalState := NecoLean.Tui.Posix.backend
  let _ : NecoLean.Tui.Model → IO (Except NecoLean.Tui.TuiFailure Unit) := NecoLean.Tui.Posix.runModel
  ()

def main : IO UInt32 := do
  let document := "{\"items\":[1,true,null],\"name\":\"neco\"}".toUTF8
  match NecoLean.Json.decode document with
  | .error failure =>
    IO.eprintln s!"decode failed: {reprStr failure}"
    return 1
  | .ok value =>
    match NecoLean.Json.encode value with
    | .error failure =>
      IO.eprintln s!"encode failed: {reprStr failure}"
      return 1
    | .ok encoded =>
      match NecoLean.Json.decode encoded with
      | .ok restored =>
        if restored == value then return 0
        IO.eprintln "decoded value changed after encoding"
        return 1
      | .error failure =>
        IO.eprintln s!"decode of encoded value failed: {reprStr failure}"
        return 1
