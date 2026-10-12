import NecoLean
import NecoLean.Kdl.Vectors
import NecoLean.Test.SharedVectors
import Lean

set_option autoImplicit false

private def report (name : String) (passed : Bool) (detail : String) : IO Bool := do
  if passed then
    IO.println s!"ok: {name}"
    return true
  IO.eprintln s!"failed: {name}: {detail}"
  return false

private def digestCheck : IO Bool := do
  let results ← NecoLean.Test.SharedVectors.digestVectors.mapM (fun (name, bytes, expected) =>
    report name (NecoLean.Digest.toHex (NecoLean.Digest.sha256 bytes) == expected) "digest mismatch")
  return results.all id

private partial def jsonEquivalent : NecoLean.Json.Value → NecoLean.Json.Value → Bool
  | .null, .null => true
  | .bool left, .bool right => left == right
  | .number left, .number right => left == right
  | .string left, .string right => left == right
  | .array left, .array right => left.length == right.length && (left.zip right).all (fun (left, right) => jsonEquivalent left right)
  | .object left, .object right =>
    left.length == right.length && left.all (fun (key, value) =>
      match right.find? (fun field => field.1 == key) with
      | some (_, other) => jsonEquivalent value other
      | none => false)
  | _, _ => false

private def jsonRoundtripPasses (text : String) (expected : NecoLean.Json.Value) : Bool :=
  match NecoLean.Json.decode text.toUTF8 with
  | .error _ => false
  | .ok decoded =>
    jsonEquivalent decoded expected &&
      match NecoLean.Json.encode decoded with
      | .error _ => false
      | .ok encoded =>
        match NecoLean.Json.decode encoded with
        | .error _ => false
        | .ok roundtrip => jsonEquivalent roundtrip expected

private def jsonRepeated (count : Nat) (text : String) : String :=
  String.join (List.replicate count text)

private def jsonNestedInput (opener closer : String) (depth : Nat) (innermost : Option String) (emptyCollection : String) : String :=
  match innermost with
  | none => jsonRepeated (depth - 1) opener ++ emptyCollection ++ jsonRepeated (depth - 1) closer
  | some value => jsonRepeated depth opener ++ value ++ jsonRepeated depth closer

private def jsonDepthResults : List (String × Bool) :=
  let kinds : List (String × String × String × String × Nat) :=
    [("array", "[", "]", "[]", 128), ("object", "{\"a\":", "}", "{}", 640)]
  let innermosts : List (String × Option String) :=
    [("empty", none), ("zero", some "0"), ("string", some "\"s\""), ("true", some "true"), ("null", some "null")]
  kinds.flatMap (fun (kind, opener, closer, emptyCollection, limitOffset) =>
    innermosts.flatMap (fun (innermostName, innermost) =>
      [ (s!"depth-{kind}-{innermostName}-128-accepted",
          match NecoLean.Json.decode (jsonNestedInput opener closer 128 innermost emptyCollection).toUTF8 with
          | .ok _ => true
          | _ => false),
        (s!"depth-{kind}-{innermostName}-129-rejected",
          match NecoLean.Json.decode (jsonNestedInput opener closer 129 innermost emptyCollection).toUTF8 with
          | .error (.invalid offset "nesting limit") => offset == limitOffset
          | _ => false) ]))

private def jsonFailureOrderResults : List (String × Bool) :=
  [ ("order-syntax-failure-before-depth",
      match NecoLean.Json.decode ("[1 2" ++ jsonRepeated 130 "[").toUTF8 with
      | .error (.invalid 3 "expected comma or closing array") => true
      | _ => false),
    ("order-depth-128-unterminated",
      match NecoLean.Json.decode (jsonRepeated 128 "[").toUTF8 with
      | .error (.unexpectedEnd 128) => true
      | _ => false),
    ("order-unexpected-byte-before-depth",
      match NecoLean.Json.decode ("x" ++ jsonRepeated 129 "[").toUTF8 with
      | .error (.invalid 0 "unexpected byte") => true
      | _ => false),
    ("order-invalid-utf8-before-depth",
      match NecoLean.Json.decode ((jsonRepeated 129 "[").toUTF8 ++ ByteArray.mk #[0xFF]) with
      | .error (.invalidUtf8 129) => true
      | _ => false),
    ("order-depth-after-duplicate-key-prefix",
      match NecoLean.Json.decode ("{\"a\":1,\"a\":" ++ jsonRepeated 128 "[").toUTF8 with
      | .error (.invalid 138 "nesting limit") => true
      | _ => false) ]

private def jsonCheck : IO Bool := do
  let sharedResults ← NecoLean.Test.SharedVectors.jsonVectors.mapM (fun vector =>
    let decoded := NecoLean.Json.decode (match vector.input with
      | .json text => text.toUTF8
      | .hex bytes => bytes)
    let passed := match vector.expected, decoded with
      | .ok expected, .ok value =>
        match NecoLean.Json.encode value with
        | .ok encoded => String.fromUTF8! encoded == expected
        | .error _ => false
      | .error tag, .error failure =>
        match tag with
        | "invalid" => match failure with | .invalid _ _ => true | _ => false
        | "invalid-utf8" => match failure with | .invalidUtf8 _ => true | _ => false
        | "unexpected-end" => match failure with | .unexpectedEnd _ => true | _ => false
        | "trailing" => match failure with | .trailing _ => true | _ => false
        | "duplicate-key" => match failure with | .duplicateKey _ _ => true | _ => false
        | _ => false
      | _, _ => false
    report s!"shared-json-{vector.name}" passed "json mismatch")
  let number := match NecoLean.Json.Number.create "1E+05" with | .ok value => value | .error _ => NecoLean.Json.Number.zero
  let semanticValue := NecoLean.Json.Value.object [("z", .array [.number number, .object [("b", .bool true), ("a", .string "x")]]), ("a", .null)]
  let reorderedValue := NecoLean.Json.Value.object [("a", .null), ("z", .array [.number number, .object [("a", .string "x"), ("b", .bool true)]])]
  let duplicateValue := NecoLean.Json.Value.object [("same", .null), ("same", .bool true)]
  let wideArray := "[" ++ String.intercalate "," ((List.range 4096).map toString) ++ "]"
  let wideObject := "{" ++ String.intercalate "," ((List.range 512).map (fun index => s!"\"field{index}\":{index}")) ++ "}"
  let wideArrayValue := (List.range 4096).mapM (fun index =>
    match NecoLean.Json.Number.create (toString index) with
    | .ok value => some (.number value)
    | .error _ => none)
  let wideObjectValue := (List.range 512).mapM (fun index =>
    match NecoLean.Json.Number.create (toString index) with
    | .ok value => some (s!"field{index}", .number value)
    | .error _ => none)
  let shallowArray := "[0]"
  let shallowObject := "{\"field\":0}"
  let wideArrayPass :=
    match wideArrayValue with
    | none => false
    | some values => jsonRoundtripPasses wideArray (.array values)
  let wideObjectPass :=
    match wideObjectValue with
    | none => false
    | some fields => jsonRoundtripPasses wideObject (.object fields)
  let nestedWide (inner : NecoLean.Json.Value) : NecoLean.Json.Value :=
    (List.range 127).foldl (fun value _ => .array [value]) inner
  let nestedWideArrayPass :=
    match wideArrayValue with
    | none => false
    | some values => jsonRoundtripPasses (jsonRepeated 127 "[" ++ wideArray ++ jsonRepeated 127 "]") (nestedWide (.array values))
  let nestedWideObjectPass :=
    match wideObjectValue with
    | none => false
    | some fields => jsonRoundtripPasses (jsonRepeated 127 "[" ++ wideObject ++ jsonRepeated 127 "]") (nestedWide (.object fields))
  let extraResults :=
    [ ("surrogate-pair", match NecoLean.Json.decode "\"\\ud83d\\ude00\"".toUTF8 with | .ok (.string value) => value == "😀" | _ => false),
      ("surrogate-high-rejected", match NecoLean.Json.decode "\"\\ud800\"".toUTF8 with | .error (.invalid _ _) => true | _ => false),
      ("surrogate-low-rejected", match NecoLean.Json.decode "\"\\udc00\"".toUTF8 with | .error (.invalid _ _) => true | _ => false),
      ("surrogate-mismatched-rejected", match NecoLean.Json.decode "\"\\ud800\\u0041\"".toUTF8 with | .error (.invalid _ _) => true | _ => false),
      ("encode-duplicate-key", match NecoLean.Json.encode duplicateValue with | .error (.duplicateKey _ "same") => true | _ => false),
      ("semantic-roundtrip", match NecoLean.Json.encode semanticValue with | .ok bytes => (match NecoLean.Json.decode bytes with | .ok decoded => jsonEquivalent decoded reorderedValue | .error _ => false) | .error _ => false),
      ("number-token-preserved", match NecoLean.Json.encode semanticValue with | .ok bytes => String.fromUTF8! bytes |>.contains "1E+05" | _ => false),
      ("recursive-canonicalize", match NecoLean.Json.encode semanticValue with | .ok bytes => String.fromUTF8! bytes == "{\"a\":null,\"z\":[1E+05,{\"a\":\"x\",\"b\":true}]}" | _ => false),
      ("non-bmp-key-order", match NecoLean.Json.decode "{\"𐀀\":2,\"\":1}".toUTF8 with | .ok value => (match NecoLean.Json.encode value with | .ok bytes => String.fromUTF8! bytes == "{\"\":1,\"𐀀\":2}" | .error _ => false) | .error _ => false),
      ("invalid-encode-result", match NecoLean.Json.encode duplicateValue with | .error (.duplicateKey _ "same") => true | _ => false),
      ("wide-array-roundtrip", wideArrayPass),
      ("wide-object-roundtrip", wideObjectPass),
      ("nested-wide-array-roundtrip", nestedWideArrayPass),
      ("nested-wide-object-roundtrip", nestedWideObjectPass),
      ("shallow-array-accepted", match NecoLean.Json.decode shallowArray.toUTF8 with | .ok (.array [.number value]) => NecoLean.Json.Number.toString value == "0" | _ => false),
      ("shallow-object-accepted", match NecoLean.Json.decode shallowObject.toUTF8 with | .ok (.object [("field", .number value)]) => NecoLean.Json.Number.toString value == "0" | _ => false),
      ("failure-unterminated-string", match NecoLean.Json.decode "\"abc".toUTF8 with | .error (.unexpectedEnd 4) => true | _ => false),
      ("failure-trailing-escape", match NecoLean.Json.decode "\"a\\".toUTF8 with | .error (.unexpectedEnd 3) => true | _ => false),
      ("failure-invalid-escape", match NecoLean.Json.decode "\"a\\q\"".toUTF8 with | .error (.invalid 2 "invalid escape") => true | _ => false),
      ("failure-short-unicode-escape", match NecoLean.Json.decode "\"\\u12\"".toUTF8 with | .error (.invalid 3 "invalid unicode escape") => true | _ => false),
      ("failure-truncated-low-surrogate", match NecoLean.Json.decode "\"\\ud800\\udc0\"".toUTF8 with | .error (.invalid 3 "invalid surrogate pair") => true | _ => false),
      ("failure-control-character", match NecoLean.Json.decode "\"a\nb\"".toUTF8 with | .error (.invalid 2 "control character in string") => true | _ => false),
      ("failure-fraction-without-digits", match NecoLean.Json.decode "[1.]".toUTF8 with | .error (.invalid 2 "invalid number") => true | _ => false),
      ("failure-exponent-without-digits", match NecoLean.Json.decode "[1e+]".toUTF8 with | .error (.invalid 2 "invalid number") => true | _ => false),
      ("failure-number-trailing", match NecoLean.Json.decode "123abc".toUTF8 with | .error (.trailing 3) => true | _ => false),
      ("failure-duplicate-key-offset", match NecoLean.Json.decode "{\"a\":1,\"a\":2}".toUTF8 with | .error (.duplicateKey 7 "a") => true | _ => false),
      ("failure-invalid-utf8-truncated-tail", match NecoLean.Json.decode (ByteArray.mk #[34, 0xE2, 0x82]) with | .error (.invalidUtf8 1) => true | _ => false),
      ("string-escapes-decoded", match NecoLean.Json.decode "\"\\n\\t\\/\\b\\f\\r\\\\\\\"é€😀\"".toUTF8 with | .ok (.string value) => value == "\n\t/\x08\x0c\r\\\"é€😀" | _ => false),
      ("representative-unclosed-array", match NecoLean.Json.decode "[".toUTF8 with | .error (.unexpectedEnd 1) => true | _ => false),
      ("representative-array-trailing-comma", match NecoLean.Json.decode "[1,".toUTF8 with | .error (.unexpectedEnd 3) => true | _ => false),
      ("representative-nested-unclosed-array", match NecoLean.Json.decode "[[1".toUTF8 with | .error (.invalid 3 "expected comma or closing array") => true | _ => false),
      ("representative-unclosed-object", match NecoLean.Json.decode "{".toUTF8 with | .error (.unexpectedEnd 1) => true | _ => false),
      ("representative-array-missing-comma", match NecoLean.Json.decode "[1 2]".toUTF8 with | .error (.invalid 3 "expected comma or closing array") => true | _ => false),
      ("representative-object-missing-colon", match NecoLean.Json.decode "{\"a\" 1}".toUTF8 with | .error (.invalid 5 "expected colon") => true | _ => false),
      ("representative-object-missing-comma", match NecoLean.Json.decode "{\"a\":1 2}".toUTF8 with | .error (.invalid 7 "expected comma or closing object") => true | _ => false),
      ("representative-object-duplicate-key", match NecoLean.Json.decode "{\"a\":1,\"a\":2}".toUTF8 with | .error (.duplicateKey 7 "a") => true | _ => false) ] ++ jsonDepthResults ++ jsonFailureOrderResults
  let directResults ← extraResults.mapM (fun (name, passed) => report s!"json-{name}" passed "json parity mismatch")
  return sharedResults.all id && directResults.all id

private def diagnosticCheck : IO Bool := do
  let zero := NecoLean.Diagnostic.Span.create 0 0
  let point := NecoLean.Diagnostic.Span.create 2 2
  let range := NecoLean.Diagnostic.Span.create 2 5
  let reversed := NecoLean.Diagnostic.Span.create 5 2
  let descending := NecoLean.Diagnostic.Span.create 1 0
  let passed :=
    (match zero with
    | .ok span => NecoLean.Diagnostic.Span.startByte span == 0 && NecoLean.Diagnostic.Span.endByte span == 0
    | _ => false) &&
    (match point with
    | .ok span => NecoLean.Diagnostic.Span.startByte span == 2 && NecoLean.Diagnostic.Span.endByte span == 2
    | _ => false) &&
    (match range with
    | .ok span => NecoLean.Diagnostic.Span.startByte span == 2 && NecoLean.Diagnostic.Span.endByte span == 5
    | _ => false) &&
    (match reversed with
    | .error (.invalidSpan 5 2) => true
    | _ => false) &&
    (match descending with
    | .error (.invalidSpan 1 0) => true
    | _ => false)
  report "diagnostic" passed "span validation mismatch"

private def systemFilesystemCheck : IO Bool := do
  let path : NecoLean.System.FilePath := ".lake/neco-lean-system-test.bin"
  let bytes := [0, 255, 65].toByteArray
  let writeResult ← NecoLean.System.writeBytes path bytes
  let readResult ← NecoLean.System.readBytes path
  let missing ← NecoLean.System.readBytes ".lake/neco-lean-missing.bin"
  let passed := (match writeResult with | .ok () => true | _ => false) && (match readResult with | .ok actual => actual.toList == bytes.toList | _ => false) && match missing with | .error (.file _ _) => true | _ => false
  report "system-filesystem" passed "filesystem result mismatch"

private def systemProcessCheck : IO Bool := do
  let bytes := [0, 255, 65].toByteArray
  let success ← NecoLean.System.run { command := "cat", stdin := bytes }
  let failure ← NecoLean.System.run { command := "sh", arguments := ["-c", "printf err >&2; exit 7"] }
  let eof ← NecoLean.System.run { command := "sh", arguments := ["-c", "cat >/dev/null; printf eof"] }
  let pressureInput := (List.replicate 262144 65).toByteArray
  let pressure ← NecoLean.System.run { command := "sh", arguments := ["-c", "cat; dd if=/dev/zero bs=65536 count=4 2>/dev/null"], stdin := pressureInput }
  let missing ← NecoLean.System.run { command := "neco-lean-command-does-not-exist" }
  let passed := match success, failure, eof, pressure, missing with
    | .ok output, .error (.nonZeroExit _ code _ stderr), .ok eofOutput, .ok pressureOutput, .error (.processStart _ _) =>
      output.stdout.toList == bytes.toList && output.stderr.isEmpty && output.exitCode == 0 &&
        code == 7 && stderr.toList == "err".toUTF8.toList && eofOutput.stdout == "eof".toUTF8 &&
        pressureOutput.stdout.size == 524288
    | _, _, _, _, _ => false
  report "system-process" passed "process result mismatch"

private def cliCheck : IO Bool := do
  let schema : NecoLean.Cli.Schema (String × List String) :=
    { commands := [{ name := "build", options := [{ name := "--output", kind := .required }], positional := 1 }, { name := "check", positional := 1 }]
      decodeCommand := fun result => .ok (result.command, result.positionals) }
  let first := NecoLean.Cli.decode schema ["build", "--output", "app", "input.gleam"]
  let second := NecoLean.Cli.decode schema ["build", "input.gleam", "--output", "app"]
  let unknown := NecoLean.Cli.decode schema ["run", "input"]
  let unknownFlag := NecoLean.Cli.decode schema ["build", "--unknown", "input"]
  let extra := NecoLean.Cli.decode schema ["check", "first", "second"]
  let missing := NecoLean.Cli.decode schema ["build", "--output"]
  let missingOption := NecoLean.Cli.decode schema ["build", "--output", "--other"]
  let passed := (match first, second with | .ok left, .ok right => left.1 == right.1 && left.2 == right.2 | _, _ => false) && match unknown, unknownFlag, extra, missing, missingOption with | .error (.unknownCommand "run"), .error (.unknownOption "--unknown"), .error (.unexpectedArgument "second"), .error (.missingValue "--output"), .error (.missingValue "--output") => true | _, _, _, _, _ => false
  report "cli" passed "CLI decoding mismatch"

private def llvmSignature (name : String) (result : NecoLean.Llvm.ValueType) (parameters : List NecoLean.Llvm.ValueType) (variadic : Bool := false) : NecoLean.Llvm.FunctionSignature :=
  { name, callable := { parameters, result, variadic } }

private def functionPointerType (result : NecoLean.Llvm.ValueType) (parameters : List NecoLean.Llvm.ValueType) (variadic : Bool := false) : NecoLean.Llvm.ValueType :=
  .functionPointer parameters result variadic

private def globalStringPointer (value : String) : NecoLean.Llvm.ValueType :=
  .pointer (some (.array (.integer 8) (value.toUTF8.size + 1)))

private def cStringPointer : NecoLean.Llvm.ValueType :=
  .pointer (some (.integer 8))

private def globalFunctionOperand (name : String) (result : NecoLean.Llvm.ValueType) (parameters : List NecoLean.Llvm.ValueType) (variadic : Bool := false) : NecoLean.Llvm.Operand :=
  .globalFunction name (functionPointerType result parameters variadic)

private def validSignature : NecoLean.Llvm.FunctionSignature :=
  llvmSignature "main" (.integer 32) []

private def validModule (value : Int) : NecoLean.Llvm.Module :=
  { targetTriple := some "arm64-apple-darwin",
    functions := [.definition validSignature [{ label := "entry", terminator := some (.ret (some (.integer 32 value))) }]] }

private def mustTailDirectValueModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "target" (.integer 32) [(.integer 32)])
          [{ label := "entry", terminator := some (.ret (some (.parameter 0 (.integer 32)))) }],
       .definition (llvmSignature "caller" (.integer 32) [(.integer 32)])
          [{ label := "entry",
             terminator := some (.mustTailCall (some ⟨0⟩) (globalFunctionOperand "target" (.integer 32) [(.integer 32)]) [(.parameter 0 (.integer 32))]) }]] }

private def mustTailDirectVoidModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "voidTarget" .void [])
          [{ label := "entry", terminator := some (.ret none) }],
       .definition (llvmSignature "voidCaller" .void [])
          [{ label := "entry", terminator := some (.mustTailCall none (globalFunctionOperand "voidTarget" .void []) []) }]] }

private def mustTailIndirectValueModule : NecoLean.Llvm.Module :=
  let functionType := functionPointerType (.integer 32) [(.integer 32)]
  { functions :=
      [.definition (llvmSignature "indirectTarget" (.integer 32) [(.integer 32)])
          [{ label := "entry", terminator := some (.ret (some (.parameter 0 (.integer 32)))) }],
       .definition (llvmSignature "indirectCaller" (.integer 32) [(.integer 32)])
          [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
           { label := "left", terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join",
             instructions := [.phi ⟨0⟩ functionType [
               ("left", globalFunctionOperand "indirectTarget" (.integer 32) [(.integer 32)]),
               ("right", globalFunctionOperand "indirectTarget" (.integer 32) [(.integer 32)])]],
             terminator := some (.mustTailCall (some ⟨1⟩) (.local ⟨0⟩ functionType) [(.parameter 0 (.integer 32))]) }]] }

private def mustTailIndirectVoidModule : NecoLean.Llvm.Module :=
  let functionType := functionPointerType .void []
  { functions :=
      [.definition (llvmSignature "indirectVoidTarget" .void [])
          [{ label := "entry", terminator := some (.ret none) }],
       .definition (llvmSignature "indirectVoidCaller" .void [])
          [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
           { label := "left", terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join",
             instructions := [.phi ⟨0⟩ functionType [
               ("left", globalFunctionOperand "indirectVoidTarget" .void []),
               ("right", globalFunctionOperand "indirectVoidTarget" .void [])]],
             terminator := some (.mustTailCall none (.local ⟨0⟩ functionType) []) }]] }

private def mustTailInvalidModules : List NecoLean.Llvm.Module :=
  let integer32 := .integer 32
  let integer64 := .integer 64
  let target32 := globalFunctionOperand "target" integer32 [integer32]
  let targetVoid := globalFunctionOperand "voidTarget" .void []
  let targetVariadic := globalFunctionOperand "variadicTarget" integer32 [integer32] true
  let baseTarget := .definition (llvmSignature "target" integer32 [integer32])
    [{ label := "entry", terminator := some (.ret (some (.parameter 0 integer32))) }]
  let baseVoidTarget := .definition (llvmSignature "voidTarget" .void [])
    [{ label := "entry", terminator := some (.ret none) }]
  let baseVariadicTarget := .definition (llvmSignature "variadicTarget" integer32 [integer32] true)
    [{ label := "entry", terminator := some (.ret (some (.parameter 0 integer32))) }]
  [ { functions := [baseTarget,
        .definition (llvmSignature "variadicCaller" integer32 [integer32] true)
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) target32 [(.parameter 0 integer32)]) }]] },
    { functions := [baseVariadicTarget,
        .definition (llvmSignature "variadicTargetCaller" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) targetVariadic [(.parameter 0 integer32)]) }]] },
    { functions := [.definition (llvmSignature "differentTarget" integer64 [integer64])
          [{ label := "entry", terminator := some (.ret (some (.parameter 0 integer64))) }],
        .definition (llvmSignature "differentCaller" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) (globalFunctionOperand "differentTarget" integer64 [integer64]) [(.parameter 0 integer32)]) }]] },
    { functions := [.definition (llvmSignature "resultTarget" integer64 [integer32])
          [{ label := "entry", terminator := some (.ret (some (.integer 64 0))) }],
        .definition (llvmSignature "resultCaller" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) (globalFunctionOperand "resultTarget" integer64 [integer32]) [(.parameter 0 integer32)]) }]] },
    { functions := [baseTarget,
        .definition (llvmSignature "missingResult" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall none target32 [(.parameter 0 integer32)]) }]] },
    { functions := [baseVoidTarget,
        .definition (llvmSignature "unexpectedResult" .void [])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) targetVoid []) }]] },
    { functions := [baseTarget,
        .definition (llvmSignature "missingArgument" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) target32 []) }]] },
    { functions := [baseTarget,
        .definition (llvmSignature "wrongArgument" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) target32 [(.integer 64 1)]) }]] },
    { functions := [baseTarget,
        .definition (llvmSignature "forgedPointer" integer32 [integer32])
          [{ label := "entry", terminator := some (.mustTailCall (some ⟨0⟩) (globalFunctionOperand "target" integer64 [integer64]) [(.parameter 0 integer32)]) }]] },
    { functions := [baseTarget,
        .definition (llvmSignature "duplicateTerminal" integer32 [integer32])
          [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.parameter 0 integer32) (.integer 32 1)], terminator := some (.mustTailCall (some ⟨0⟩) target32 [(.parameter 0 integer32)]) }]] },
    { functions := [baseTarget,
        .definition (llvmSignature "nonDominatingCallee" integer32 [integer32])
          [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
           { label := "left",
             instructions := [.alloca ⟨0⟩ (functionPointerType integer32 [integer32]),
               .store target32 (.local ⟨0⟩ (.pointer (some (functionPointerType integer32 [integer32])))),
               .load ⟨1⟩ (.local ⟨0⟩ (.pointer (some (functionPointerType integer32 [integer32]))))],
             terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join", terminator := some (.mustTailCall (some ⟨2⟩) (.local ⟨1⟩ (functionPointerType integer32 [integer32])) [(.parameter 0 integer32)]) }]] } ]

private def llvmMustTailCheck : IO Bool := do
  let validModules := [mustTailDirectValueModule, mustTailDirectVoidModule, mustTailIndirectValueModule, mustTailIndirectVoidModule]
  let validResults := validModules.map NecoLean.Llvm.validate
  let validPassed := match validResults with
    | [.ok directValue, .ok directVoid, .ok indirectValue, .ok indirectVoid] =>
      let directValueText := String.fromUTF8! (NecoLean.Llvm.encode directValue)
      let directVoidText := String.fromUTF8! (NecoLean.Llvm.encode directVoid)
      let indirectValueText := String.fromUTF8! (NecoLean.Llvm.encode indirectValue)
      let indirectVoidText := String.fromUTF8! (NecoLean.Llvm.encode indirectVoid)
      let repeated := [NecoLean.Llvm.encode directValue == NecoLean.Llvm.encode directValue,
        NecoLean.Llvm.encode directVoid == NecoLean.Llvm.encode directVoid,
        NecoLean.Llvm.encode indirectValue == NecoLean.Llvm.encode indirectValue,
        NecoLean.Llvm.encode indirectVoid == NecoLean.Llvm.encode indirectVoid].all id
      repeated && directValueText.contains "musttail call i32 @target(i32 %p0)" && directValueText.contains "ret i32 %r0" &&
        directVoidText.contains "musttail call void @voidTarget()" && directVoidText.contains "ret void" &&
        indirectValueText.contains "musttail call i32 %r0(i32 %p0)" && indirectValueText.contains "ret i32 %r1" &&
        indirectVoidText.contains "musttail call void %r0()" && indirectVoidText.contains "ret void"
    | _ => false
  let invalidPassed := mustTailInvalidModules.all (fun module => match NecoLean.Llvm.validate module with | .error (.invalidModule _) => true | _ => false)
  report "llvm-musttail" (validPassed && invalidPassed) "musttail validation or rendering mismatch"

private def mustTailValueExecutionModule (module : NecoLean.Llvm.Module) (caller : String) : NecoLean.Llvm.Module :=
  { module with
    functions := module.functions ++
      [.definition (llvmSignature "main" (.integer 32) [])
          [{ label := "entry",
             instructions := [.call (some ⟨0⟩) (globalFunctionOperand caller (.integer 32) [(.integer 32)]) [(.integer 32 41)]],
             terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]] }

private def mustTailVoidExecutionModule (module : NecoLean.Llvm.Module) (caller : String) : NecoLean.Llvm.Module :=
  { module with
    functions := module.functions ++
      [.definition (llvmSignature "main" (.integer 32) [])
          [{ label := "entry",
             instructions := [.call none (globalFunctionOperand caller .void []) []],
             terminator := some (.ret (some (.integer 32 0))) }]] }

private def mustTailByteArrayText (bytes : ByteArray) : String :=
  "[" ++ String.intercalate ", " (bytes.toList.map (fun byte => s!"{byte.toNat}")) ++ "]"

private def mustTailLlvmFailureText : NecoLean.Llvm.Failure → String
  | .invalidModule message => s!"invalidModule({message})"
  | .invalidUtf8 source => s!"invalidUtf8({source})"
  | .invalidRuntimeSourceName name message => s!"invalidRuntimeSourceName({name},{message})"
  | .duplicateRuntimeSourceName name => s!"duplicateRuntimeSourceName({name})"
  | .invalidRuntimeUnitOptimization runtimeSourceIndex logicalName inputDigest reason =>
    s!"invalidRuntimeUnitOptimization({runtimeSourceIndex},{logicalName},{inputDigest},{reason})"
  | .runtimeSourceDirectoryCreation message => s!"runtimeSourceDirectoryCreation({message})"
  | .runtimeSourceWrite name path message => s!"runtimeSourceWrite({name},{path},{message})"
  | .artifactFile operation path message => s!"artifactFile({operation},{path},{message})"
  | .artifactDirectoryExists path => s!"artifactDirectoryExists({path})"
  | .artifactDirectoryAcquisition path message => s!"artifactDirectoryAcquisition({path},{message})"
  | .artifactCleanup path message none => s!"artifactCleanup({path},{message},prior=none)"
  | .artifactCleanup path message (some prior) => s!"artifactCleanup({path},{message},prior={mustTailLlvmFailureText prior})"
  | .emptyObjectLinkInput => "emptyObjectLinkInput"
  | .compilerIdentityMismatch expected actual =>
    s!"compilerIdentityMismatch(expected={reprStr expected},actual={reprStr actual})"
  | .objectDigestMismatch path expected actual =>
    s!"objectDigestMismatch({path},expected={expected},actual={actual})"
  | .invalidLinkOutputPath path message => s!"invalidLinkOutputPath({path},{message})"
  | .linkPublication operation path message => s!"linkPublication({operation},{path},{message})"
  | .toolUnavailable command => s!"toolUnavailable({command})"
  | .toolRejected command arguments code stdout stderr => s!"toolRejected({command},arguments={arguments},{code},stdout={mustTailByteArrayText stdout},stderr={mustTailByteArrayText stderr})"

private def mustTailSystemFailureText : NecoLean.System.Failure → String
  | .file path message => s!"file({path},{message})"
  | .processStart command message => s!"processStart({command},{message})"
  | .nonZeroExit command code stdout stderr => s!"nonZeroExit({command},{code},stdout={mustTailByteArrayText stdout},stderr={mustTailByteArrayText stderr})"

private def reportMustTailExecutionFailure (path : System.FilePath) (stage detail : String) : IO Unit :=
  IO.eprintln s!"llvm-musttail-execution {path} {stage}: {detail}"

private def runMustTailExecutionCase (path : System.FilePath) (module : NecoLean.Llvm.Module) (expectedExit : UInt32) : IO Bool := do
  match NecoLean.Llvm.validate module with
  | .error failure =>
    reportMustTailExecutionFailure path "validate" (mustTailLlvmFailureText failure)
    pure false
  | .ok valid =>
    match ← NecoLean.Llvm.compile { module := valid, outputPath := path } with
    | .error failure =>
      reportMustTailExecutionFailure path "compile" (mustTailLlvmFailureText failure)
      pure false
    | .ok _ =>
      match ← NecoLean.System.run { command := path.toString } with
      | .ok output =>
        let passed := output.exitCode == expectedExit && output.stdout.isEmpty && output.stderr.isEmpty
        if !passed then
          reportMustTailExecutionFailure path "run"
            s!"expectedExit={expectedExit},actualExit={output.exitCode},stdout={mustTailByteArrayText output.stdout},stderr={mustTailByteArrayText output.stderr}"
        pure passed
      | .error failure =>
        let passed := match failure with
          | .nonZeroExit _ code stdout stderr => code == expectedExit && stdout.isEmpty && stderr.isEmpty
          | _ => false
        if !passed then
          reportMustTailExecutionFailure path "run" (mustTailSystemFailureText failure)
        pure passed

private def mustTailExecutionCheck : IO Bool := do
  let directValue ← runMustTailExecutionCase ".lake/neco-lean-musttail-direct-value"
    (mustTailValueExecutionModule mustTailDirectValueModule "caller") 41
  let directVoid ← runMustTailExecutionCase ".lake/neco-lean-musttail-direct-void"
    (mustTailVoidExecutionModule mustTailDirectVoidModule "voidCaller") 0
  let indirectValue ← runMustTailExecutionCase ".lake/neco-lean-musttail-indirect-value"
    (mustTailValueExecutionModule mustTailIndirectValueModule "indirectCaller") 41
  let indirectVoid ← runMustTailExecutionCase ".lake/neco-lean-musttail-indirect-void"
    (mustTailVoidExecutionModule mustTailIndirectVoidModule "indirectVoidCaller") 0
  let directValueReport ← report "llvm-musttail-execution-direct-value" directValue "wrapper execution mismatch"
  let directVoidReport ← report "llvm-musttail-execution-direct-void" directVoid "wrapper execution mismatch"
  let indirectValueReport ← report "llvm-musttail-execution-indirect-value" indirectValue "wrapper execution mismatch"
  let indirectVoidReport ← report "llvm-musttail-execution-indirect-void" indirectVoid "wrapper execution mismatch"
  report "llvm-musttail-execution" (directValueReport && directVoidReport && indirectValueReport && indirectVoidReport)
    "musttail wrapper execution mismatch"

private def joinAndCastModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition validSignature
        [{ label := "entry",
           instructions := [.alloca ⟨0⟩ (.array (.integer 32) 4)],
           terminator := some (.condBranch (.integer 1 0) "left" "right") },
         { label := "left",
           instructions := [.zext ⟨2⟩ (.integer 8 1) 32],
           terminator := some (.branch "join") },
         { label := "right",
           instructions := [.getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.array (.integer 32) 4)))) [.integer 32 0, .integer 32 1], .sext ⟨3⟩ (.integer 8 (-1)) 32],
           terminator := some (.branch "join") },
         { label := "join",
           instructions := [.phi ⟨4⟩ (.integer 32) [("left", .local ⟨2⟩ (.integer 32)), ("right", .local ⟨3⟩ (.integer 32))], .trunc ⟨5⟩ (.local ⟨4⟩ (.integer 32)) 8],
           terminator := some (.switch (.integer 8 0) "exit" [(.integer 8 1, "exit")]) },
         { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }

private def floatModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition validSignature
        [{ label := "entry",
           instructions :=
             [.fadd ⟨0⟩ (.float64 0x3FF0000000000000) (.float64 0x4000000000000000),
              .fsub ⟨1⟩ (.local ⟨0⟩ .float64) (.float64 0x3FF0000000000000),
              .fmul ⟨2⟩ (.local ⟨1⟩ .float64) (.float64 0x4000000000000000),
              .fdiv ⟨3⟩ (.local ⟨2⟩ .float64) (.float64 0x4000000000000000),
              .fneg ⟨4⟩ (.local ⟨3⟩ .float64),
              .fcmp ⟨5⟩ .false (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨6⟩ .oeq (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨7⟩ .ogt (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨8⟩ .oge (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨9⟩ .olt (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨10⟩ .ole (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨11⟩ .one (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨12⟩ .ord (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨13⟩ .uno (.local ⟨4⟩ .float64) (.float64 0x7FF8000000000001),
              .fcmp ⟨14⟩ .ueq (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨15⟩ .ugt (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨16⟩ .uge (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨17⟩ .ult (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨18⟩ .ule (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨19⟩ .une (.local ⟨4⟩ .float64) (.float64 0x7FF8000000000002),
              .fcmp ⟨20⟩ .true (.local ⟨4⟩ .float64) (.float64 0x0000000000000000),
              .fadd ⟨21⟩ (.float64 0x8000000000000000) (.float64 0x0000000000000000),
              .fadd ⟨22⟩ (.float64 0x0000000000000001) (.float64 0x0000000000000000),
              .fadd ⟨23⟩ (.float64 0x7FF0000000000000) (.float64 0x0000000000000000)],
           terminator := some (.ret (some (.integer 32 0))) }]] }

private def floatArrayModule : NecoLean.Llvm.Module :=
  { functions := [.definition validSignature
      [{ label := "entry",
         instructions := [.alloca ⟨0⟩ (.array .float64 2),
           .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.array .float64 2)))) [.integer 32 0, .integer 32 1],
           .store (.float64 0x3FF0000000000000) (.local ⟨1⟩ (.pointer (some .float64))),
           .load ⟨2⟩ (.local ⟨1⟩ (.pointer (some .float64))),
           .fcmp ⟨3⟩ .oeq (.local ⟨2⟩ .float64) (.float64 0x3FF0000000000000),
           .zext ⟨4⟩ (.local ⟨3⟩ (.integer 1)) 32],
         terminator := some (.ret (some (.local ⟨4⟩ (.integer 32)))) }]] }

private def callableTransportModule : NecoLean.Llvm.Module :=
  let calleeType := functionPointerType (.integer 32) [(.integer 32)]
  { functions :=
      [.definition (llvmSignature "increment" (.integer 32) [(.integer 32)])
          [{ label := "entry",
             instructions := [.add ⟨0⟩ 32 (.parameter 0 (.integer 32)) (.integer 32 1)],
             terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }],
       .definition (llvmSignature "apply" (.integer 32) [calleeType, (.integer 32)])
          [{ label := "entry",
             instructions := [.call (some ⟨0⟩) (.parameter 0 calleeType) [(.parameter 1 (.integer 32))]],
             terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }],
       .definition (llvmSignature "choose" calleeType [])
          [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
           { label := "left", terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join",
             instructions := [.phi ⟨0⟩ calleeType [("left", globalFunctionOperand "increment" (.integer 32) [(.integer 32)]), ("right", globalFunctionOperand "increment" (.integer 32) [(.integer 32)])]],
             terminator := some (.ret (some (.local ⟨0⟩ calleeType))) }],
       .definition validSignature
          [{ label := "entry",
             instructions :=
               [.alloca ⟨0⟩ calleeType,
                .store (globalFunctionOperand "increment" (.integer 32) [(.integer 32)]) (.local ⟨0⟩ (.pointer (some calleeType))),
                .load ⟨1⟩ (.local ⟨0⟩ (.pointer (some calleeType))),
                .call (some ⟨2⟩) (globalFunctionOperand "apply" (.integer 32) [calleeType, (.integer 32)]) [(.local ⟨1⟩ calleeType), (.integer 32 41)],
                .call (some ⟨3⟩) (globalFunctionOperand "choose" calleeType []) [],
                .call none (.local ⟨3⟩ calleeType) [(.integer 32 0)]],
             terminator := some (.ret (some (.local ⟨2⟩ (.integer 32)))) }]] }

private def rawPointerSlotModule : NecoLean.Llvm.Module :=
  { functions := [.definition (llvmSignature "main" (.integer 32) [.pointer none])
      [{ label := "entry",
         instructions := [.alloca ⟨0⟩ (.pointer none), .store (.parameter 0 (.pointer none)) (.local ⟨0⟩ (.pointer (some (.pointer none))))],
         terminator := some (.ret (some (.integer 32 0))) }]] }

private def nullTransportModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "consume_raw" (.integer 32) [.pointer none])
          [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }],
       .definition (llvmSignature "consume_typed" (.integer 32) [(.pointer (some (.integer 8)))])
          [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }],
       .definition (llvmSignature "consume_empty" (.integer 32) [(.pointer (some (.array (.integer 8) 0)))])
          [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }],
       .definition validSignature
          [{ label := "entry",
             instructions :=
               [.call (some ⟨0⟩) (globalFunctionOperand "consume_raw" (.integer 32) [.pointer none]) [(.null (.pointer none))],
                .call (some ⟨1⟩) (globalFunctionOperand "consume_typed" (.integer 32) [(.pointer (some (.integer 8)))]) [(.null (.pointer (some (.integer 8))))],
                .call none (globalFunctionOperand "consume_empty" (.integer 32) [(.pointer (some (.array (.integer 8) 0)))]) [(.null (.pointer (some (.array (.integer 8) 0))))],
                .add ⟨2⟩ 32 (.local ⟨0⟩ (.integer 32)) (.local ⟨1⟩ (.integer 32))],
             terminator := some (.ret (some (.local ⟨2⟩ (.integer 32)))) }]] }

private def nullPhiReturnModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "raw_phi" (.pointer none) [])
          [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") },
           { label := "left", terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join",
             instructions := [.phi ⟨0⟩ (.pointer none) [("left", .null (.pointer none)), ("right", .null (.pointer none))]],
             terminator := some (.ret (some (.local ⟨0⟩ (.pointer none)))) }],
       .definition (llvmSignature "typed_phi" (.pointer (some (.integer 8))) [])
          [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") },
           { label := "left", terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join",
             instructions := [.phi ⟨0⟩ (.pointer (some (.integer 8))) [("left", .null (.pointer (some (.integer 8)))), ("right", .null (.pointer (some (.integer 8))))]],
             terminator := some (.ret (some (.local ⟨0⟩ (.pointer (some (.integer 8)))))) }]] }

private def nullPhiTypeMismatchModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition validSignature
          [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") },
           { label := "left", terminator := some (.branch "join") },
           { label := "right", terminator := some (.branch "join") },
           { label := "join",
             instructions := [.phi ⟨0⟩ (.pointer none) [("left", .null (.pointer none)), ("right", .null (.pointer (some (.integer 8))))]],
             terminator := some (.ret (some (.integer 32 0))) }]] }

private def nullReturnTypeMismatchModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "raw_return" (.pointer none) [])
          [{ label := "entry", terminator := some (.ret (some (.null (.pointer (some (.integer 8)))))) }]] }

private def gepNonZeroFirstIndexModule : NecoLean.Llvm.Module :=
  { functions := [.definition validSignature
      [{ label := "entry",
         instructions := [.alloca ⟨0⟩ (.array (.integer 8) 4), .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.array (.integer 8) 4)))) [.integer 32 1, .integer 32 2]],
         terminator := some (.ret (some (.integer 32 0))) }]] }

private def structGepModule : NecoLean.Llvm.Module :=
  let pairType := .struct [(.array (.integer 8) 4), (.struct [])]
  { functions := [.definition validSignature
      [{ label := "entry",
         instructions := [.alloca ⟨0⟩ pairType,
           .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some pairType))) [.integer 32 0, .integer 32 0, .integer 32 2],
           .store (.integer 8 7) (.local ⟨1⟩ (.pointer (some (.integer 8)))),
           .load ⟨2⟩ (.local ⟨1⟩ (.pointer (some (.integer 8)))),
           .getElementPtr ⟨3⟩ (.local ⟨0⟩ (.pointer (some pairType))) [.integer 32 0, .integer 32 1]],
         terminator := some (.ret (some (.integer 32 0))) }]] }

private def allocatorStructType : NecoLean.Llvm.ValueType :=
  .struct [(.integer 32), (.integer 32)]

private def allocatorStructModule : NecoLean.Llvm.Module :=
  { functions :=
      [.declaration (llvmSignature "allocate_pair" (.pointer (some allocatorStructType)) [.pointer none]),
       .definition validSignature
          [{ label := "entry",
             instructions :=
               [.call (some ⟨0⟩) (globalFunctionOperand "allocate_pair" (.pointer (some allocatorStructType)) [.pointer none]) [(.null (.pointer none))],
                .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some allocatorStructType))) [.integer 32 0, .integer 32 1],
                .store (.integer 32 42) (.local ⟨1⟩ (.pointer (some (.integer 32)))),
                .load ⟨2⟩ (.local ⟨1⟩ (.pointer (some (.integer 32))))],
             terminator := some (.ret (some (.local ⟨2⟩ (.integer 32)))) }]] }

private def allocatorStructStoreMismatchModule : NecoLean.Llvm.Module :=
  { functions :=
      [.declaration (llvmSignature "allocate_pair" (.pointer (some allocatorStructType)) [.pointer none]),
       .definition validSignature
          [{ label := "entry",
             instructions :=
               [.call (some ⟨0⟩) (globalFunctionOperand "allocate_pair" (.pointer (some allocatorStructType)) [.pointer none]) [(.null (.pointer none))],
                .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some allocatorStructType))) [.integer 32 0, .integer 32 1],
                .store (.float64 0x3FF0000000000000) (.local ⟨1⟩ (.pointer (some (.integer 32))))],
             terminator := some (.ret (some (.integer 32 0))) }]] }

private def callableStructGepModule : NecoLean.Llvm.Module :=
  let callableType := functionPointerType (.integer 32) [(.integer 32)]
  let storageType := .struct [(.array (.struct [callableType]) 1)]
  { functions :=
      [.definition (llvmSignature "increment" (.integer 32) [(.integer 32)])
          [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.parameter 0 (.integer 32)) (.integer 32 1)], terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }],
       .definition validSignature
          [{ label := "entry",
             instructions := [.alloca ⟨0⟩ storageType,
               .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some storageType))) [.integer 32 0, .integer 32 0, .integer 32 0, .integer 32 0],
               .store (globalFunctionOperand "increment" (.integer 32) [(.integer 32)]) (.local ⟨1⟩ (.pointer (some callableType))),
               .load ⟨2⟩ (.local ⟨1⟩ (.pointer (some callableType))),
               .call (some ⟨3⟩) (.local ⟨2⟩ callableType) [(.integer 32 41)]],
             terminator := some (.ret (some (.local ⟨3⟩ (.integer 32)))) }]] }

private def fcmpPredicates : List NecoLean.Llvm.FcmpPredicate :=
  [.false, .oeq, .ogt, .oge, .olt, .ole, .one, .ord,
   .uno, .ueq, .ugt, .uge, .ult, .ule, .une, .true]

private def fcmpExpected : List (UInt64 × UInt64 × List Bool) :=
  [ (0x3FF0000000000000, 0x4000000000000000, [false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true]),
    (0x3FF0000000000000, 0x3FF0000000000000, [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true]),
    (0x4000000000000000, 0x3FF0000000000000, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true]),
    (0x7FF8000000000001, 0x3FF0000000000000, [false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true]),
    (0x3FF0000000000000, 0x7FF8000000000001, [false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true]),
    (0x7FF8000000000001, 0x7FF8000000000002, [false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true]) ]

private def fcmpTruthTableModule : NecoLean.Llvm.Module :=
  let cases := fcmpExpected
  let checks := (cases.mapIdx (fun (caseIndex : Nat) (item : UInt64 × UInt64 × List Bool) =>
    let left := item.1
    let right := item.2.1
    let expected := item.2.2
    expected.mapIdx (fun (predicateIndex : Nat) (expectedValue : Bool) =>
      let base := caseIndex * 64 + predicateIndex * 4
      let fcmpResult : NecoLean.Llvm.ResultId := ⟨base⟩
      let bitResult : NecoLean.Llvm.ResultId := ⟨base + 1⟩
      let equalityResult : NecoLean.Llvm.ResultId := ⟨base + 2⟩
      let consumedResult : NecoLean.Llvm.ResultId := ⟨base + 3⟩
      let instructions : List NecoLean.Llvm.Instruction :=
        [.fcmp fcmpResult (fcmpPredicates.getD predicateIndex .false) (.float64 left) (.float64 right),
         .zext bitResult (.local fcmpResult (.integer 1)) 32,
         .icmpEq equalityResult 32 (.local bitResult (.integer 32)) (.integer 32 (if expectedValue then 1 else 0)),
         .zext consumedResult (.local equalityResult (.integer 1)) 32]
      let operand : NecoLean.Llvm.Operand := .local consumedResult (.integer 32)
      (instructions, operand)))).flatten
  let checkInstructions := checks.flatMap Prod.fst
  let sumInstructions := checks.mapIdx (fun index check =>
    .add ⟨400 + index⟩ 32 (if index == 0 then .integer 32 0 else .local ⟨399 + index⟩ (.integer 32)) check.2)
  let finalSum : NecoLean.Llvm.Operand := .local ⟨495⟩ (.integer 32)
  { functions := [.definition validSignature
      [{ label := "entry",
         instructions := checkInstructions ++ sumInstructions ++
           [.icmpEq ⟨500⟩ 32 finalSum (.integer 32 checks.length),
            .zext ⟨501⟩ (.local ⟨500⟩ (.integer 1)) 32,
            .sub ⟨502⟩ 32 (.integer 32 1) (.local ⟨501⟩ (.integer 32))],
         terminator := some (.ret (some (.local ⟨502⟩ (.integer 32)))) }]] }

private def invalidFloatModules : List NecoLean.Llvm.Module :=
  [ { functions := [.definition validSignature
        [{ label := "entry", instructions := [.fneg ⟨0⟩ (.integer 32 1)], terminator := some (.ret (some (.integer 32 0))) }]] },
    { functions := [.definition validSignature
        [{ label := "entry", instructions := [.fcmp ⟨0⟩ .oeq (.float64 0x3FF0000000000000) (.float64 0x3FF0000000000000), .fadd ⟨1⟩ (.local ⟨0⟩ .float64) (.float64 0x3FF0000000000000)], terminator := some (.ret (some (.integer 32 0))) }]] },
    { functions := [.declaration (llvmSignature "takes-float" .float64 [.float64]), .definition validSignature
        [{ label := "entry", instructions := [.call (some ⟨0⟩) (globalFunctionOperand "takes-float" .float64 [.float64]) [.integer 32 1]], terminator := some (.ret (some (.integer 32 0))) }]] },
    { functions := [.definition validSignature
        [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
         { label := "left", instructions := [.fadd ⟨0⟩ (.float64 0x3FF0000000000000) (.float64 0x3FF0000000000000)], terminator := some (.branch "join") },
         { label := "right", instructions := [.add ⟨1⟩ 32 (.integer 32 1) (.integer 32 2)], terminator := some (.branch "join") },
         { label := "join", instructions := [.phi ⟨2⟩ .float64 [("left", .local ⟨0⟩ .float64), ("right", .local ⟨1⟩ (.integer 32))]], terminator := some (.ret (some (.integer 32 0))) }]] },
    { functions := [.definition validSignature
        [{ label := "entry", instructions := [.alloca ⟨0⟩ .float64, .store (.integer 32 1) (.local ⟨0⟩ (.pointer (some .float64)))], terminator := some (.ret (some (.integer 32 0))) }]] },
    { functions := [.definition validSignature
        [{ label := "entry", instructions := [.alloca ⟨0⟩ .float64, .load ⟨1⟩ (.local ⟨0⟩ (.pointer (some .float64))), .fadd ⟨2⟩ (.local ⟨1⟩ (.integer 32)) (.float64 0x3FF0000000000000)], terminator := some (.ret (some (.integer 32 0))) }]] },
    { functions := [.definition { validSignature with callable := { validSignature.callable with result := .float64 } }
        [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }]] } ]


private def runtimeSourceHeader (delta : Nat) : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "runtime_fixture.h" .header s!"#ifndef RUNTIME_FIXTURE_H\n#define RUNTIME_FIXTURE_H\n#define ADD_RUNTIME_DELTA {delta}\nint add_runtime(int value);\n#endif\n".toUTF8

private def runtimeSourceUnit : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "runtime_fixture.c" .compilationUnit "#include \"runtime_fixture.h\"\nint add_runtime(int value) { return value + ADD_RUNTIME_DELTA; }\n".toUTF8

private def allocatorSourceHeader : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "allocator_fixture.h" .header "void *allocate_pair(void *nullable);\n".toUTF8

private def allocatorSourceUnit : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "allocator_fixture.c" .compilationUnit "#include \"allocator_fixture.h\"\nstruct AllocatorPair { int first; int second; };\nstatic struct AllocatorPair pair;\nvoid *allocate_pair(void *nullable) { (void)nullable; return &pair; }\n".toUTF8

private def allocatorSources : Except NecoLean.Llvm.Failure (List NecoLean.Llvm.RuntimeSource) := do
  let header ← allocatorSourceHeader
  let unit ← allocatorSourceUnit
  pure [header, unit]

private def runtimeSourceHiddenHeaderUnit : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "runtime_fixture.c" .compilationUnit "#include \"runtime_fixture.h\"\n#include \"extra.h\"\nint add_runtime(int value) { return value + ADD_RUNTIME_DELTA + EXTRA_DELTA; }\n".toUTF8

private def runtimeSourceAlternateUnit : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "runtime_fixture.c" .compilationUnit "#include \"runtime_fixture.h\"\nint add_runtime(int value) { return value + ADD_RUNTIME_DELTA + 1; }\n".toUTF8

private def runtimeSourceExtraHeader : Except NecoLean.Llvm.Failure NecoLean.Llvm.RuntimeSource :=
  NecoLean.Llvm.RuntimeSource.create "extra.h" .header "#define EXTRA_DELTA 11\n".toUTF8

private def runtimeSourceModule : NecoLean.Llvm.Module :=
  { functions :=
      [.declaration (llvmSignature "add_runtime" (.integer 32) [(.integer 32)]),
       .definition validSignature
          [{ label := "entry",
             instructions := [.call (some ⟨0⟩) (globalFunctionOperand "add_runtime" (.integer 32) [(.integer 32)]) [(.integer 32 37)]],
             terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]] }

private def runtimeSourceRequestSources (delta : Nat := 5) (alternateUnit : Bool := false) : Except NecoLean.Llvm.Failure (List NecoLean.Llvm.RuntimeSource) := do
  let header ← runtimeSourceHeader delta
  let unit ← if alternateUnit then runtimeSourceAlternateUnit else runtimeSourceUnit
  pure [header, unit]

private def runtimeSourceHiddenHeaderSources : Except NecoLean.Llvm.Failure (List NecoLean.Llvm.RuntimeSource) := do
  let header ← runtimeSourceHeader 5
  let unit ← runtimeSourceHiddenHeaderUnit
  let extra ← runtimeSourceExtraHeader
  pure [header, unit, extra]

private def runtimeSourceHiddenHeaderMissingSources : Except NecoLean.Llvm.Failure (List NecoLean.Llvm.RuntimeSource) := do
  let header ← runtimeSourceHeader 5
  let unit ← runtimeSourceHiddenHeaderUnit
  pure [header, unit]

open Lean Elab Term

elab "privateDecl%" modulePrefix:str declarationSuffix:str : term => do
  let environment ← getEnv
  let modulePrefixText := modulePrefix.getString
  let declarationSuffixText := declarationSuffix.getString
  let candidates := environment.constants.toList.filter fun item =>
    let name := item.1.toString
    name.startsWith modulePrefixText && name.endsWith declarationSuffixText
  match candidates with
  | [(name, _)] => elabTerm (mkIdent name) none
  | [] => throwError "private declaration not found"
  | _ => throwError "private declaration is ambiguous"

private def productionPredecessorsOf : List NecoLean.Llvm.Block → String → List String :=
  privateDecl% "_private.NecoLean.Llvm." ".NecoLean.Llvm.predecessorsOf"

private def productionComputeDominators : List NecoLean.Llvm.Block → List (String × List String) :=
  privateDecl% "_private.NecoLean.Llvm." ".NecoLean.Llvm.computeDominators"

private structure DominatorGraph where
  blocks : List NecoLean.Llvm.Block

private def graphLabels (graph : DominatorGraph) : List String :=
  graph.blocks.map NecoLean.Llvm.Block.label

private def graphTerminator (labels : List String) (targets : List Nat) : Option NecoLean.Llvm.Terminator :=
  match targets with
  | [] => some (.ret none)
  | target :: rest =>
      let targetLabel := labels.getD target "unknown"
      some (.switch (.integer 1 0) targetLabel (rest.map (fun index => (.integer 1 0, labels.getD index "unknown"))))

private def graphBlock (labels : List String) (source : Nat) (targets : List Nat) : NecoLean.Llvm.Block :=
  { label := labels.getD source "unknown", terminator := graphTerminator labels targets }

private def graphPredecessorLabels (graph : DominatorGraph) (target : String) : List String :=
  productionPredecessorsOf graph.blocks target

private def graphLookup (values : List (String × List String)) (label : String) : List String :=
  values.find? (·.1 == label) |>.map (·.2) |>.getD []

private def graphSame (left right : List (String × List String)) : Bool :=
  left.length == right.length && left.all (fun item => graphLookup right item.1 == item.2)

private def graphOldStep (graph : DominatorGraph) (current : List (String × List String)) : List (String × List String) :=
  let labels := graphLabels graph
  graph.blocks.map (fun block =>
    if labels.head? == some block.label then
      (block.label, [block.label])
    else
      let predecessors := graphPredecessorLabels graph block.label
      if predecessors.isEmpty then
        (block.label, [block.label])
      else
        let common := labels.filter (fun candidate =>
          predecessors.all (fun predecessor => (graphLookup current predecessor).any (· == candidate)))
        (block.label, block.label :: common))

private def graphOldComputeWithFuel (graph : DominatorGraph) (fuel : Nat) : List (String × List String) :=
  let labels := graphLabels graph
  let initial := labels.map (fun label =>
    if labels.head? == some label then (label, [label]) else (label, labels))
  let rec loop : Nat → List (String × List String) → List (String × List String)
    | 0, current => current
    | fuel + 1, current =>
      let next := graphOldStep graph current
      if graphSame current next then next else loop fuel next
  loop fuel initial

private def dominatorGraph (count edgeMask : Nat) : DominatorGraph :=
  let labels := (List.range count).map (fun index => s!"b{index}")
  let targets := (List.range count).map (fun source =>
    (List.range count).filter (fun target => Nat.testBit edgeMask (source * count + target)))
  { blocks := (List.range count).map (fun source => graphBlock labels source (targets.getD source [])) }

private def fixedDominatorGraph (count : Nat) (kind : Nat) : DominatorGraph :=
  let targets := fun source =>
    match kind with
    | 0 => if source + 1 < count then [source + 1] else []
    | 1 => if source == 0 then [1, 2] else if source == 1 || source == 2 then [3] else if source + 1 < count then [source + 1] else []
    | 2 => if count < 2 then [] else if source + 1 < count then [source + 1] else [0]
    | 3 => if source == 1 then [2] else if source == 2 then [1] else []
    | _ => if source == 0 then [count + 1] else []
  let labels := (List.range count).map (fun index => s!"b{index}")
  { blocks := (List.range count).map (fun source => graphBlock labels source (targets source)) }

private def linearDominatorExpected (count : Nat) : List (String × List String) :=
  (List.range count).map (fun index =>
    let label := s!"b{index}"
    if index == 0 then (label, [label])
    else (label, label :: (List.range index).map (fun dominator => s!"b{dominator}")))

private def dominatorCostCheck : IO Bool := do
  let exhaustive := [0, 1, 2, 3].all (fun count =>
    (List.range (2 ^ (count * count))).all (fun edgeMask =>
      let graph := dominatorGraph count edgeMask
      productionComputeDominators graph.blocks == graphOldComputeWithFuel graph (count + 1)))
  let fixed := [63, 64, 65].all (fun count =>
    [0, 1, 2, 3, 4].all (fun kind =>
      let graph := fixedDominatorGraph count kind
      productionComputeDominators graph.blocks == graphOldComputeWithFuel graph (count + 1)))
  let linear := productionComputeDominators (fixedDominatorGraph 3 0).blocks
  let diamond := productionComputeDominators (fixedDominatorGraph 4 1).blocks
  let disconnected := productionComputeDominators (fixedDominatorGraph 4 3).blocks
  let unknown := productionComputeDominators (fixedDominatorGraph 4 4).blocks
  let expectedValues :=
    linear == [("b0", ["b0"]), ("b1", ["b1", "b0"]), ("b2", ["b2", "b0", "b1"])] &&
    graphLookup diamond "b3" == ["b3", "b0"] &&
    disconnected == [("b0", ["b0"]), ("b1", ["b1", "b0", "b1", "b2", "b3"]),
      ("b2", ["b2", "b0", "b1", "b2", "b3"]), ("b3", ["b3"])] &&
    unknown == [("b0", ["b0"]), ("b1", ["b1"]), ("b2", ["b2"]), ("b3", ["b3"])] &&
    [63, 64, 65].all (fun count =>
      productionComputeDominators (fixedDominatorGraph count 0).blocks == linearDominatorExpected count)
  report "llvm-dominator-cost" (exhaustive && fixed && expectedValues) "array-backed dominator mismatch"

private def reachableStressBlocks (count : Nat) (cycle : Bool) : List NecoLean.Llvm.Block :=
  (List.range count).map (fun index =>
    let label := s!"b{index}"
    let terminator :=
      if index + 1 < count then some (.branch s!"b{index + 1}")
      else if cycle && count > 0 then some (.branch "b0")
      else some (.ret (some (.integer 32 0)))
    { label, terminator })

private def projectedModuleInvalid (blocks : List NecoLean.Llvm.Block) : Bool :=
  let projected := NecoLean.Llvm.blocksReachableFromEntry blocks
  match NecoLean.Llvm.validate { functions := [.definition validSignature projected] } with
  | .error (.invalidModule _) => true
  | _ => false

private def reachableBlockProjectionCheck : IO Bool := do
  let branchSwitchCycle : List NecoLean.Llvm.Block :=
    [{ label := "entry",
       terminator := some (.switch (.integer 1 0) "left" [(.integer 1 1, "right")]) },
     { label := "right", terminator := some (.branch "join") },
     { label := "dead", terminator := some (.ret (some (.integer 32 0))) },
     { label := "left", terminator := some (.branch "join") },
     { label := "join", terminator := some (.branch "cycle") },
     { label := "cycle", terminator := some (.branch "join") }]
  let orderedLabels :=
    (NecoLean.Llvm.blocksReachableFromEntry branchSwitchCycle).map NecoLean.Llvm.Block.label
  let disconnected : List NecoLean.Llvm.Block :=
    [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) },
     { label := "chain0", terminator := some (.branch "chain1") },
     { label := "chain1", terminator := some (.ret (some (.integer 32 0))) },
     { label := "cycle0", terminator := some (.branch "cycle1") },
     { label := "cycle1", terminator := some (.branch "cycle0") }]
  let disconnectedProjection := NecoLean.Llvm.blocksReachableFromEntry disconnected
  let phiBlocks : List NecoLean.Llvm.Block :=
    [{ label := "entry", terminator := some (.branch "live") },
     { label := "dead", terminator := some (.branch "join") },
     { label := "live", terminator := some (.branch "join") },
     { label := "join",
       instructions := [.phi ⟨0⟩ (.integer 32)
         [("dead", .integer 32 2), ("live", .integer 32 1)]],
       terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]
  let phiProjection := NecoLean.Llvm.blocksReachableFromEntry phiBlocks
  let phiPreserved :=
    phiProjection.map NecoLean.Llvm.Block.label == ["entry", "live", "join"] &&
      match phiProjection.find? (fun block => block.label == "join") with
      | some block =>
        block.instructions == [.phi ⟨0⟩ (.integer 32) [("live", .integer 32 1)]]
      | none => false
  let missingTarget : List NecoLean.Llvm.Block :=
    [{ label := "entry", terminator := some (.branch "missing") }]
  let deadDefinition : List NecoLean.Llvm.Block :=
    [{ label := "entry", terminator := some (.branch "live") },
     { label := "dead",
       instructions := [.add ⟨0⟩ 32 (.integer 32 1) (.integer 32 2)],
       terminator := some (.ret (some (.integer 32 0))) },
     { label := "live", terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]
  let invalidPhi := fun (incoming : List (String × NecoLean.Llvm.Operand)) =>
    projectedModuleInvalid
      [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
       { label := "left", terminator := some (.branch "join") },
       { label := "right", terminator := some (.branch "join") },
       { label := "join", instructions := [.phi ⟨0⟩ (.integer 32) incoming],
         terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]
  let duplicatePhi := invalidPhi [("left", .integer 32 1), ("left", .integer 32 2)]
  let missingPhi := invalidPhi [("left", .integer 32 1)]
  let mismatchedPhi := invalidPhi [("left", .integer 32 1), ("right", .integer 64 2)]
  let chain := reachableStressBlocks 565 false
  let cycle := reachableStressBlocks 565 true
  let passed :=
    NecoLean.Llvm.blocksReachableFromEntry [] == [] &&
    orderedLabels == ["entry", "right", "left", "join", "cycle"] &&
    disconnectedProjection ==
      [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }] &&
    phiPreserved &&
    NecoLean.Llvm.blocksReachableFromEntry chain == chain &&
    NecoLean.Llvm.blocksReachableFromEntry cycle == cycle &&
    projectedModuleInvalid missingTarget && projectedModuleInvalid deadDefinition &&
    duplicatePhi && missingPhi && mismatchedPhi
  report "llvm-reachable-block-projection" passed
    "reachable order, discarded phi incoming, invalid preservation, chain, or cycle mismatch"

private def llvmValidationCheck : IO Bool := do
  let reachableProjection ← reachableBlockProjectionCheck
  let floatValidation := NecoLean.Llvm.validate floatModule
  let badFloatOperand := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.fadd ⟨0⟩ (.integer 64 1) (.float64 0x3FF0000000000000)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badFcmpOperand := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.fcmp ⟨0⟩ .oeq (.integer 64 1) (.float64 0x3FF0000000000000)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let function2 := match (validModule 2).functions with | function :: _ => function | [] => .definition validSignature []
  let duplicate := NecoLean.Llvm.validate { functions := [function2, function2] }
  let zero := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.integer 0] } } [{ label := "entry", terminator := some (.ret (some (.integer 32 2))) }]] }
  let operandMismatch := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.integer 64] } } [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.parameter 0 (.integer 64)) (.integer 32 1)], terminator := some (.ret (some (.integer 32 2))) }]] }
  let expectedOperandMismatchInstruction : NecoLean.Llvm.Instruction := .add ⟨0⟩ 32 (.parameter 0 (.integer 64)) (.integer 32 1)
  let returnMismatch := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with result := .integer 64 } } [{ label := "entry", terminator := some (.ret (some (.integer 32 2))) }]] }
  let missingTerminator := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry" }]] }
  let missingTerminatorLater := NecoLean.Llvm.validate { functions := [.definition (llvmSignature "helper" (.integer 32) []) [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }], .definition validSignature [{ label := "entry" }]] }
  let invalidGlobalName := NecoLean.Llvm.validate { globals := [{ name := "bad name", value := "x" }], functions := [match (validModule 2).functions with | function :: _ => function | [] => .definition validSignature []] }
  let invalidNames := NecoLean.Llvm.validate { globals := [{ name := "fmt", value := "x" }], functions := [.definition { validSignature with name := "" } [{ label := "bad label", terminator := some (.ret (some (.integer 32 2))) }]] }
  let badCall := NecoLean.Llvm.validate { functions := [.declaration (llvmSignature "printf" (.integer 32) [cStringPointer] true), .definition validSignature [{ label := "entry", instructions := [.call none (globalFunctionOperand "printf" (.integer 32) [cStringPointer] true) []], terminator := some (.ret (some (.integer 32 2))) }]] }
  let badBranch := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.branch "missing") }]] }
  let expectedBadBranchTerminator : NecoLean.Llvm.Terminator := .branch "missing"
  let badCondition := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.integer 32 1) (.integer 32 2)], terminator := some (.condBranch (.local ⟨0⟩ (.integer 32)) "entry" "entry") }]] }
  let badGlobal := NecoLean.Llvm.validate { globals := [{ name := "fmt", value := "x" }], functions := [.definition validSignature [{ label := "entry", instructions := [.call none (globalFunctionOperand "missing" (.integer 32) [.pointer none] true) [.globalString "fmt" (globalStringPointer "x")]], terminator := some (.ret (some (.integer 32 2))) }]] }
  let undefinedLocal := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.ret (some (.local ⟨9⟩ (.integer 32)))) }]] }
  let entryLeftRight := { label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") }
  let left := { label := "left", instructions := [.add ⟨0⟩ 32 (.integer 32 1) (.integer 32 2)], terminator := some (.branch "join") }
  let right := { label := "right", terminator := some (.branch "join") }
  let join := { label := "join", terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }
  let siblingUse := NecoLean.Llvm.validate { functions := [.definition validSignature [entryLeftRight, left, right, join]] }
  let definitionBeforeUse := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.local ⟨1⟩ (.integer 32)) (.integer 32 1), .add ⟨1⟩ 32 (.integer 32 1) (.integer 32 2)], terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]] }
  let sparseDefinition := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨1000000⟩ 32 (.integer 32 1) (.integer 32 2)], terminator := some (.ret (some (.local ⟨1000000⟩ (.integer 32)))) }]] }
  let duplicateBlockLabel := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }, { label := "entry", instructions := [.add ⟨0⟩ 32 (.integer 64 1) (.integer 32 2)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let duplicateResultBeforeInvalidInstruction := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.integer 32 1) (.integer 32 2), .add ⟨0⟩ 32 (.integer 64 1) (.integer 32 2)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let invalidInstructionBeforeInvalidTerminator := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.integer 64 1) (.integer 32 2)], terminator := some (.branch "missing") }]] }
  let emptyFunction := NecoLean.Llvm.validate { functions := [.declaration (llvmSignature "" (.integer 32) [])] }
  let sdivMismatch := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.integer 64] } } [{ label := "entry", instructions := [.sdiv ⟨0⟩ 64 (.parameter 0 (.integer 64)) (.integer 32 2)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let sremMismatch := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.integer 64] } } [{ label := "entry", instructions := [.srem ⟨0⟩ 64 (.parameter 0 (.integer 64)) (.integer 32 2)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let icmpSltMismatch := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.integer 64] } } [{ label := "entry", instructions := [.icmpSlt ⟨0⟩ 64 (.parameter 0 (.integer 64)) (.integer 32 2)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let unreachable := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some .unreachable }]] }
  let signedEncoding :=
    let signedModule : NecoLean.Llvm.Module :=
      { functions := [.definition (llvmSignature "signed" (.integer 64) [])
          [{ label := "entry",
             instructions := [.sdiv ⟨0⟩ 64 (.integer 64 (-7)) (.integer 64 2), .srem ⟨1⟩ 64 (.integer 64 (-7)) (.integer 64 2), .icmpSlt ⟨2⟩ 64 (.integer 64 (-7)) (.integer 64 2)],
             terminator := some (.ret (some (.local ⟨0⟩ (.integer 64)))) }]] }
    match NecoLean.Llvm.validate signedModule with
    | .ok valid =>
      let text := String.fromUTF8! (NecoLean.Llvm.encode valid)
      text.contains "sdiv i64 -7" && text.contains "srem i64 -7" && text.contains "icmp slt i64 -7"
    | .error _ => false
  let joinAndCast := NecoLean.Llvm.validate joinAndCastModule
  let missingPhi := NecoLean.Llvm.validate { joinAndCastModule with functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", instructions := [.zext ⟨0⟩ (.integer 8 1) 32], terminator := some (.branch "join") }, { label := "right", instructions := [.sext ⟨1⟩ (.integer 8 (-1)) 32], terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨2⟩ (.integer 32) [("left", .local ⟨0⟩ (.integer 32))]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let invalidPhiBeforeInvalidTerminator := NecoLean.Llvm.validate { joinAndCastModule with functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", instructions := [.zext ⟨0⟩ (.integer 8 1) 32], terminator := some (.branch "join") }, { label := "right", instructions := [.sext ⟨1⟩ (.integer 8 (-1)) 32], terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨2⟩ (.integer 32) [("left", .local ⟨0⟩ (.integer 32))]], terminator := some (.branch "missing") }]] }
  let multiplePhiInvalid := NecoLean.Llvm.validate { joinAndCastModule with functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", instructions := [.zext ⟨0⟩ (.integer 8 1) 32], terminator := some (.branch "join") }, { label := "right", instructions := [.sext ⟨1⟩ (.integer 8 (-1)) 32], terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨2⟩ (.integer 32) [("left", .local ⟨0⟩ (.integer 32)), ("right", .local ⟨1⟩ (.integer 32))], .phi ⟨3⟩ (.integer 32) [("left", .local ⟨9⟩ (.integer 32)), ("right", .local ⟨9⟩ (.integer 32))]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nonLeadingPhiInvalid := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.integer 32 1) (.integer 32 2), .phi ⟨1⟩ (.integer 32) []], terminator := some (.ret (some (.local ⟨0⟩ (.integer 32)))) }]] }
  let duplicatePhi := NecoLean.Llvm.validate { joinAndCastModule with functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", instructions := [.zext ⟨0⟩ (.integer 8 1) 32], terminator := some (.branch "join") }, { label := "right", instructions := [.sext ⟨1⟩ (.integer 8 (-1)) 32], terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨2⟩ (.integer 32) [("left", .local ⟨0⟩ (.integer 32)), ("left", .local ⟨0⟩ (.integer 32))]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let unavailablePhi := NecoLean.Llvm.validate { joinAndCastModule with functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", instructions := [.zext ⟨0⟩ (.integer 8 1) 32], terminator := some (.branch "join") }, { label := "right", instructions := [.sext ⟨1⟩ (.integer 8 (-1)) 32], terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨2⟩ (.integer 32) [("left", .local ⟨1⟩ (.integer 32)), ("right", .local ⟨1⟩ (.integer 32))]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let phiTypeMismatch := NecoLean.Llvm.validate { joinAndCastModule with functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", instructions := [.zext ⟨0⟩ (.integer 8 1) 32], terminator := some (.branch "join") }, { label := "right", instructions := [.sext ⟨1⟩ (.integer 8 (-1)) 32], terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨2⟩ (.integer 64) [("left", .local ⟨0⟩ (.integer 32)), ("right", .local ⟨1⟩ (.integer 32))]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badCast := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.zext ⟨0⟩ (.integer 32 1) 8], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badSext := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.sext ⟨0⟩ (.integer 32 1) 8], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badTrunc := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.trunc ⟨0⟩ (.integer 8 1) 32], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badArray := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.array .void 4)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badStructVoid := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.struct [.void])], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badStructFunction := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.struct [functionPointerType (.integer 32) [.void]])], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badGep := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.getElementPtr ⟨0⟩ (.integer 32 0) [.integer 32 0]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badGepElementType := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.integer 32), .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.integer 32)))) [.integer 32 0, .integer 32 1]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badStructGepWidth := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.struct [(.integer 8)]), .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.struct [(.integer 8)])))) [.integer 32 0, .integer 64 0]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badStructGepNegative := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.struct [(.integer 8)]), .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.struct [(.integer 8)])))) [.integer 32 0, .integer 32 (-1)]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badStructGepOutOfRange := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.struct [(.integer 8)]), .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.struct [(.integer 8)])))) [.integer 32 0, .integer 32 1]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let badSwitch := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.switch (.integer 8 0) "exit" [(.integer 8 1, "exit"), (.integer 8 1, "entry")]) }, { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }
  let badSwitchWidth := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.switch (.integer 8 0) "exit" [(.integer 16 1, "exit")]) }, { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }
  let duplicateSwitchTarget := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.switch (.integer 8 0) "exit" [(.integer 8 1, "exit"), (.integer 8 2, "exit")]) }, { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }
  let missingSwitchDefault := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.switch (.integer 8 0) "missing" [(.integer 8 1, "exit")]) }, { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }
  let missingSwitchCase := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.switch (.integer 8 0) "exit" [(.integer 8 1, "missing")]) }, { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }
  let localSwitchCase := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 8 (.integer 8 1) (.integer 8 2)], terminator := some (.switch (.integer 8 0) "exit" [(.local ⟨0⟩ (.integer 8), "exit")]) }, { label := "exit", terminator := some (.ret (some (.integer 32 0))) }]] }
  let invalidTriple := NecoLean.Llvm.validate { (validModule 0) with targetTriple := some "x86_64-linux-gnu extra" }
  let invalidTripleNewline := NecoLean.Llvm.validate { (validModule 0) with targetTriple := some "x86_64-unknown-linux\ngnu" }
  let invalidTripleQuote := NecoLean.Llvm.validate { (validModule 0) with targetTriple := some "x86_64-\"unknown-linux" }
  let invalidTriplePunctuation := NecoLean.Llvm.validate { (validModule 0) with targetTriple := some "x86_64-unknown-linux/gnu" }
  let invalidTripleCount := NecoLean.Llvm.validate { (validModule 0) with targetTriple := some "x86_64-linux" }
  let validTriples := ["x86_64-unknown-linux-gnu", "arm64-apple-darwin"].all (fun triple => match NecoLean.Llvm.validate { (validModule 0) with targetTriple := some triple } with | .ok _ => true | _ => false)
  let voidResultLocal := NecoLean.Llvm.validate { functions := [.declaration (llvmSignature "abort" .void []), .definition validSignature [{ label := "entry", instructions := [.call (some ⟨0⟩) (globalFunctionOperand "abort" .void []) []], terminator := some (.ret (some (.integer 32 0))) }]] }
  let rawPointerLoad := NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [.pointer none]) [{ label := "entry", instructions := [.load ⟨0⟩ (.parameter 0 (.pointer none))], terminator := some (.ret (some (.integer 32 0))) }]] }
  let rawPointerStore := NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [.pointer none]) [{ label := "entry", instructions := [.store (.integer 32 0) (.parameter 0 (.pointer none))], terminator := some (.ret (some (.integer 32 0))) }]] }
  let rawPointerGetElementPtr := NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [.pointer none]) [{ label := "entry", instructions := [.getElementPtr ⟨0⟩ (.parameter 0 (.pointer none)) [.integer 32 0]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let rawPointerCall := NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [.pointer none]) [{ label := "entry", instructions := [.call none (.parameter 0 (.pointer none)) []], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullRawLoad := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.load ⟨0⟩ (.null (.pointer none))], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullRawStore := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.store (.integer 32 0) (.null (.pointer none))], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullRawGetElementPtr := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.getElementPtr ⟨0⟩ (.null (.pointer none)) [.integer 32 0]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullRawCall := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.call none (.null (.pointer none)) []], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullInteger := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.null (.integer 32)) (.integer 32 0)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullVoidPointee := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.call none (globalFunctionOperand "consume" (.integer 32) [(.pointer (some .void))]) [(.null (.pointer (some .void)))]] , terminator := some (.ret (some (.integer 32 0))) }]] }
  let nullFunctionPointer := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 32 (.null (functionPointerType (.integer 32) [])) (.integer 32 0)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let forgedGlobalFunction := NecoLean.Llvm.validate { functions := [.definition (llvmSignature "target" (.integer 32) []) [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }], .definition validSignature [{ label := "entry", instructions := [.call (some ⟨0⟩) (globalFunctionOperand "target" (.integer 64) []) []], terminator := some (.ret (some (.integer 32 0))) }]] }
  let nonVariadicExtraArguments := NecoLean.Llvm.validate { functions := [.declaration (llvmSignature "one" (.integer 32) [(.integer 32)]), .definition validSignature [{ label := "entry", instructions := [.call none (globalFunctionOperand "one" (.integer 32) [(.integer 32)]) [(.integer 32 1), (.integer 32 2)]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let voidPointee := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.pointer (some .void)] } } [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }]] }
  let voidFunctionParameter := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [functionPointerType (.integer 32) [.void]] } } [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }]] }
  let nestedArrayVoidPointee := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [.array (.pointer (some .void)) 1] } } [{ label := "entry", terminator := some (.ret (some (.integer 32 0))) }]] }
  let allocatorStructStoreMismatch := NecoLean.Llvm.validate allocatorStructStoreMismatchModule
  let functionPointerStoreMismatch :=
    let storedType := functionPointerType (.integer 32) [(.integer 32)]
    let valueType := functionPointerType (.integer 32) [(.integer 64)]
    NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [valueType]) [{ label := "entry", instructions := [.alloca ⟨0⟩ storedType, .store (.parameter 0 valueType) (.local ⟨0⟩ (.pointer (some storedType)))], terminator := some (.ret (some (.integer 32 0))) }]] }
  let forgedLoadResultType :=
    let storedType := functionPointerType (.integer 32) [(.integer 32)]
    let forgedType := functionPointerType (.integer 32) [(.integer 64)]
    NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [storedType]) [{ label := "entry", instructions := [.alloca ⟨0⟩ storedType, .store (.parameter 0 storedType) (.local ⟨0⟩ (.pointer (some storedType))), .load ⟨1⟩ (.local ⟨0⟩ (.pointer (some storedType))), .call none (.local ⟨1⟩ forgedType) [(.integer 64 1)]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let functionPointerPhiMismatch :=
    let firstType := functionPointerType (.integer 32) [(.integer 32)]
    let secondType := functionPointerType (.integer 32) [(.integer 64)]
    NecoLean.Llvm.validate { functions := [.definition (llvmSignature "main" (.integer 32) [firstType, secondType]) [{ label := "entry", terminator := some (.condBranch (.integer 1 0) "left" "right") }, { label := "left", terminator := some (.branch "join") }, { label := "right", terminator := some (.branch "join") }, { label := "join", instructions := [.phi ⟨0⟩ firstType [("left", .parameter 0 firstType), ("right", .parameter 1 secondType)]], terminator := some (.ret (some (.integer 32 0))) }]] }
  let runtimeSourceNameFailures :=
    [NecoLean.Llvm.RuntimeSource.create "/abs.c" .compilationUnit ByteArray.empty,
     NecoLean.Llvm.RuntimeSource.create ".." .header ByteArray.empty].all (fun result => match result with | .error (.invalidRuntimeSourceName _ _) => true | _ => false)
  let invalids := [badFloatOperand, badFcmpOperand, duplicate, zero, operandMismatch, returnMismatch, missingTerminator, invalidGlobalName, invalidNames, badCall, badBranch, badCondition, badGlobal, undefinedLocal, siblingUse, definitionBeforeUse, duplicateBlockLabel, emptyFunction, sdivMismatch, sremMismatch, icmpSltMismatch, missingPhi, duplicatePhi, unavailablePhi, phiTypeMismatch, badCast, badSext, badTrunc, badArray, badStructVoid, badStructFunction, badGep, badGepElementType, badStructGepWidth, badStructGepNegative, badStructGepOutOfRange, badSwitch, badSwitchWidth, duplicateSwitchTarget, missingSwitchDefault, missingSwitchCase, localSwitchCase, voidResultLocal, rawPointerLoad, rawPointerStore, rawPointerGetElementPtr, rawPointerCall, nullRawLoad, nullRawStore, nullRawGetElementPtr, nullRawCall, nullInteger, nullVoidPointee, nullFunctionPointer, forgedGlobalFunction, nonVariadicExtraArguments, voidPointee, voidFunctionParameter, nestedArrayVoidPointee, functionPointerStoreMismatch, forgedLoadResultType, functionPointerPhiMismatch, invalidTriple, invalidTripleNewline, invalidTripleQuote, invalidTriplePunctuation, invalidTripleCount]
  let invalidFloatPassed := invalidFloatModules.all (fun module => match NecoLean.Llvm.validate module with | .error (.invalidModule _) => true | _ => false)
  let truthTableValidation := NecoLean.Llvm.validate fcmpTruthTableModule
  let floatArrayValidation := NecoLean.Llvm.validate floatArrayModule
  let callableTransportValidation := NecoLean.Llvm.validate callableTransportModule
  let runtimeSourceValidation := NecoLean.Llvm.validate runtimeSourceModule
  let rawPointerSlotValidation := NecoLean.Llvm.validate rawPointerSlotModule
  let nullTransportValidation := NecoLean.Llvm.validate nullTransportModule
  let nullPhiReturnValidation := NecoLean.Llvm.validate nullPhiReturnModule
  let allocatorStructValidation := NecoLean.Llvm.validate allocatorStructModule
  let gepNonZeroFirstIndexValidation := NecoLean.Llvm.validate gepNonZeroFirstIndexModule
  let structGepValidation := NecoLean.Llvm.validate structGepModule
  let callableStructGepValidation := NecoLean.Llvm.validate callableStructGepModule
  let i8Underflow := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 8 (.integer 8 (-129)) (.integer 8 1)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let i8Overflow := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 8 (.integer 8 128) (.integer 8 1)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let i64Underflow := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.add ⟨0⟩ 64 (.integer 64 (-9223372036854775809)) (.integer 64 1)], terminator := some (.ret (some (.integer 32 0))) }]] }
  let invalidsWithAllocator := invalids ++ [allocatorStructStoreMismatch] ++ ([nullPhiTypeMismatchModule, nullReturnTypeMismatchModule].map NecoLean.Llvm.validate) ++ [i8Underflow, i8Overflow, i64Underflow]
  let invalidPassed := invalidsWithAllocator.all (fun result => match result with | .error (.invalidModule _) => true | _ => false)
  let expectedMissingPhiInstruction : NecoLean.Llvm.Instruction := .phi ⟨2⟩ (.integer 32) [("left", .local ⟨0⟩ (.integer 32))]
  let expectedMultiplePhiInstruction : NecoLean.Llvm.Instruction := .phi ⟨3⟩ (.integer 32) [("left", .local ⟨9⟩ (.integer 32)), ("right", .local ⟨9⟩ (.integer 32))]
  let expectedNonLeadingPhiInstruction : NecoLean.Llvm.Instruction := .add ⟨0⟩ 32 (.integer 32 1) (.integer 32 2)
  let validationLocationPassed :=
    let instructionLocation := match operandMismatch with
      | .error (.invalidModule message) =>
        message.contains "functionIndex=0" && message.contains "function=main" && message.contains "stage=instruction" && message.contains "blockIndex=0" && message.contains "block=entry" && message.contains "instructionIndex=0" && message.contains s!"instruction={repr expectedOperandMismatchInstruction}"
      | _ => false
    let terminatorLocation := match badBranch with
      | .error (.invalidModule message) =>
        message.contains "functionIndex=0" && message.contains "function=main" && message.contains "stage=terminator" && message.contains "blockIndex=0" && message.contains "block=entry" && message.contains s!"terminator={repr expectedBadBranchTerminator}"
      | _ => false
    let missingTerminatorLocation := match missingTerminatorLater with
      | .error (.invalidModule message) =>
        message.contains "functionIndex=1" && message.contains "function=main" && message.contains "stage=missing-terminator" && message.contains "blockIndex=0" && message.contains "block=entry"
      | _ => false
    let phiLocation := match missingPhi with
      | .error (.invalidModule message) =>
        message.contains "stage=phi" && message.contains "blockIndex=3" && message.contains "block=join" && message.contains "instructionIndex=0" && message.contains s!"instruction={repr expectedMissingPhiInstruction}"
      | _ => false
    let laterPhiLocation := match multiplePhiInvalid with
      | .error (.invalidModule message) =>
        message.contains "stage=phi" && message.contains "blockIndex=3" && message.contains "block=join" && message.contains "instructionIndex=1" && message.contains s!"instruction={repr expectedMultiplePhiInstruction}"
      | _ => false
    let nonLeadingPhiLocation := match nonLeadingPhiInvalid with
      | .error (.invalidModule message) =>
        message.contains "stage=phi" && message.contains "blockIndex=0" && message.contains "block=entry" && message.contains "instructionIndex=0" && message.contains s!"instruction={repr expectedNonLeadingPhiInstruction}"
      | _ => false
    instructionLocation && terminatorLocation && missingTerminatorLocation && phiLocation && laterPhiLocation && nonLeadingPhiLocation
  let definitionIndexPassed :=
    let sparseAccepted := match sparseDefinition with
      | .ok _ => true
      | _ => false
    let undefinedRejected := match undefinedLocal with
      | .error (.invalidModule message) =>
        message.contains "stage=terminator" && message.contains "blockIndex=0" && message.contains "block=entry"
      | _ => false
    let forwardRejected := match definitionBeforeUse with
      | .error (.invalidModule message) =>
        message.contains "stage=instruction" && message.contains "blockIndex=0" && message.contains "instructionIndex=0"
      | _ => false
    let siblingRejected := match siblingUse with
      | .error (.invalidModule message) =>
        message.contains "stage=terminator" && message.contains "blockIndex=3" && message.contains "block=join"
      | _ => false
    let duplicateFirst := match duplicateResultBeforeInvalidInstruction with
      | .error (.invalidModule message) => message.contains "stage=duplicate-result" && message.contains "result="
      | _ => false
    let duplicateBlockLabelFirst := match duplicateBlockLabel with
      | .error (.invalidModule message) => message.contains "stage=duplicate-block-label" && message.contains "block=entry"
      | _ => false
    let instructionFirst := match invalidInstructionBeforeInvalidTerminator with
      | .error (.invalidModule message) =>
        message.contains "stage=instruction" && message.contains "blockIndex=0" && message.contains "instructionIndex=0"
      | _ => false
    let phiFirst := match invalidPhiBeforeInvalidTerminator with
      | .error (.invalidModule message) =>
        message.contains "stage=phi" && message.contains "blockIndex=3" && message.contains "block=join" && message.contains "instructionIndex=0"
      | _ => false
    sparseAccepted && undefinedRejected && forwardRejected && siblingRejected && duplicateFirst && duplicateBlockLabelFirst && instructionFirst && phiFirst
  let dominatorCost ← dominatorCostCheck
  let integerRange :=
    let i1Good := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "yes" "no") }, { label := "yes", terminator := some (.ret (some (.integer 32 0))) }, { label := "no", terminator := some (.ret (some (.integer 32 0))) }]] }
    let i1BadNegative := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", terminator := some (.condBranch (.integer 1 (-1)) "yes" "no") }, { label := "yes", terminator := some (.ret (some (.integer 32 0))) }, { label := "no", terminator := some (.ret (some (.integer 32 0))) }]] }
    let i1Bad := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [] } } [{ label := "entry", terminator := some (.ret (some (.integer 1 2))) }]] }
    let i64Overflow := NecoLean.Llvm.validate { functions := [.definition { validSignature with callable := { validSignature.callable with parameters := [] } } [{ label := "entry", terminator := some (.ret (some (.integer 64 9223372036854775808))) }]] }
    let endpoints := NecoLean.Llvm.validIntegerValue 1 0 && NecoLean.Llvm.validIntegerValue 1 1 && !NecoLean.Llvm.validIntegerValue 1 (-1) && !NecoLean.Llvm.validIntegerValue 1 2 && NecoLean.Llvm.validIntegerValue 8 (-128) && NecoLean.Llvm.validIntegerValue 8 127 && NecoLean.Llvm.validIntegerValue 64 (-9223372036854775808) && NecoLean.Llvm.validIntegerValue 64 9223372036854775807 && !NecoLean.Llvm.validIntegerValue 0 0 && !NecoLean.Llvm.validIntegerValue 129 0
    let i1Encoding := match i1Good with | .ok valid => (String.fromUTF8! (NecoLean.Llvm.encode valid)).contains "br i1 true" | _ => false
    endpoints && i1Encoding && match i1Good, i1BadNegative, i1Bad, i64Overflow with | .ok _, .error (.invalidModule _), .error (.invalidModule _), .error (.invalidModule _) => true | _, _, _, _ => false
  let joinEncoding := match joinAndCast with
    | .ok valid =>
      let text := String.fromUTF8! (NecoLean.Llvm.encode valid)
      text.contains "alloca [4 x i32]" && text.contains "phi i32 [ %r2, %left ], [ %r3, %right ]" && text.contains "switch i8 0, label %exit" && text.contains "zext i8 1 to i32" && text.contains "sext i8 -1 to i32" && text.contains "trunc i32 %r4 to i8" && text.contains "getelementptr [4 x i32], ptr %r0, i32 0, i32 1"
    | .error _ => false
  let gepPointerResult := NecoLean.Llvm.validate { functions := [.definition validSignature [{ label := "entry", instructions := [.alloca ⟨0⟩ (.integer 32), .getElementPtr ⟨1⟩ (.local ⟨0⟩ (.pointer (some (.integer 32)))) [.integer 32 0], .load ⟨2⟩ (.local ⟨1⟩ (.pointer (some (.integer 32))))], terminator := some (.ret (some (.local ⟨2⟩ (.integer 32)))) }]] }
  let structEncoding := match structGepValidation with
    | .ok valid =>
      let text := String.fromUTF8! (NecoLean.Llvm.encode valid)
      text.contains "alloca { [4 x i8], {} }" && text.contains "getelementptr { [4 x i8], {} }, ptr %r0, i32 0, i32 0, i32 2" && text.contains "getelementptr { [4 x i8], {} }, ptr %r0, i32 0, i32 1"
    | .error _ => false
  let callableStructEncoding := match callableStructGepValidation with
    | .ok valid =>
      let text := String.fromUTF8! (NecoLean.Llvm.encode valid)
      text.contains "alloca { [1 x { ptr }] }" && text.contains "getelementptr { [1 x { ptr }] }, ptr %r0, i32 0, i32 0, i32 0, i32 0" && text.contains "call i32 %r2(i32 41)"
    | .error _ => false
  let nullPhiReturnEncoding := match nullPhiReturnValidation with
    | .ok valid =>
      let text := String.fromUTF8! (NecoLean.Llvm.encode valid)
      text.contains "define ptr @raw_phi" && text.contains "define ptr @typed_phi" && text.contains "phi ptr [ null, %left ], [ null, %right ]" && text.contains "ret ptr %r0"
    | .error _ => false
  let floatEncoding := match floatValidation with
    | .ok valid =>
      let text := String.fromUTF8! (NecoLean.Llvm.encode valid)
      text.contains "0x3FF0000000000000" && text.contains "0x7FF8000000000001" && ["false", "oeq", "ogt", "oge", "olt", "ole", "one", "ord", "uno", "ueq", "ugt", "uge", "ult", "ule", "une", "true"].all (fun predicate => text.contains s!"fcmp {predicate} double") && !text.contains "fast"
    | .error _ => false
  let mustTailPassed ← llvmMustTailCheck
  let passed := reachableProjection && dominatorCost && mustTailPassed && runtimeSourceNameFailures && invalidPassed && validationLocationPassed && definitionIndexPassed && invalidFloatPassed && (match truthTableValidation with | .ok _ => true | _ => false) && (match floatArrayValidation with | .ok _ => true | _ => false) && (match callableTransportValidation with | .ok _ => true | _ => false) && (match runtimeSourceValidation with | .ok _ => true | _ => false) && (match rawPointerSlotValidation with | .ok _ => true | _ => false) && (match nullTransportValidation with | .ok _ => true | _ => false) && (match nullPhiReturnValidation with | .ok _ => true | _ => false) && (match allocatorStructValidation with | .ok _ => true | _ => false) && (match gepNonZeroFirstIndexValidation with | .ok _ => true | _ => false) && (match structGepValidation with | .ok _ => true | _ => false) && (match callableStructGepValidation with | .ok _ => true | _ => false) && validTriples && integerRange && (match unreachable with | .ok _ => true | _ => false) && signedEncoding && joinEncoding && (match floatValidation with | .ok _ => true | _ => false) && floatEncoding && (match gepPointerResult with | .ok _ => true | _ => false) && structEncoding && callableStructEncoding && nullPhiReturnEncoding
  if !passed then
    IO.println s!"llvm-validation detail: invalids={invalidPassed} struct={match structGepValidation with | .ok _ => true | _ => false} callableStruct={match callableStructGepValidation with | .ok _ => true | _ => false} structEncoding={structEncoding} callableEncoding={callableStructEncoding}"
  report "llvm-validation" passed "LLVM triple, join, cast, array, getelementptr, switch, or validation mismatch"

private def llvmPointerEqualityCheck : IO Bool := do
  let rawPointer : NecoLean.Llvm.ValueType := .pointer none
  let typedPointer : NecoLean.Llvm.ValueType := .pointer (some (.integer 32))
  let nullNullModule : NecoLean.Llvm.Module :=
    { functions := [.definition (llvmSignature "null_null" (.integer 1) [])
        [{ label := "entry",
           instructions := [.icmpPtrEq ⟨0⟩ (.null rawPointer) (.null rawPointer)],
           terminator := some (.ret (some (.local ⟨0⟩ (.integer 1)))) }]] }
  let nullNonNullModule : NecoLean.Llvm.Module :=
    { functions := [.definition (llvmSignature "null_nonnull" (.integer 1) [typedPointer])
        [{ label := "entry",
           instructions := [.icmpPtrEq ⟨0⟩ (.null typedPointer) (.parameter 0 typedPointer)],
           terminator := some (.ret (some (.local ⟨0⟩ (.integer 1)))) }]] }
  let localLocalModule : NecoLean.Llvm.Module :=
    { functions := [.definition (llvmSignature "local_local" (.integer 1) [])
        [{ label := "entry",
           instructions := [.alloca ⟨0⟩ (.integer 32), .alloca ⟨1⟩ (.integer 32),
             .icmpPtrEq ⟨2⟩ (.local ⟨0⟩ (.pointer (some (.integer 32))))
               (.local ⟨1⟩ (.pointer (some (.integer 32))))],
           terminator := some (.ret (some (.local ⟨2⟩ (.integer 1)))) }]] }
  let integerOperands := NecoLean.Llvm.validate
    { functions := [.definition (llvmSignature "integer_operands" (.integer 1) [])
        [{ label := "entry",
           instructions := [.icmpPtrEq ⟨0⟩ (.integer 32 0) (.integer 32 0)],
           terminator := some (.ret (some (.integer 1 0))) }]] }
  let undefinedLocal := NecoLean.Llvm.validate
    { functions := [.definition (llvmSignature "undefined_local" (.integer 1) [])
        [{ label := "entry",
           instructions := [.icmpPtrEq ⟨0⟩ (.local ⟨9⟩ rawPointer) (.null rawPointer)],
           terminator := some (.ret (some (.integer 1 0))) }]] }
  let validResults := [nullNullModule, nullNonNullModule, localLocalModule].map NecoLean.Llvm.validate
  let validPassed := validResults.all (fun result => match result with | .ok _ => true | _ => false)
  let invalidPassed := [integerOperands, undefinedLocal].all
    (fun result => match result with | .error (.invalidModule _) => true | _ => false)
  let deterministic := match NecoLean.Llvm.validate nullNullModule with
    | .ok valid =>
        let first := NecoLean.Llvm.encode valid
        let second := NecoLean.Llvm.encode valid
        first == second && (String.fromUTF8! first).contains "icmp eq ptr null, null"
    | .error _ => false
  report "llvm-pointer-equality" (validPassed && invalidPassed && deterministic)
    "pointer equality validation, SSA checks, or deterministic encoding mismatch"

private def scalarInstructionModule (instructions : List NecoLean.Llvm.Instruction) : NecoLean.Llvm.Module :=
  { functions := [.definition validSignature
      [{ label := "entry", instructions, terminator := some (.ret (some (.integer 32 0))) }]] }

private def scalarInstructionExecutionModule : NecoLean.Llvm.Module :=
  let patterns : List Int :=
    [0, -9223372036854775808, 4607182418800017408,
     9218868437227405312, 9221120237041090626]
  let casts := (patterns.mapIdx (fun index bits =>
    let floatResult : NecoLean.Llvm.ResultId := ⟨6 + 2 * index⟩
    let roundtripResult : NecoLean.Llvm.ResultId := ⟨7 + 2 * index⟩
    [.bitcast floatResult (.integer 64 bits) .float64,
     .bitcast roundtripResult (.local floatResult .float64) (.integer 64)])).flatten
  let integerChecks : List NecoLean.Llvm.Instruction :=
    [.icmpEq ⟨16⟩ 64 (.local ⟨0⟩ (.integer 64)) (.integer 64 10),
     .icmpEq ⟨17⟩ 64 (.local ⟨1⟩ (.integer 64)) (.integer 64 15),
     .icmpEq ⟨18⟩ 64 (.local ⟨2⟩ (.integer 64)) (.integer 64 12),
     .icmpEq ⟨19⟩ 64 (.local ⟨3⟩ (.integer 64)) (.integer 64 24),
     .icmpEq ⟨20⟩ 64 (.local ⟨4⟩ (.integer 64)) (.integer 64 6),
     .icmpEq ⟨21⟩ 64 (.local ⟨5⟩ (.integer 64)) (.integer 64 (-2))]
  let patternChecks := patterns.mapIdx (fun index bits =>
    .icmpEq ⟨22 + index⟩ 64 (.local ⟨7 + 2 * index⟩ (.integer 64)) (.integer 64 bits))
  let conjunctions : List NecoLean.Llvm.Instruction :=
    (List.range (integerChecks.length + patternChecks.length)).map (fun index =>
      .bitAnd ⟨40 + index⟩ 1
        (if index == 0 then .integer 1 1 else .local ⟨39 + index⟩ (.integer 1))
        (.local ⟨16 + index⟩ (.integer 1)))
  { functions := [.definition validSignature
      [{ label := "entry",
         instructions :=
           [.bitAnd ⟨0⟩ 64 (.integer 64 14) (.integer 64 11),
            .bitOr ⟨1⟩ 64 (.local ⟨0⟩ (.integer 64)) (.integer 64 5),
            .bitXor ⟨2⟩ 64 (.local ⟨1⟩ (.integer 64)) (.integer 64 3),
            .shl ⟨3⟩ 64 (.local ⟨2⟩ (.integer 64)) (.integer 64 1),
            .lshr ⟨4⟩ 64 (.local ⟨3⟩ (.integer 64)) (.integer 64 2),
            .ashr ⟨5⟩ 64 (.integer 64 (-8)) (.integer 64 2)] ++
           casts ++ integerChecks ++ patternChecks ++ conjunctions ++
           [.zext ⟨51⟩ (.local ⟨50⟩ (.integer 1)) 32,
            .sub ⟨52⟩ 32 (.integer 32 1) (.local ⟨51⟩ (.integer 32))],
         terminator := some (.ret (some (.local ⟨52⟩ (.integer 32)))) }]] }

private def scalarIntegerConstructors : List (Nat → NecoLean.Llvm.Operand → NecoLean.Llvm.Operand → NecoLean.Llvm.Instruction) :=
  [.bitAnd ⟨0⟩, .bitOr ⟨0⟩, .bitXor ⟨0⟩, .shl ⟨0⟩, .lshr ⟨0⟩, .ashr ⟨0⟩]

private def scalarValidationPassed : Bool :=
  let integerConstructors := scalarIntegerConstructors
  let invalidOperandPairs : List (NecoLean.Llvm.Operand × NecoLean.Llvm.Operand) :=
    [(.integer 32 1, .integer 64 1),
     (.integer 64 1, .integer 32 1),
     (.float64 0, .integer 64 1),
     (.integer 64 1, .float64 0),
     (.null (.pointer none), .integer 64 1),
     (.integer 64 1, .null (.pointer none))]
  let invalidInstructions : List NecoLean.Llvm.Instruction :=
    integerConstructors.flatMap (fun constructor =>
      invalidOperandPairs.map (fun pair => constructor 64 pair.1 pair.2) ++
        [constructor 0 (.integer 1 1) (.integer 1 1),
         constructor 129 (.integer 64 1) (.integer 64 1)]) ++
    [
     .bitcast ⟨0⟩ (.integer 32 1) .float64,
     .bitcast ⟨0⟩ (.float64 0) (.integer 32),
     .bitcast ⟨0⟩ (.null (.pointer none)) (.integer 64),
     .bitcast ⟨0⟩ (.integer 64 1) (.integer 64),
     .bitAnd ⟨0⟩ 64 (.local ⟨9⟩ (.integer 64)) (.integer 64 1),
     .bitcast ⟨0⟩ (.local ⟨9⟩ (.integer 64)) .float64]
  let invalid := invalidInstructions.all (fun instruction =>
    match NecoLean.Llvm.validate (scalarInstructionModule [instruction]) with
    | .error (.invalidModule message) => message.contains "stage=instruction"
    | _ => false)
  let invalidResultUses : List (List NecoLean.Llvm.Instruction) :=
    integerConstructors.map (fun constructor =>
      [constructor 64 (.integer 64 3) (.integer 64 1),
       .bitAnd ⟨1⟩ 32 (.local ⟨0⟩ (.integer 32)) (.integer 32 1)]) ++
    [[.bitcast ⟨0⟩ (.integer 64 4607182418800017408) .float64,
      .bitAnd ⟨1⟩ 64 (.local ⟨0⟩ (.integer 64)) (.integer 64 1)],
     [.bitcast ⟨0⟩ (.float64 0x3FF0000000000000) (.integer 64),
      .fneg ⟨1⟩ (.local ⟨0⟩ .float64)]]
  let resultTypes := invalidResultUses.all (fun instructions =>
    match NecoLean.Llvm.validate (scalarInstructionModule instructions) with
    | .error (.invalidModule message) => message.contains "stage=instruction"
    | _ => false)
  let dominance := match NecoLean.Llvm.validate (scalarInstructionModule
      [.bitcast ⟨0⟩ (.local ⟨1⟩ (.integer 64)) .float64,
       .bitAnd ⟨1⟩ 64 (.integer 64 1) (.integer 64 1)]) with
    | .error (.invalidModule message) => message.contains "stage=instruction"
    | _ => false
  invalid && resultTypes && dominance &&
    match NecoLean.Llvm.validate scalarInstructionExecutionModule with
    | .ok _ => true
    | .error _ => false

private def scalarDeterminismPassed : Bool :=
  let integerConstructors := scalarIntegerConstructors
  let valid := NecoLean.Llvm.validate scalarInstructionExecutionModule
  let perOpcode := (integerConstructors.zip ["and", "or", "xor", "shl", "lshr", "ashr"]).all
      (fun (constructor, opcode) =>
        match NecoLean.Llvm.validate (scalarInstructionModule
            [constructor 64 (.integer 64 3) (.integer 64 1)]) with
        | .ok module =>
          let first := NecoLean.Llvm.encode module
          first == NecoLean.Llvm.encode module &&
            (String.fromUTF8! first).contains s!" = {opcode} i64 3, 1"
        | .error _ => false) &&
    ([.bitcast ⟨0⟩ (.integer 64 4607182418800017408) .float64,
      .bitcast ⟨0⟩ (.float64 0x3FF0000000000000) (.integer 64)] :
      List NecoLean.Llvm.Instruction).all (fun instruction =>
        match NecoLean.Llvm.validate (scalarInstructionModule [instruction]) with
        | .ok module =>
          let first := NecoLean.Llvm.encode module
          first == NecoLean.Llvm.encode module &&
            (String.fromUTF8! first).contains " = bitcast "
        | .error _ => false)
  let rendered := match valid with
    | .ok module =>
      let first := NecoLean.Llvm.encode module
      let second := NecoLean.Llvm.encode module
      let ir := String.fromUTF8! first
      first == second &&
        ["and i64 14, 11", "or i64 %r0, 5", "xor i64 %r1, 3",
         "shl i64 %r2, 1", "lshr i64 %r3, 2", "ashr i64 -8, 2",
         "bitcast i64 0 to double", "bitcast double %r6 to i64",
         "bitcast i64 -9223372036854775808 to double",
         "bitcast i64 9218868437227405312 to double",
         "bitcast i64 9221120237041090626 to double"].all (fun fragment => ir.contains fragment)
    | .error _ => false
  perOpcode && rendered

private def scalarExecutionPassed : IO Bool := do
  let valid := NecoLean.Llvm.validate scalarInstructionExecutionModule
  match valid with
    | .error _ => pure false
    | .ok module => do
      let path : System.FilePath := ".lake/neco-lean-scalar-instructions"
      let result ← NecoLean.Llvm.compile { module, outputPath := path }
      match result with
        | .error _ => pure false
        | .ok _ =>
          match ← NecoLean.System.run { command := path.toString } with
          | .ok output => pure (output.exitCode == 0 && output.stdout.isEmpty && output.stderr.isEmpty)
          | .error _ => pure false

private def llvmScalarInstructionCheck : IO Bool := do
  let execution ← scalarExecutionPassed
  report "llvm-scalar-instructions" (scalarValidationPassed && scalarDeterminismPassed && execution)
    "bitwise, shift, or bitcast validation, rendering, or execution mismatch"

private def llvmDeterminismCheck : IO Bool := do
  let module2 := NecoLean.Llvm.validate (validModule 2)
  let module7 := NecoLean.Llvm.validate (validModule 7)
  let joinAndCast := NecoLean.Llvm.validate joinAndCastModule
  let floatModule := NecoLean.Llvm.validate floatModule
  let callableTransport := NecoLean.Llvm.validate callableTransportModule
  let nullTransport := NecoLean.Llvm.validate nullTransportModule
  let linuxArgs := NecoLean.Llvm.clangArguments .linux "program.ll" "program" [] none
  let macArgs := NecoLean.Llvm.clangArguments .macOS "program.ll" "program" ["program.runtime-sources/runtime.c"] (some "/SDK")
  let unsupported := NecoLean.Llvm.platformFromName "FreeBSD"
  let platformPassed :=
    (match linuxArgs with | .ok args => args == ["program.ll", "-Wno-override-module", "-lm", "-o", "program"] | .error _ => false) &&
    (match macArgs with | .ok args => args == ["program.ll", "program.runtime-sources/runtime.c", "-Wno-override-module", "-isysroot", "/SDK", "-o", "program"] | .error _ => false) &&
    match NecoLean.Llvm.platformFromName "Linux", NecoLean.Llvm.platformFromName "Darwin", unsupported with
    | .ok .linux, .ok .macOS, .error (.toolUnavailable message) => message == "unsupported operating system: FreeBSD"
    | _, _, _ => false
  let passed := match module2, module7, joinAndCast, floatModule, callableTransport, nullTransport with
    | .ok valid2, .ok valid7, .ok validJoinAndCast, .ok validFloat, .ok validCallable, .ok validNull =>
      let first2 := NecoLean.Llvm.encode valid2
      let second2 := NecoLean.Llvm.encode valid2
      let first7 := NecoLean.Llvm.encode valid7
      let second7 := NecoLean.Llvm.encode valid7
      let firstJoinAndCast := NecoLean.Llvm.encode validJoinAndCast
      let secondJoinAndCast := NecoLean.Llvm.encode validJoinAndCast
      let firstFloat := NecoLean.Llvm.encode validFloat
      let secondFloat := NecoLean.Llvm.encode validFloat
      let firstNull := NecoLean.Llvm.encode validNull
      let secondNull := NecoLean.Llvm.encode validNull
      let callableText := String.fromUTF8! (NecoLean.Llvm.encode validCallable)
      let floatText := String.fromUTF8! firstFloat
      platformPassed && first2 == second2 && first7 == second7 && first2 != first7 && firstJoinAndCast == secondJoinAndCast && firstFloat == secondFloat && firstNull == secondNull && (String.fromUTF8! firstNull).contains "ptr null" && callableText.contains "call i32 @apply(ptr %r1, i32 41)" && callableText.contains "call i32 %r3(i32 0)" && !callableText.contains "call i32 ptr" && ["0x0000000000000000", "0x8000000000000000", "0x0000000000000001", "0x3FF0000000000000", "0x4000000000000000", "0x7FF0000000000000", "0x7FF8000000000001", "0x7FF8000000000002"].all (fun bits => floatText.contains bits)
    | _, _, _, _, _, _ => false
  report "llvm-determinism" passed "LLVM IR or platform arguments are not deterministic"

private def directCallModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "answer" (.integer 32) [])
          [{ label := "entry", terminator := some (.ret (some (.integer 32 41))) }],
       .definition validSignature
          [{ label := "entry",
             instructions :=
               [.call (some ⟨0⟩) (globalFunctionOperand "answer" (.integer 32) []) [],
                .add ⟨1⟩ 32 (.local ⟨0⟩ (.integer 32)) (.integer 32 1)],
             terminator := some (.ret (some (.local ⟨1⟩ (.integer 32)))) }]] }

private def stdoutModule : NecoLean.Llvm.Module :=
  { globals := [{ name := "fmt", value := "neco-lean stdout\n" }],
    functions :=
      [.declaration (llvmSignature "printf" (.integer 32) [cStringPointer] true),
       .definition validSignature
          [{ label := "entry",
             instructions := [.getElementPtr ⟨0⟩ (.globalString "fmt" (globalStringPointer "neco-lean stdout\n")) [(.integer 32 0), (.integer 32 0)], .call none (globalFunctionOperand "printf" (.integer 32) [cStringPointer] true) [(.local ⟨0⟩ cStringPointer)]],
              terminator := some (.ret (some (.integer 32 0))) }]] }

private def unreachableModule : NecoLean.Llvm.Module :=
  { functions :=
      [.declaration (llvmSignature "abort" .void []),
       .definition validSignature
          [{ label := "entry",
             instructions := [.call none (globalFunctionOperand "abort" .void []) []],
             terminator := some .unreachable }]] }

private def floatExecutionModule : NecoLean.Llvm.Module :=
  { functions :=
      [.definition (llvmSignature "identity" .float64 [.float64])
          [{ label := "entry", terminator := some (.ret (some (.parameter 0 .float64))) }],
       .definition validSignature
          [{ label := "entry",
             instructions :=
               [.alloca ⟨0⟩ .float64,
                .store (.float64 0x3FF0000000000000) (.local ⟨0⟩ (.pointer (some .float64))),
                .load ⟨1⟩ (.local ⟨0⟩ (.pointer (some .float64))),
                .call (some ⟨2⟩) (globalFunctionOperand "identity" .float64 [.float64]) [(.local ⟨1⟩ .float64)],
                .fadd ⟨3⟩ (.local ⟨2⟩ .float64) (.float64 0x4000000000000000),
                .fsub ⟨4⟩ (.local ⟨3⟩ .float64) (.float64 0x3FF0000000000000),
                .fmul ⟨5⟩ (.local ⟨4⟩ .float64) (.float64 0x4000000000000000),
                .fdiv ⟨6⟩ (.local ⟨5⟩ .float64) (.float64 0x4000000000000000),
                .fneg ⟨7⟩ (.local ⟨6⟩ .float64),
                .fcmp ⟨8⟩ .olt (.local ⟨7⟩ .float64) (.float64 0x0000000000000000),
              .fcmp ⟨9⟩ .une (.float64 0x7FF8000000000001) (.float64 0x7FF8000000000002),
              .zext ⟨10⟩ (.local ⟨8⟩ (.integer 1)) 32,
              .zext ⟨11⟩ (.local ⟨9⟩ (.integer 1)) 32,
              .add ⟨12⟩ 32 (.local ⟨10⟩ (.integer 32)) (.local ⟨11⟩ (.integer 32)),
              .fdiv ⟨13⟩ (.float64 0x3FF0000000000000) (.float64 0x0000000000000000),
              .fcmp ⟨14⟩ .oeq (.local ⟨13⟩ .float64) (.float64 0x7FF0000000000000),
              .fdiv ⟨15⟩ (.float64 0x3FF0000000000000) (.float64 0x8000000000000000),
              .fcmp ⟨16⟩ .oeq (.local ⟨15⟩ .float64) (.float64 0xFFF0000000000000),
              .fdiv ⟨17⟩ (.float64 0x0000000000000000) (.float64 0x0000000000000000),
              .fcmp ⟨18⟩ .uno (.local ⟨17⟩ .float64) (.float64 0x0000000000000000),
              .fneg ⟨19⟩ (.float64 0x0000000000000000),
              .fdiv ⟨20⟩ (.float64 0x3FF0000000000000) (.local ⟨19⟩ .float64),
              .fcmp ⟨21⟩ .oeq (.local ⟨20⟩ .float64) (.float64 0xFFF0000000000000),
              .zext ⟨22⟩ (.local ⟨14⟩ (.integer 1)) 32,
              .zext ⟨23⟩ (.local ⟨16⟩ (.integer 1)) 32,
              .zext ⟨24⟩ (.local ⟨18⟩ (.integer 1)) 32,
              .zext ⟨25⟩ (.local ⟨21⟩ (.integer 1)) 32,
              .add ⟨26⟩ 32 (.local ⟨12⟩ (.integer 32)) (.local ⟨22⟩ (.integer 32)),
              .add ⟨27⟩ 32 (.local ⟨26⟩ (.integer 32)) (.local ⟨23⟩ (.integer 32)),
              .add ⟨28⟩ 32 (.local ⟨27⟩ (.integer 32)) (.local ⟨24⟩ (.integer 32)),
              .add ⟨29⟩ 32 (.local ⟨28⟩ (.integer 32)) (.local ⟨25⟩ (.integer 32)),
              .fneg ⟨30⟩ (.float64 0x8000000000000000),
              .fdiv ⟨31⟩ (.float64 0x3FF0000000000000) (.local ⟨30⟩ .float64),
              .fcmp ⟨32⟩ .oeq (.local ⟨31⟩ .float64) (.float64 0x7FF0000000000000),
              .zext ⟨33⟩ (.local ⟨32⟩ (.integer 1)) 32,
              .add ⟨34⟩ 32 (.local ⟨29⟩ (.integer 32)) (.local ⟨33⟩ (.integer 32))],
             terminator := some (.ret (some (.local ⟨34⟩ (.integer 32)))) }]] }

private def floatPhiVarargModule : NecoLean.Llvm.Module :=
  { globals := [{ name := "float_fmt", value := "%.17g\n" }],
    functions :=
      [.declaration (llvmSignature "printf" (.integer 32) [cStringPointer] true),
       .definition validSignature
          [{ label := "entry", terminator := some (.condBranch (.integer 1 1) "left" "right") },
           { label := "left", instructions := [.fadd ⟨0⟩ (.float64 0x3FF0000000000000) (.float64 0x3FF0000000000000)], terminator := some (.branch "join") },
           { label := "right", instructions := [.fsub ⟨1⟩ (.float64 0x4000000000000000) (.float64 0x3FF0000000000000)], terminator := some (.branch "join") },
           { label := "join", instructions := [.phi ⟨2⟩ .float64 [("left", .local ⟨0⟩ .float64), ("right", .local ⟨1⟩ .float64)], .getElementPtr ⟨3⟩ (.globalString "float_fmt" (globalStringPointer "%.17g\n")) [(.integer 32 0), (.integer 32 0)], .call none (globalFunctionOperand "printf" (.integer 32) [cStringPointer] true) [(.local ⟨3⟩ cStringPointer), (.local ⟨2⟩ .float64)]], terminator := some (.ret (some (.integer 32 0))) }]] }

private def llvmFcmpTruthTableExecutionCheck : IO Bool := do
  let path : System.FilePath := ".lake/neco-lean-fcmp-truth-table"
  match NecoLean.Llvm.validate fcmpTruthTableModule with
  | .error _ => report "llvm-fcmp-truth-table" false "typed truth-table module rejected"
  | .ok module =>
    match ← NecoLean.Llvm.compile { module, outputPath := path } with
    | .error _ => report "llvm-fcmp-truth-table" false "clang compile failed"
    | .ok _ =>
      match ← NecoLean.System.run { command := path.toString } with
      | .ok output => report "llvm-fcmp-truth-table" (output.exitCode == 0) "truth-table mismatch"
      | .error _ => report "llvm-fcmp-truth-table" false "truth-table executable failed"

private inductive CompileOutcome where
  | compiled
  | unavailable (command : String)
  | rejected (command : String) (exitCode : UInt32)
  | otherFailure (text : String)
  deriving Repr, BEq

private def compileOutcome : Except NecoLean.Llvm.Failure NecoLean.Llvm.CompileOutput → CompileOutcome
  | .ok _ => .compiled
  | .error (.toolUnavailable command) => .unavailable command
  | .error (.toolRejected command _ exitCode _ _) => .rejected command exitCode
  | .error failure => .otherFailure (mustTailLlvmFailureText failure)

private def llvmCompileProbe (outputPath : System.FilePath) : IO UInt32 := do
  match NecoLean.Llvm.validate (validModule 0) with
  | .error _ => return 1
  | .ok module =>
    let outcome := compileOutcome (← NecoLean.Llvm.compile { module, outputPath })
    IO.println (reprStr outcome)
    return 0

private structure PrerequisiteCase where
  name : String
  tools : List (String × String)
  expected : CompileOutcome

private def hostCommandPath (command : String) : IO (Except String String) := do
  match ← NecoLean.System.run { command := "sh", arguments := ["-c", s!"command -v {command}"] } with
  | .ok output =>
    match String.fromUTF8? output.stdout with
    | some text => return .ok text.trimAscii.toString
    | none => return .error s!"{command}: path is not UTF-8"
  | .error _ => return .error s!"{command}: not found on the host"

private def writeToolScript (directory : System.FilePath) (tool body : String) : IO Unit := do
  let path := directory / tool
  IO.FS.writeFile path ("#!/bin/sh\n" ++ body ++ "\n")
  IO.setAccessRights path { user := { read := true, write := true, execution := true } }

private def runPrerequisiteCase (root : System.FilePath) (testCase : PrerequisiteCase) : IO Bool := do
  let directory := root / testCase.name
  if ← directory.pathExists then IO.FS.removeDirAll directory
  IO.FS.createDirAll directory
  for (tool, body) in testCase.tools do writeToolScript directory tool body
  let output ← IO.Process.output
    { cmd := (← IO.appPath).toString
      args := #["llvm-compile-probe", (directory / "program").toString]
      env := #[("PATH", some directory.toString)] }
  let expected := reprStr testCase.expected
  let actual := output.stdout.trimAscii.toString
  if output.exitCode == 0 && actual == expected then return true
  IO.eprintln s!"llvm-platform-prerequisite {testCase.name}: expected {expected}, observed exit {output.exitCode} stdout {actual} stderr {output.stderr.trimAscii.toString}"
  return false

private def llvmPlatformPrerequisiteCheck : IO Bool := do
  let root := (← IO.currentDir) / ".lake" / "neco-lean-platform-prerequisite"
  let hostName ← NecoLean.System.run { command := "uname", arguments := ["-s"] }
  let hostPlatform := match hostName with
    | .ok output => (String.fromUTF8? output.stdout).map (fun text => NecoLean.Llvm.platformFromName text)
    | .error _ => none
  let sdkTools := match hostPlatform with
    | some (.ok .macOS) => ["xcrun"]
    | _ => []
  let resolved ← (["uname"] ++ sdkTools).mapM (fun tool => do return (tool, ← hostCommandPath tool))
  match hostPlatform, resolved.find? (fun (_, path) => match path with | .error _ => true | .ok _ => false) with
  | some (.ok _), none =>
    let delegate := fun (tool : String) => resolved.find? (·.1 == tool) |>.bind (fun (_, path) => match path with | .ok text => some (tool, s!"exec '{text}' \"$@\"") | .error _ => none)
    let uname := (delegate "uname").toList
    let sdk := sdkTools.filterMap delegate
    let pureSdkPassed :=
      (match NecoLean.Llvm.sdkArguments .macOS none with | .error (.toolUnavailable "xcrun") => true | _ => false) &&
      (match NecoLean.Llvm.sdkArguments .linux (some "/SDK") with | .error (.toolUnavailable _) => true | _ => false)
    let cases : List PrerequisiteCase :=
      [{ name := "unsupported-system", tools := [("uname", "printf 'FreeBSD\\n'")], expected := .unavailable "unsupported operating system: FreeBSD" },
       { name := "missing-compiler", tools := uname ++ sdk, expected := .unavailable "clang" },
       { name := "rejecting-compiler", tools := uname ++ sdk ++ [("clang", "exit 7")], expected := .rejected "clang" 7 }] ++
      sdkTools.map (fun tool => { name := s!"missing-{tool}", tools := uname ++ sdk.filter (·.1 != tool), expected := .unavailable tool })
    let results ← cases.mapM (runPrerequisiteCase root)
    report "llvm-platform-prerequisite" (pureSdkPassed && results.all id) "missing or failing platform prerequisite was not reported as an explicit failure"
  | _, _ => report "llvm-platform-prerequisite" false "host platform or host tool path is unavailable"

private def objectRootStateText : NecoLean.Llvm.ObjectOutputRootState → String
  | .observedPresent => "present"
  | .observedAbsent => "absent"
  | .observationFailed failure => "observationFailed(" ++ mustTailSystemFailureText failure ++ ")"

private def arbitrateObjectCleanup (stage : String) (primary : Option NecoLean.Llvm.Failure)
    (residual : NecoLean.Llvm.OwnedObjectCleanupResidual) : IO Bool := do
  let primaryText := primary.map mustTailLlvmFailureText |>.getD "none"
  IO.eprintln s!"object-cleanup: stage={stage} primary={primaryText} initial={mustTailLlvmFailureText residual.cleanup} root={residual.rootObservation.root} state={objectRootStateText residual.rootObservation.state}"
  match ← NecoLean.Llvm.releaseObjectOutputs residual.ownership with
  | .released => pure true
  | .retained finalResidual =>
    IO.eprintln s!"object-cleanup-retained: stage={stage} primary={primaryText} initial={mustTailLlvmFailureText residual.cleanup} initialRoot={residual.rootObservation.root} initialState={objectRootStateText residual.rootObservation.state} final={mustTailLlvmFailureText finalResidual.cleanup} finalRoot={finalResidual.rootObservation.root} finalState={objectRootStateText finalResidual.rootObservation.state}"
    pure false

private def runtimeOptimizationSources : Except NecoLean.Llvm.Failure
    (NecoLean.Llvm.RuntimeSource × NecoLean.Llvm.RuntimeSource × List NecoLean.Llvm.RuntimeSource) := do
  let header ← runtimeSourceHeader 5
  let unit ← runtimeSourceUnit
  let metadata ← NecoLean.Llvm.RuntimeSource.create "runtime_metadata.c" .compilationUnit
    "int runtime_metadata(void) { return 7; }\n".toUTF8
  let launcher ← NecoLean.Llvm.RuntimeSource.create "runtime_launcher.c" .compilationUnit
    "int runtime_launcher(void) { return 11; }\n".toUTF8
  pure (header, unit, [header, unit, metadata, launcher])

private def normalizeObjectArguments (root : System.FilePath) (arguments : List String) : List String :=
  arguments.map fun argument =>
    if argument.startsWith root.toString then
      "$ROOT" ++ (argument.drop root.toString.length).toString
    else
      argument

private structure RuntimeOptimizationInvalidCase where
  label : String
  selections : List NecoLean.Llvm.RuntimeUnitOptimization
  expectedIndex : Nat
  expectedName : String
  expectedDigest : String
  expectedReason : String

private def llvmRuntimeUnitOptimizationCheck : IO Bool := do
  let parent ← IO.FS.createTempDir
  let mut allObjectOwnersReleased := true
  let outputDefault : System.FilePath := parent.toString ++ "/objects-default"
  let outputOptimized : System.FilePath := parent.toString ++ "/objects-optimized"
  let moduleResult := NecoLean.Llvm.validate runtimeSourceModule
  let result ← match moduleResult, runtimeOptimizationSources with
    | .ok module, .ok (header, runtimeUnit, runtimeSources) => do
      let selection : NecoLean.Llvm.RuntimeUnitOptimization := {
        runtimeSourceIndex := 1,
        logicalName := runtimeUnit.logicalName,
        inputDigest := runtimeUnit.digest,
        optimization := .o2
      }
      let validSelection := NecoLean.Llvm.validateRuntimeUnitOptimizations runtimeSources [selection]
      let invalidRequests : List RuntimeOptimizationInvalidCase :=
        [ { label := "index", selections := [{ selection with runtimeSourceIndex := 9 }], expectedIndex := 9,
            expectedName := runtimeUnit.logicalName, expectedDigest := runtimeUnit.digest,
            expectedReason := "runtime source index is out of range" },
          { label := "header", selections := [{ selection with runtimeSourceIndex := 0, logicalName := header.logicalName, inputDigest := header.digest }], expectedIndex := 0,
            expectedName := header.logicalName, expectedDigest := header.digest,
            expectedReason := "runtime source index does not name a compilation unit" },
          { label := "duplicate", selections := [selection, selection], expectedIndex := 1,
            expectedName := runtimeUnit.logicalName, expectedDigest := runtimeUnit.digest,
            expectedReason := "runtime source index is repeated" },
          { label := "name", selections := [{ selection with logicalName := "other.c" }], expectedIndex := 1,
            expectedName := "other.c", expectedDigest := runtimeUnit.digest,
            expectedReason := "runtime source logical name does not match" },
          { label := "digest", selections := [{ selection with inputDigest := "not-the-source-digest" }], expectedIndex := 1,
            expectedName := runtimeUnit.logicalName, expectedDigest := "not-the-source-digest",
            expectedReason := "runtime source digest does not match" } ]
      let defaultValidation := NecoLean.Llvm.validateRuntimeUnitOptimizations runtimeSources []
      let defaultValidationPassed := match defaultValidation with | .ok () => true | .error _ => false
      let validSelectionPassed := match validSelection with | .ok () => true | .error _ => false
      let invalidValidationPassed := invalidRequests.all (fun request =>
        match NecoLean.Llvm.validateRuntimeUnitOptimizations runtimeSources request.selections with
        | .error (.invalidRuntimeUnitOptimization index name digest reason) =>
          index == request.expectedIndex && name == request.expectedName && digest == request.expectedDigest && reason == request.expectedReason
        | _ => false)
      let mut invalidCompilePassed := true
      for request in invalidRequests do
        let output : System.FilePath := parent.toString ++ "/invalid-" ++ request.label
        let compiled ← NecoLean.Llvm.compileObjects {
          module,
          outputDirectory := output,
          runtimeSources,
          runtimeUnitOptimizations := request.selections
        }
        let typedFailure ← match compiled with
          | .error (.operation (.invalidRuntimeUnitOptimization index name digest reason)) =>
            pure (index == request.expectedIndex && name == request.expectedName && digest == request.expectedDigest && reason == request.expectedReason)
          | .error (.cleanupRetained primary residual) =>
            let released ← arbitrateObjectCleanup ("runtime-optimization-invalid-" ++ request.label) (some primary) residual
            allObjectOwnersReleased := allObjectOwnersReleased && released
            pure false
          | .error (.operation _) => pure false
          | .ok artifact =>
            let releaseResult ← NecoLean.Llvm.releaseObjectOutputs artifact.ownership
            let released ← match releaseResult with
              | .released => pure true
              | .retained residual => arbitrateObjectCleanup ("runtime-optimization-invalid-" ++ request.label) none residual
            allObjectOwnersReleased := allObjectOwnersReleased && released
            pure false
        invalidCompilePassed := invalidCompilePassed && typedFailure && !(← output.pathExists)
      let defaultCompiled ← NecoLean.Llvm.compileObjects {
        module,
        outputDirectory := outputDefault,
        runtimeSources
      }
      let optimizedCompiled ← NecoLean.Llvm.compileObjects {
        module,
        outputDirectory := outputOptimized,
        runtimeSources,
        runtimeUnitOptimizations := [selection]
      }
      match defaultCompiled, optimizedCompiled with
      | .ok baseline, .ok optimized => do
        let expectedRoles := [
          .llvmModule,
          .runtimeCompilationUnit 1 "runtime_fixture.c",
          .runtimeCompilationUnit 2 "runtime_metadata.c",
          .runtimeCompilationUnit 3 "runtime_launcher.c"
        ]
        let rolesMatch := baseline.objects.map NecoLean.Llvm.CompiledObjectArtifact.role == expectedRoles &&
          optimized.objects.map NecoLean.Llvm.CompiledObjectArtifact.role == expectedRoles
        let artifactsKeepIdentity := baseline.runtimeSourceBundleIdentity == optimized.runtimeSourceBundleIdentity &&
          baseline.runtimeSources.map NecoLean.Llvm.RuntimeSourceArtifact.digest ==
            optimized.runtimeSources.map NecoLean.Llvm.RuntimeSourceArtifact.digest
        let ordinalsMatch :=
          (baseline.objects[1]?.map NecoLean.Llvm.CompiledObjectArtifact.outputPath).any (fun path => path.toString.contains "object-002-") &&
          (baseline.objects[2]?.map NecoLean.Llvm.CompiledObjectArtifact.outputPath).any (fun path => path.toString.contains "object-003-") &&
          (baseline.objects[3]?.map NecoLean.Llvm.CompiledObjectArtifact.outputPath).any (fun path => path.toString.contains "object-004-")
        let untouchedArgumentsMatch := [0, 2, 3].all (fun index =>
          match baseline.objects[index]?, optimized.objects[index]? with
          | some base, some candidate =>
            base.normalizedArguments == candidate.normalizedArguments &&
            normalizeObjectArguments outputDefault base.arguments == normalizeObjectArguments outputOptimized candidate.arguments &&
            !base.arguments.contains "-O2" && !candidate.arguments.contains "-O2" &&
            !base.normalizedArguments.contains "-O2" && !candidate.normalizedArguments.contains "-O2"
          | _, _ => false)
        let targetedArgumentsMatch :=
          match baseline.objects[1]?, optimized.objects[1]? with
          | some base, some candidate =>
            let expectedNormalized := base.normalizedArguments.take 4 ++ ["-O2"] ++ base.normalizedArguments.drop 4
            let baseActual := normalizeObjectArguments outputDefault base.arguments
            let candidateActual := normalizeObjectArguments outputOptimized candidate.arguments
            let expectedActual := baseActual.take 4 ++ ["-O2"] ++ baseActual.drop 4
            candidate.normalizedArguments == expectedNormalized && candidateActual == expectedActual &&
              (candidate.arguments.filter (· == "-O2")).length == 1 &&
              (candidate.normalizedArguments.filter (· == "-O2")).length == 1 &&
              !(base.arguments.contains "-O2") && !(base.normalizedArguments.contains "-O2")
          | _, _ => false
        let defaultRelease ← NecoLean.Llvm.releaseObjectOutputs baseline.ownership
        let optimizedRelease ← NecoLean.Llvm.releaseObjectOutputs optimized.ownership
        let defaultReleased ← match defaultRelease with
          | .released => pure true
          | .retained residual => arbitrateObjectCleanup "runtime-optimization-default-release" none residual
        let optimizedReleased ← match optimizedRelease with
          | .released => pure true
          | .retained residual => arbitrateObjectCleanup "runtime-optimization-candidate-release" none residual
        allObjectOwnersReleased := allObjectOwnersReleased && defaultReleased && optimizedReleased
        let cleanupPassed := defaultReleased && optimizedReleased &&
          !(← outputDefault.pathExists) && !(← outputOptimized.pathExists)
        pure (defaultValidationPassed && validSelectionPassed && invalidValidationPassed && invalidCompilePassed &&
          rolesMatch && artifactsKeepIdentity && ordinalsMatch && untouchedArgumentsMatch && targetedArgumentsMatch && cleanupPassed)
      | .ok baseline, .error (.cleanupRetained primary residual) => do
        let candidateReleased ← arbitrateObjectCleanup "runtime-optimization-candidate-failed" (some primary) residual
        let baselineRelease ← NecoLean.Llvm.releaseObjectOutputs baseline.ownership
        let baselineReleased ← match baselineRelease with
          | .released => pure true
          | .retained cleanup => arbitrateObjectCleanup "runtime-optimization-default-release" none cleanup
        allObjectOwnersReleased := allObjectOwnersReleased && candidateReleased && baselineReleased
        pure false
      | .ok baseline, .error (.operation _) => do
        let release ← NecoLean.Llvm.releaseObjectOutputs baseline.ownership
        let baselineReleased ← match release with
          | .released => pure true
          | .retained residual => arbitrateObjectCleanup "runtime-optimization-default-release" none residual
        allObjectOwnersReleased := allObjectOwnersReleased && baselineReleased
        pure false
      | .error (.cleanupRetained primary residual), .ok optimized => do
        let baselineReleased ← arbitrateObjectCleanup "runtime-optimization-baseline-failed" (some primary) residual
        let release ← NecoLean.Llvm.releaseObjectOutputs optimized.ownership
        let optimizedReleased ← match release with
          | .released => pure true
          | .retained cleanup => arbitrateObjectCleanup "runtime-optimization-candidate-release" none cleanup
        allObjectOwnersReleased := allObjectOwnersReleased && baselineReleased && optimizedReleased
        pure false
      | .error (.operation _), .ok optimized => do
        let release ← NecoLean.Llvm.releaseObjectOutputs optimized.ownership
        let optimizedReleased ← match release with
          | .released => pure true
          | .retained residual => arbitrateObjectCleanup "runtime-optimization-candidate-release" none residual
        allObjectOwnersReleased := allObjectOwnersReleased && optimizedReleased
        pure false
      | _, _ => pure false
    | _, _ => pure false
  if allObjectOwnersReleased then try IO.FS.removeDirAll parent catch _ => pure ()
  report "llvm-runtime-unit-optimization" result "runtime unit selection, validation, or argument plan mismatch"

private def llvmCompiledObjectFileName (path : System.FilePath) : String :=
  path.toString.splitOn "/" |>.reverse.head?.getD path.toString

private def releaseObjectOptimizationOutput (output : NecoLean.Llvm.ObjectCompileOutput) : IO Bool := do
  match ← NecoLean.Llvm.releaseObjectOutputs output.ownership with
  | .released => return !(← output.ownership.directory.pathExists)
  | .retained residual =>
    let released ← arbitrateObjectCleanup "optimization-policy" none residual
    return released && !(← output.ownership.directory.pathExists)

private def llvmObjectOptimizationCheck : IO Bool := do
  let parent ← IO.FS.createTempDir
  let defaultOutputDirectory : System.FilePath := parent.toString ++ "/objects-default"
  let optimizedOutputDirectory : System.FilePath := parent.toString ++ "/objects-o1"
  let mut allObjectOwnersReleased := true
  let result ←
    match NecoLean.Llvm.validate (validModule 17),
        NecoLean.Llvm.RuntimeSource.create "optimization_runtime.c" .compilationUnit "int optimization_runtime(void) { return 17; }\n".toUTF8 with
    | .ok module, .ok runtimeSource => do
      let defaultResult ← NecoLean.Llvm.compileObjects {
        module
        outputDirectory := defaultOutputDirectory
        runtimeSources := [runtimeSource]
      }
      match defaultResult with
      | .error (.cleanupRetained primary residual) => do
        allObjectOwnersReleased := ← arbitrateObjectCleanup "optimization-policy-default" (some primary) residual
        pure false
      | .error (.operation _) => pure false
      | .ok defaultOutput => do
        let optimizedResult ← NecoLean.Llvm.compileObjects {
          module
          outputDirectory := optimizedOutputDirectory
          runtimeSources := [runtimeSource]
          moduleOptimization := .o1
        }
        match optimizedResult with
        | .error (.cleanupRetained primary residual) => do
          let optimizedReleased ← arbitrateObjectCleanup "optimization-policy-o1" (some primary) residual
          let defaultReleased ← releaseObjectOptimizationOutput defaultOutput
          allObjectOwnersReleased := optimizedReleased && defaultReleased
          pure false
        | .error (.operation _) => do
          allObjectOwnersReleased := ← releaseObjectOptimizationOutput defaultOutput
          pure false
        | .ok optimizedOutput => do
          let argumentsAndIdentityMatch :=
            match defaultOutput.objects, optimizedOutput.objects with
            | [defaultModule, defaultRuntime], [optimizedModule, optimizedRuntime] =>
              let defaultSdkArguments := match defaultOutput.compilerIdentity.sdkIdentity with
                | none => []
                | some identity => ["-isysroot", identity.path.toString]
              let optimizedSdkArguments := match optimizedOutput.compilerIdentity.sdkIdentity with
                | none => []
                | some identity => ["-isysroot", identity.path.toString]
              let defaultModuleName := llvmCompiledObjectFileName defaultModule.outputPath
              let optimizedModuleName := llvmCompiledObjectFileName optimizedModule.outputPath
              let defaultRuntimeName := llvmCompiledObjectFileName defaultRuntime.outputPath
              let optimizedRuntimeName := llvmCompiledObjectFileName optimizedRuntime.outputPath
              let defaultModuleActual := ["-c", defaultOutputDirectory.toString ++ "/inputs/module.ll", "-Wno-override-module"] ++
                defaultSdkArguments ++ ["-o", defaultModule.outputPath.toString]
              let defaultModuleNormalized := ["-c", "$INPUTS/module.ll", "-Wno-override-module"] ++
                defaultSdkArguments ++ ["-o", "$ARTIFACT/objects/" ++ defaultModuleName]
              let optimizedModuleActual := ["-c", optimizedOutputDirectory.toString ++ "/inputs/module.ll", "-Wno-override-module", "-O1"] ++
                optimizedSdkArguments ++ ["-o", optimizedModule.outputPath.toString]
              let optimizedModuleNormalized := ["-c", "$INPUTS/module.ll", "-Wno-override-module", "-O1"] ++
                optimizedSdkArguments ++ ["-o", "$ARTIFACT/objects/" ++ optimizedModuleName]
              let defaultRuntimeActual := ["-c", defaultOutputDirectory.toString ++ "/inputs/optimization_runtime.c", "-I", defaultOutputDirectory.toString ++ "/inputs"] ++
                defaultSdkArguments ++ ["-o", defaultRuntime.outputPath.toString]
              let defaultRuntimeNormalized := ["-c", "$INPUTS/optimization_runtime.c", "-I", "$INPUTS"] ++
                defaultSdkArguments ++ ["-o", "$ARTIFACT/objects/" ++ defaultRuntimeName]
              let optimizedRuntimeActual := ["-c", optimizedOutputDirectory.toString ++ "/inputs/optimization_runtime.c", "-I", optimizedOutputDirectory.toString ++ "/inputs"] ++
                optimizedSdkArguments ++ ["-o", optimizedRuntime.outputPath.toString]
              let optimizedRuntimeNormalized := ["-c", "$INPUTS/optimization_runtime.c", "-I", "$INPUTS"] ++
                optimizedSdkArguments ++ ["-o", "$ARTIFACT/objects/" ++ optimizedRuntimeName]
              let defaultManifestRelevantTuple :=
                s!"{reprStr defaultModule.role}\u0000{defaultModule.inputDigest}\u0000{String.intercalate "\u0000" defaultModule.normalizedArguments}\u0000{defaultModuleName}\u0000{defaultModule.outputDigest}"
              let optimizedManifestRelevantTuple :=
                s!"{reprStr optimizedModule.role}\u0000{optimizedModule.inputDigest}\u0000{String.intercalate "\u0000" optimizedModule.normalizedArguments}\u0000{optimizedModuleName}\u0000{optimizedModule.outputDigest}"
              defaultModule.role == .llvmModule && optimizedModule.role == .llvmModule &&
                defaultRuntime.role == .runtimeCompilationUnit 0 "optimization_runtime.c" &&
                optimizedRuntime.role == .runtimeCompilationUnit 0 "optimization_runtime.c" &&
                defaultModule.arguments == defaultModuleActual && defaultModule.normalizedArguments == defaultModuleNormalized &&
                optimizedModule.arguments == optimizedModuleActual && optimizedModule.normalizedArguments == optimizedModuleNormalized &&
                defaultRuntime.arguments == defaultRuntimeActual && defaultRuntime.normalizedArguments == defaultRuntimeNormalized &&
                optimizedRuntime.arguments == optimizedRuntimeActual && optimizedRuntime.normalizedArguments == optimizedRuntimeNormalized &&
                defaultModule.inputDigest == optimizedModule.inputDigest &&
                defaultRuntime.inputDigest == optimizedRuntime.inputDigest &&
                defaultRuntime.normalizedArguments == optimizedRuntime.normalizedArguments &&
                defaultOutput.runtimeSourceBundleIdentity == optimizedOutput.runtimeSourceBundleIdentity &&
                defaultOutput.compilerIdentity.executableDigest == optimizedOutput.compilerIdentity.executableDigest &&
                defaultOutput.compilerIdentity.versionDigest == optimizedOutput.compilerIdentity.versionDigest &&
                defaultOutput.compilerIdentity.targetTriple == optimizedOutput.compilerIdentity.targetTriple &&
                defaultSdkArguments == optimizedSdkArguments &&
                defaultManifestRelevantTuple != optimizedManifestRelevantTuple
            | _, _ => false
          let defaultReleased ← releaseObjectOptimizationOutput defaultOutput
          let optimizedReleased ← releaseObjectOptimizationOutput optimizedOutput
          allObjectOwnersReleased := defaultReleased && optimizedReleased
          pure (argumentsAndIdentityMatch && defaultReleased && optimizedReleased)
    | _, _ => pure false
  if allObjectOwnersReleased then
    try IO.FS.removeDirAll parent catch _ => pure ()
  report "llvm-object-optimization" result "LLVM-module optimization flags, runtime arguments, manifest tuple, or cleanup mismatch"

private def llvmObjectCompilationCheck : IO Bool := do
  let parent ← IO.FS.createTempDir
  let mut allObjectOwnersReleased := true
  let output : System.FilePath := parent.toString ++ "/objects-success"
  let existing : System.FilePath := parent.toString ++ "/objects-existing"
  let mismatched : System.FilePath := parent.toString ++ "/objects-mismatched"
  let rejected : System.FilePath := parent.toString ++ "/objects-rejected"
  let result ←
    match NecoLean.Llvm.validate runtimeSourceModule, runtimeSourceRequestSources,
        NecoLean.Llvm.RuntimeSource.create "runtime_fixture_copy.c" .compilationUnit "int runtime_fixture_copy(void) { return 1; }\n".toUTF8 with
    | .ok module, .ok baseRuntimeSources, .ok secondUnit => do
      let runtimeSources := baseRuntimeSources ++ [secondUnit]
      let compiled ← NecoLean.Llvm.compileObjects { module, outputDirectory := output, runtimeSources }
      match compiled with
      | .error (.cleanupRetained primary residual) => do
        let released ← arbitrateObjectCleanup "compile-success-fixture" (some primary) residual
        allObjectOwnersReleased := released
        pure false
      | .error (.operation _) => pure false
      | .ok artifact =>
        let objectBytes ← artifact.objects.mapM (fun object => NecoLean.System.readBytes object.outputPath)
        let objectDigestsMatch := (artifact.objects.zip objectBytes).all (fun (object, bytes) =>
          match bytes with
          | .ok value => object.outputDigest == NecoLean.Digest.toHex (NecoLean.Digest.sha256 value)
          | .error _ => false)
        let orderedRoles := artifact.objects.map NecoLean.Llvm.CompiledObjectArtifact.role ==
          [.llvmModule, .runtimeCompilationUnit 1 "runtime_fixture.c", .runtimeCompilationUnit 2 "runtime_fixture_copy.c"]
        let normalized := artifact.objects.all (fun object =>
          object.normalizedArguments.any (·.contains "$INPUTS") &&
          object.normalizedArguments.any (·.contains "$ARTIFACT") &&
          object.normalizedArguments.contains "-c" &&
          !object.normalizedArguments.any (·.contains parent.toString))
        let identity := !artifact.compilerIdentity.executablePath.toString.isEmpty &&
          !artifact.compilerIdentity.executableDigest.isEmpty &&
          !artifact.compilerIdentity.versionBytes.isEmpty &&
          !artifact.compilerIdentity.versionDigest.isEmpty &&
          !artifact.compilerIdentity.targetTriple.isEmpty
        let released ← NecoLean.Llvm.releaseObjectOutputs artifact.ownership
        let releasedAbsent := !(← output.pathExists)
        IO.FS.createDir existing
        let sentinel : System.FilePath := existing.toString ++ "/sentinel"
        let _ ← NecoLean.System.writeBytes sentinel "owned-by-test".toUTF8
        let existingResult ← NecoLean.Llvm.compileObjects { module, outputDirectory := existing, runtimeSources }
        let existingPreserved ← match existingResult, (← NecoLean.System.readBytes sentinel) with
          | .error (.operation (.artifactDirectoryExists path)), .ok bytes =>
            pure (path == existing && bytes == "owned-by-test".toUTF8)
          | .error (.cleanupRetained primary residual), _ => do
            let released ← arbitrateObjectCleanup "existing-directory" (some primary) residual
            allObjectOwnersReleased := allObjectOwnersReleased && released
            pure false
          | _, _ => pure false
        let mismatchedResult ← NecoLean.Llvm.compileObjects { module, outputDirectory := mismatched, runtimeSources }
        let markerMismatch ← match mismatchedResult with
          | .error (.cleanupRetained primary residual) => do
            let released ← arbitrateObjectCleanup "marker-fixture-compile" (some primary) residual
            allObjectOwnersReleased := allObjectOwnersReleased && released
            pure false
          | .error (.operation _) => pure false
          | .ok second => do
            let marker : System.FilePath := mismatched.toString ++ "/.neco-object-output-owner"
            let originalMarker ← NecoLean.System.readBytes marker
            let _ ← NecoLean.System.writeBytes marker "different-owner".toUTF8
            let releaseResult ← NecoLean.Llvm.releaseObjectOutputs second.ownership
            let remains ← mismatched.pathExists
            match releaseResult with
              | .retained residual =>
                let inspected := residual.ownership == second.ownership &&
                  residual.rootObservation.root == mismatched &&
                  residual.rootObservation.state == .observedPresent &&
                  match residual.cleanup with | .artifactCleanup _ _ none => true | _ => false
                let restored ← match originalMarker with
                  | .ok bytes => NecoLean.System.writeBytes marker bytes
                  | .error failure => pure (.error failure)
                let released ← match restored with
                  | .ok () => arbitrateObjectCleanup "marker-mismatch" none residual
                  | .error _ => arbitrateObjectCleanup "marker-restore-failed" none residual
                allObjectOwnersReleased := allObjectOwnersReleased && released
                pure (remains && inspected && released)
              | .released => pure false
        let brokenResult ←
          match NecoLean.Llvm.RuntimeSource.create "broken.c" .compilationUnit "int broken( {".toUTF8 with
          | .error failure => pure (.error (.operation failure))
          | .ok broken => NecoLean.Llvm.compileObjects { module, outputDirectory := rejected, runtimeSources := [broken] }
        let rejectedPayload ← match brokenResult with
          | .error (.operation (.toolRejected command arguments code _ stderr)) =>
            pure (!command.isEmpty && arguments.any (·.contains "broken.c") && code != 0 && !stderr.isEmpty)
          | .error (.cleanupRetained primary residual) => do
            let released ← arbitrateObjectCleanup "rejected-compilation" (some primary) residual
            allObjectOwnersReleased := allObjectOwnersReleased && released
            pure false
          | _ => pure false
        let rejectedCleaned := !(← rejected.pathExists)
        let releasedSuccessfully ← match released with
          | .released => pure true
          | .retained residual => do
            let settled ← arbitrateObjectCleanup "success-release" none residual
            allObjectOwnersReleased := allObjectOwnersReleased && settled
            pure false
        pure (artifact.runtimeSources.length == 3 && artifact.objects.length == 3 &&
          artifact.runtimeSourceBundleIdentity == NecoLean.Llvm.runtimeSourceBundleIdentity runtimeSources &&
          orderedRoles && objectDigestsMatch && normalized && identity && releasedSuccessfully &&
          releasedAbsent && existingPreserved && markerMismatch && rejectedPayload && rejectedCleaned)
    | _, _, _ => pure false
  if allObjectOwnersReleased then
    try IO.FS.removeDirAll parent catch _ => pure ()
  report "llvm-object-compilation" result "object compilation or ownership mismatch"

private def directoryEntryWithPrefixAbsent (directory : System.FilePath) (namePrefix : String) : IO Bool := do
  try
    let entries ← System.FilePath.readDir directory
    return !entries.any (fun entry => entry.fileName.startsWith namePrefix)
  catch _ =>
    return false

private def llvmObjectLinkCheck : IO Bool := do
  let parent ← IO.FS.createTempDir
  let mut allObjectOwnersReleased := true
  let realParent ← IO.FS.realPath parent
  let objectDirectory : System.FilePath := parent / "link-inputs"
  let publishedPath : System.FilePath := parent / "linked-runtime"
  let occupiedPath : System.FilePath := parent / "occupied-runtime"
  let compilerMismatchPath : System.FilePath := parent / "compiler-mismatch"
  let digestMismatchPath : System.FilePath := parent / "digest-mismatch"
  let brokenPath : System.FilePath := parent / "broken.o"
  let brokenOutputPath : System.FilePath := parent / "broken-output"
  let markerMismatchPath : System.FilePath := parent / "marker-mismatch"
  let result ←
    match NecoLean.Llvm.validate runtimeSourceModule, runtimeSourceRequestSources with
    | .ok module, .ok runtimeSources => do
      match ← NecoLean.Llvm.compileObjects { module, outputDirectory := objectDirectory, runtimeSources } with
      | .error (.cleanupRetained primary residual) => do
        let released ← arbitrateObjectCleanup "link-input-compilation" (some primary) residual
        allObjectOwnersReleased := released
        pure false
      | .error (.operation _) => pure false
      | .ok artifact =>
        let inputs := artifact.objects.map NecoLean.Llvm.CompiledObjectArtifact.linkInput
        let linked ← NecoLean.Llvm.linkObjects {
          compilerIdentity := artifact.compilerIdentity
          orderedObjects := inputs
          outputPath := publishedPath
        }
        let result ← match linked with
          | .linked output => do
            let identity := output.identity
            let resolvedObjectPaths ← inputs.mapM (fun input => IO.FS.realPath input.path)
            let identityPassed :=
              identity.compilerIdentity == artifact.compilerIdentity &&
              identity.orderedObjectDigests == inputs.map (fun input => input.digest) &&
              identity.identityDigest == identity.recomputeDigest &&
              !identity.executableDigest.isEmpty &&
              identity.normalizedArguments.any (·.contains "$OBJECTS/") &&
              !identity.normalizedArguments.any (·.contains parent.toString) &&
              identity.normalizedArguments.contains "-lm" == !System.Platform.isOSX &&
              output.arguments.contains "-lm" == !System.Platform.isOSX &&
              (match identity.systemLinkClosureIdentity with
               | .unresolved target sdk reason =>
                 target == artifact.compilerIdentity.targetTriple &&
                 sdk == artifact.compilerIdentity.sdkIdentity && !reason.isEmpty)
            let safeObjectArguments := resolvedObjectPaths.all (fun path => output.arguments.contains path.toString)
            let stagedSibling := output.stagedExecutablePath.parent == some output.ownership.directory &&
              output.ownership.directory.parent == some realParent &&
              !(← publishedPath.pathExists)
            let publication ← NecoLean.Llvm.publishLinkedOutput output
            let publicationPassed ← match publication with
              | .published published => do
                let stagingAbsent := !(← output.ownership.directory.pathExists)
                let directExecution := match ← NecoLean.System.run { command := published.outputPath.toString } with
                  | .error (.nonZeroExit _ 42 stdout stderr) => stdout.isEmpty && stderr.isEmpty
                  | _ => false
                pure (published.outputPath == realParent / "linked-runtime" && stagingAbsent && directExecution)
              | _ => pure false

            let _ ← NecoLean.System.writeBytes occupiedPath "caller-owned".toUTF8
            let occupiedResult ← NecoLean.Llvm.linkObjects {
              compilerIdentity := artifact.compilerIdentity
              orderedObjects := inputs
              outputPath := occupiedPath
            }
            let noClobberPassed ← match occupiedResult with
              | .linked occupied => do
                let publishResult ← NecoLean.Llvm.publishLinkedOutput occupied
                let sentinelPreserved := match ← NecoLean.System.readBytes occupiedPath with
                  | .ok bytes => bytes == "caller-owned".toUTF8
                  | _ => false
                let released := match ← NecoLean.Llvm.releaseLinkedOutput occupied with
                  | .released => true
                  | _ => false
                pure (sentinelPreserved && released && match publishResult with
                  | .notPublished (.linkPublication "hard-link" path _) retained =>
                    path == realParent / "occupied-runtime" && retained == occupied
                  | _ => false)
              | _ => pure false

            let changedCompiler := {
              artifact.compilerIdentity with versionDigest := artifact.compilerIdentity.versionDigest ++ "-changed" }
            let compilerMismatchResult ← NecoLean.Llvm.linkObjects {
              compilerIdentity := changedCompiler
              orderedObjects := inputs
              outputPath := compilerMismatchPath
            }
            let compilerMismatchAbsent ← directoryEntryWithPrefixAbsent parent ".compiler-mismatch.neco-link-"
            let compilerMismatchPassed := compilerMismatchAbsent && match compilerMismatchResult with
              | .failed (.compilerIdentityMismatch expected actual) =>
                expected == changedCompiler && actual == artifact.compilerIdentity
              | _ => false

            let changedInputs := match inputs with
              | [] => []
              | first :: rest => { first with digest := first.digest ++ "-changed" } :: rest
            let digestMismatchResult ← NecoLean.Llvm.linkObjects {
              compilerIdentity := artifact.compilerIdentity
              orderedObjects := changedInputs
              outputPath := digestMismatchPath
            }
            let digestMismatchAbsent ← directoryEntryWithPrefixAbsent parent ".digest-mismatch.neco-link-"
            let digestMismatchPassed := digestMismatchAbsent && match digestMismatchResult, changedInputs with
              | .failed (.objectDigestMismatch path expected actual), first :: _ =>
                path == first.path && expected == first.digest && actual != expected
              | _, _ => false

            let _ ← NecoLean.System.writeBytes brokenPath "not an object file".toUTF8
            let brokenDigest := NecoLean.Digest.toHex (NecoLean.Digest.sha256 "not an object file".toUTF8)
            let brokenResult ← NecoLean.Llvm.linkObjects {
              compilerIdentity := artifact.compilerIdentity
              orderedObjects := [{ path := brokenPath, digest := brokenDigest }]
              outputPath := brokenOutputPath
            }
            let brokenStagingAbsent ← directoryEntryWithPrefixAbsent parent ".broken-output.neco-link-"
            let brokenPassed := brokenStagingAbsent && match brokenResult with
              | .failed (.toolRejected command arguments code _ stderr) =>
                !command.isEmpty && arguments.any (·.contains "broken.o") && code != 0 && !stderr.isEmpty
              | _ => false

            let markerResult ← NecoLean.Llvm.linkObjects {
              compilerIdentity := artifact.compilerIdentity
              orderedObjects := inputs
              outputPath := markerMismatchPath
            }
            let markerPassed ← match markerResult with
              | .linked markerOutput => do
                let marker := markerOutput.ownership.markerPath
                let _ ← NecoLean.System.writeBytes marker "different-owner".toUTF8
                match ← NecoLean.Llvm.releaseLinkedOutput markerOutput with
                | .retained (.artifactCleanup path "ownership marker mismatch" none) ownership paths =>
                  pure (path == marker && ownership == markerOutput.ownership &&
                    paths.contains markerOutput.ownership.directory && paths.contains marker)
                | _ => pure false
              | _ => pure false

            pure (identityPassed && safeObjectArguments && stagedSibling && publicationPassed &&
              noClobberPassed && compilerMismatchPassed && digestMismatchPassed && brokenPassed && markerPassed)
          | _ => pure false
        let objectReleased ← match ← NecoLean.Llvm.releaseObjectOutputs artifact.ownership with
          | .released => pure true
          | .retained residual => do
            let released ← arbitrateObjectCleanup "link-input-release" none residual
            allObjectOwnersReleased := allObjectOwnersReleased && released
            pure false
        pure (result && objectReleased)
    | _, _ => pure false
  if allObjectOwnersReleased then
    try IO.FS.removeDirAll parent catch _ => pure ()
  report "llvm-object-link" result "owned object link, publication, identity, or cleanup mismatch"

private def llvmStaticLibraryCheck : IO Bool := do
  let parent ← IO.FS.createTempDir
  let librarySource := parent / "library.c"
  let libraryObject := parent / "library.o"
  let libraryPath := parent / "library.a"
  IO.FS.writeFile (parent / "answer.h") "int external_answer(void);\n"
  IO.FS.writeFile librarySource "int external_answer(void) { return 42; }\n"
  let built ← NecoLean.System.run { command := "clang", arguments := ["-c", librarySource.toString, "-o", libraryObject.toString] }
  let archived ← NecoLean.System.run { command := "ar", arguments := ["rcs", libraryPath.toString, libraryObject.toString] }
  let result ← match built, archived, NecoLean.Llvm.validate runtimeSourceModule,
      NecoLean.Llvm.RuntimeSource.create "adapter.c" .compilationUnit
        "#include <answer.h>\nint add_runtime(int value) { (void)value; return external_answer(); }\n".toUTF8 with
    | .ok _, .ok _, .ok module, .ok source => do
      let bytes ← IO.FS.readBinFile libraryPath
      let digest := NecoLean.Digest.toHex (NecoLean.Digest.sha256 bytes)
      let library : NecoLean.Llvm.StaticLibraryInput := { path := libraryPath, digest }
      let direct ← NecoLean.Llvm.compile {
        module, outputPath := parent / "direct", runtimeSources := [source],
        includeDirectories := [parent], staticLibraries := [library] }
      let directPassed ← match direct with
        | .ok _ => do
          match ← NecoLean.System.run { command := (parent / "direct").toString } with
          | .error (.nonZeroExit _ 42 _ _) => pure true
          | _ => pure false
        | .error _ => pure false
      let badDirect ← NecoLean.Llvm.compile {
        module, outputPath := parent / "bad-direct", runtimeSources := [source],
        includeDirectories := [parent], staticLibraries := [{ library with digest := "changed" }] }
      let badPassed := match badDirect with
        | .error (.objectDigestMismatch _ "changed" actual) => actual == digest
        | _ => false
      match ← NecoLean.Llvm.compileObjects {
        module, outputDirectory := parent / "objects", runtimeSources := [source], includeDirectories := [parent] } with
      | .error _ => pure false
      | .ok objects =>
        let linked ← NecoLean.Llvm.linkObjects {
          compilerIdentity := objects.compilerIdentity,
          orderedObjects := objects.objects.map NecoLean.Llvm.CompiledObjectArtifact.linkInput,
          outputPath := parent / "linked", staticLibraries := [library] }
        let linkPassed ← match linked with
          | .linked output => do
            let passed := output.identity.orderedObjectDigests.getLast? == some digest &&
              output.identity.identityDigest == output.identity.recomputeDigest
            let execution ← NecoLean.System.run { command := output.stagedExecutablePath.toString }
            let _ ← NecoLean.Llvm.releaseLinkedOutput output
            pure (passed && match execution with | .error (.nonZeroExit _ 42 _ _) => true | _ => false)
          | _ => pure false
        let badLink ← NecoLean.Llvm.linkObjects {
          compilerIdentity := objects.compilerIdentity,
          orderedObjects := objects.objects.map NecoLean.Llvm.CompiledObjectArtifact.linkInput,
          outputPath := parent / "bad-linked", staticLibraries := [{ library with digest := "changed" }] }
        let badLinkPassed := match badLink with
          | .failed (.objectDigestMismatch _ "changed" actual) => actual == digest
          | _ => false
        let _ ← NecoLean.Llvm.releaseObjectOutputs objects.ownership
        pure (directPassed && badPassed && linkPassed && badLinkPassed)
    | _, _, _, _ => pure false
  IO.FS.removeDirAll parent
  report "llvm-static-library" result "static library, include directory, digest, or execution mismatch"

private def llvmExecutionCheck : IO Bool := do
  let mustTailExecutionPassed ← mustTailExecutionCheck
  let path2 : System.FilePath := ".lake/neco-lean-main-2"
  let path7 : System.FilePath := ".lake/neco-lean-main-7"
  let callPath : System.FilePath := ".lake/neco-lean-direct-call"
  let stdoutPath : System.FilePath := ".lake/neco-lean-stdout"
  let unreachablePath : System.FilePath := ".lake/neco-lean-unreachable"
  let joinAndCastPath : System.FilePath := ".lake/neco-lean-join-and-cast"
  let floatPath : System.FilePath := ".lake/neco-lean-float"
  let floatPhiVarargPath : System.FilePath := ".lake/neco-lean-float-phi-vararg"
  let callableTransportPath : System.FilePath := ".lake/neco-lean-callable-transport"
  let callableStructGepPath : System.FilePath := ".lake/neco-lean-callable-struct-gep"
  let nullTransportPath : System.FilePath := ".lake/neco-lean-null-transport"
  let runtimeSourcePath : System.FilePath := ".lake/neco-lean-runtime-source"
  let valid2 := match NecoLean.Llvm.validate (validModule 2) with | .ok module => some module | .error _ => none
  let valid7 := match NecoLean.Llvm.validate (validModule 7) with | .ok module => some module | .error _ => none
  let callValidation := NecoLean.Llvm.validate directCallModule
  let stdoutValidation := NecoLean.Llvm.validate stdoutModule
  let unreachableValidation := NecoLean.Llvm.validate unreachableModule
  let joinAndCastValidation := NecoLean.Llvm.validate joinAndCastModule
  let floatValidation := NecoLean.Llvm.validate floatExecutionModule
  let floatPhiVarargValidation := NecoLean.Llvm.validate floatPhiVarargModule
  let callableTransportValidation := NecoLean.Llvm.validate callableTransportModule
  let runtimeSourceValidation := NecoLean.Llvm.validate runtimeSourceModule
  let validCall := match callValidation with | .ok module => some module | .error _ => none
  let validStdout := match stdoutValidation with | .ok module => some module | .error _ => none
  let validUnreachable := match unreachableValidation with | .ok module => some module | .error _ => none
  let validJoinAndCast := match joinAndCastValidation with | .ok module => some module | .error _ => none
  let validFloat := match floatValidation with | .ok module => some module | .error _ => none
  let validFloatPhiVararg := match floatPhiVarargValidation with | .ok module => some module | .error _ => none
  let validCallableTransport := match callableTransportValidation with | .ok module => some module | .error _ => none
  let validRuntimeSource := match runtimeSourceValidation with | .ok module => some module | .error _ => none
  let callableStructExecutionPassed ←
    match NecoLean.Llvm.validate callableStructGepModule with
    | .ok module =>
      match ← NecoLean.Llvm.compile { module, outputPath := callableStructGepPath } with
      | .ok _ =>
        match ← NecoLean.System.run { command := callableStructGepPath.toString } with
        | .error (.nonZeroExit _ code _ _) => pure (code == 42)
        | .ok _ => pure false
        | .error _ => pure false
      | .error _ => pure false
    | .error _ => pure false
  let allocatorExecutionPassed ←
    match NecoLean.Llvm.validate allocatorStructModule, allocatorSources with
    | .ok module, .ok runtimeSources =>
      match ← NecoLean.Llvm.compile { module, outputPath := ".lake/neco-lean-allocator-struct", runtimeSources } with
      | .ok _ =>
        match ← NecoLean.System.run { command := ".lake/neco-lean-allocator-struct" } with
        | .error (.nonZeroExit _ code _ _) => pure (code == 42)
        | .ok _ => pure false
        | .error _ => pure false
      | .error _ => pure false
    | _, _ => pure false
  let nullExecutionPassed ←
    match NecoLean.Llvm.validate nullTransportModule with
    | .ok module =>
      match ← NecoLean.Llvm.compile { module, outputPath := nullTransportPath } with
      | .ok _ =>
        match ← NecoLean.System.run { command := nullTransportPath.toString } with
        | .ok output => pure (output.exitCode == 0)
        | .error _ => pure false
      | .error _ => pure false
    | .error _ => pure false
  let validationMessage := match callValidation, stdoutValidation, unreachableValidation, joinAndCastValidation with
    | .error (.invalidModule message), _, _, _ => s!"llvm-call-validation: {message}"
    | _, .error (.invalidModule message), _, _ => s!"llvm-stdout-validation: {message}"
    | _, _, .error (.invalidModule message), _ => s!"llvm-unreachable-validation: {message}"
    | _, _, _, .error (.invalidModule message) => s!"llvm-join-and-cast-validation: {message}"
    | _, _, _, _ => ""
  if !validationMessage.isEmpty then IO.println validationMessage
  match valid2, valid7, validCall, validStdout, validUnreachable, validJoinAndCast, validFloat, validFloatPhiVararg, validCallableTransport, validRuntimeSource, runtimeSourceRequestSources with
  | some module2, some module7, some callModule, some stdoutModule, some unreachableModule, some joinAndCastModule, some floatModule, some floatPhiVarargModule, some callableTransportModule, some runtimeSourceModule, .ok runtimeSources =>
    let result2 ← NecoLean.Llvm.compile { module := module2, outputPath := path2 }
    let result7 ← NecoLean.Llvm.compile { module := module7, outputPath := path7 }
    let callResult ← NecoLean.Llvm.compile { module := callModule, outputPath := callPath }
    let stdoutResult ← NecoLean.Llvm.compile { module := stdoutModule, outputPath := stdoutPath }
    let unreachableResult ← NecoLean.Llvm.compile { module := unreachableModule, outputPath := unreachablePath }
    let joinAndCastResult ← NecoLean.Llvm.compile { module := joinAndCastModule, outputPath := joinAndCastPath }
    let floatResult ← NecoLean.Llvm.compile { module := floatModule, outputPath := floatPath }
    let floatPhiVarargResult ← NecoLean.Llvm.compile { module := floatPhiVarargModule, outputPath := floatPhiVarargPath }
    let callableTransportResult ← NecoLean.Llvm.compile { module := callableTransportModule, outputPath := callableTransportPath }
    let runtimeSourceResult ← NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := runtimeSourcePath, runtimeSources }
    let changedHeaderResult ←
      match runtimeSourceRequestSources 8 false with
      | .ok sources => NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := ".lake/neco-lean-runtime-source-header", runtimeSources := sources }
      | .error failure => pure (.error failure)
    let changedUnitResult ←
      match runtimeSourceRequestSources 5 true with
      | .ok sources => NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := ".lake/neco-lean-runtime-source-unit", runtimeSources := sources }
      | .error failure => pure (.error failure)
    let removedHeaderResult ←
      match runtimeSources with
      | _ :: unit :: _ => NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := runtimeSourcePath, runtimeSources := [unit] }
      | _ => pure (.error (.duplicateRuntimeSourceName "missing"))
    let hiddenHeaderResult ←
      match runtimeSourceHiddenHeaderSources with
      | .ok sources => NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := ".lake/neco-lean-runtime-hidden-header", runtimeSources := sources }
      | .error failure => pure (.error failure)
    let missingHiddenHeaderResult ←
      match runtimeSourceHiddenHeaderMissingSources with
      | .ok sources => NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := ".lake/neco-lean-runtime-hidden-header", runtimeSources := sources }
      | .error failure => pure (.error failure)
    let duplicateRuntimeSourceResult ←
      match runtimeSources with
      | first :: _ => NecoLean.Llvm.compile { module := runtimeSourceModule, outputPath := ".lake/neco-lean-runtime-duplicate", runtimeSources := [first, first] }
      | [] => pure (.error (.duplicateRuntimeSourceName "missing"))
    match result2, result7, callResult, stdoutResult, unreachableResult, joinAndCastResult, floatResult, floatPhiVarargResult, callableTransportResult, runtimeSourceResult, changedHeaderResult, changedUnitResult, removedHeaderResult, hiddenHeaderResult, missingHiddenHeaderResult, duplicateRuntimeSourceResult with
    | .ok _, .ok _, .ok _, .ok _, .ok _, .ok _, .ok _, .ok _, .ok _, .ok runtimeSourceOutput, .ok _, .ok _, .error (.toolRejected _ _ _ _ _), .ok _, .error (.toolRejected _ _ _ _ _), .error (.duplicateRuntimeSourceName _) =>
      let run2 ← NecoLean.System.run { command := path2.toString }
      let run7 ← NecoLean.System.run { command := path7.toString }
      let runCall ← NecoLean.System.run { command := callPath.toString }
      let runStdout ← NecoLean.System.run { command := stdoutPath.toString }
      let runUnreachable ← NecoLean.System.run { command := unreachablePath.toString }
      let runJoinAndCast ← NecoLean.System.run { command := joinAndCastPath.toString }
      let runFloat ← NecoLean.System.run { command := floatPath.toString }
      let runFloatPhiVararg ← NecoLean.System.run { command := floatPhiVarargPath.toString }
      let runCallableTransport ← NecoLean.System.run { command := callableTransportPath.toString }
      let runRuntimeSource ← NecoLean.System.run { command := runtimeSourcePath.toString }
      let runChangedHeader ← NecoLean.System.run { command := ".lake/neco-lean-runtime-source-header" }
      let runChangedUnit ← NecoLean.System.run { command := ".lake/neco-lean-runtime-source-unit" }
      let runHiddenHeader ← NecoLean.System.run { command := ".lake/neco-lean-runtime-hidden-header" }
      let ir2 ← NecoLean.System.readBytes (path2.toString ++ ".ll")
      let ir7 ← NecoLean.System.readBytes (path7.toString ++ ".ll")
      let irCall ← NecoLean.System.readBytes (callPath.toString ++ ".ll")
      let irStdout ← NecoLean.System.readBytes (stdoutPath.toString ++ ".ll")
      let irUnreachable ← NecoLean.System.readBytes (unreachablePath.toString ++ ".ll")
      let irJoinAndCast ← NecoLean.System.readBytes (joinAndCastPath.toString ++ ".ll")
      let irFloat ← NecoLean.System.readBytes (floatPath.toString ++ ".ll")
      let irFloatPhiVararg ← NecoLean.System.readBytes (floatPhiVarargPath.toString ++ ".ll")
      let irCallableTransport ← NecoLean.System.readBytes (callableTransportPath.toString ++ ".ll")
      let runtimeHeaderPath := (runtimeSourceOutput.runtimeSources.find? (fun artifact => artifact.logicalName == "runtime_fixture.h")).map NecoLean.Llvm.RuntimeSourceArtifact.path
      let runtimeUnitPath := (runtimeSourceOutput.runtimeSources.find? (fun artifact => artifact.logicalName == "runtime_fixture.c")).map NecoLean.Llvm.RuntimeSourceArtifact.path
      let runtimeHeader ← match runtimeHeaderPath with | some path => NecoLean.System.readBytes path | none => pure (.error (.file "runtime_fixture.h" "missing"))
      let runtimeUnit ← match runtimeUnitPath with | some path => NecoLean.System.readBytes path | none => pure (.error (.file "runtime_fixture.c" "missing"))
      let irFiles := [ir2, ir7, irCall, irStdout, irUnreachable, irJoinAndCast, irFloat, irFloatPhiVararg, irCallableTransport].all (fun result => match result with | .ok bytes => !bytes.isEmpty | _ => false)
      let runtimeSourceFiles := match runtimeHeader, runtimeUnit, runtimeSources with
        | .ok headerBytes, .ok unitBytes, headerSource :: unitSource :: _ => headerBytes == headerSource.bytes && unitBytes == unitSource.bytes
        | _, _, _ => false
      let runtimeArtifacts :=
        runtimeSourceOutput.runtimeSources.length == 2 && runtimeSourceOutput.runtimeSourceBundleIdentity == NecoLean.Llvm.runtimeSourceBundleIdentity runtimeSources &&
          runtimeSourceOutput.runtimeSources.all (fun artifact => !artifact.digest.isEmpty && !artifact.path.toString.isEmpty) &&
          runtimeSourceOutput.runtimeSources.any (fun artifact => artifact.logicalName == "runtime_fixture.h" && artifact.kind == .header) &&
          runtimeSourceOutput.runtimeSources.any (fun artifact => artifact.logicalName == "runtime_fixture.c" && artifact.kind == .compilationUnit)
      let irMatches := match ir2, ir7, irCall, irStdout, irUnreachable, irJoinAndCast, irFloat, irFloatPhiVararg, irCallableTransport with
        | .ok bytes2, .ok bytes7, .ok bytesCall, .ok bytesStdout, .ok bytesUnreachable, .ok bytesJoinAndCast, .ok bytesFloat, .ok bytesFloatPhiVararg, .ok bytesCallableTransport =>
          bytes2 == NecoLean.Llvm.encode module2 && bytes7 == NecoLean.Llvm.encode module7 && bytesCall == NecoLean.Llvm.encode callModule && bytesStdout == NecoLean.Llvm.encode stdoutModule && bytesUnreachable == NecoLean.Llvm.encode unreachableModule && bytesJoinAndCast == NecoLean.Llvm.encode joinAndCastModule && bytesFloat == NecoLean.Llvm.encode floatModule && bytesFloatPhiVararg == NecoLean.Llvm.encode floatPhiVarargModule && bytesCallableTransport == NecoLean.Llvm.encode callableTransportModule && (String.fromUTF8! bytesStdout).contains "getelementptr [18 x i8], ptr @fmt, i32 0, i32 0" && (String.fromUTF8! bytesStdout).contains "call i32 (ptr, ...) @printf(ptr %r0)" && (String.fromUTF8! bytesFloatPhiVararg).contains "getelementptr [7 x i8], ptr @float_fmt, i32 0, i32 0" && (String.fromUTF8! bytesFloatPhiVararg).contains "call i32 (ptr, ...) @printf(ptr %r3, double %r2)" && (String.fromUTF8! bytesFloatPhiVararg).contains "phi double" && (String.fromUTF8! bytesFloatPhiVararg).contains "..." && (String.fromUTF8! bytesCallableTransport).contains "call i32 %p0(i32 %p1)"
        | _, _, _, _, _, _, _, _, _ => false
      let exitStatuses := match run2, run7, runCall, runUnreachable, runJoinAndCast, runFloat, runFloatPhiVararg, runCallableTransport, runRuntimeSource, runChangedHeader, runChangedUnit, runHiddenHeader with
        | .error (.nonZeroExit _ 2 _ _), .error (.nonZeroExit _ 7 _ _), .error (.nonZeroExit _ 42 _ _), .error (.nonZeroExit _ _ _ _), .ok joinOutput, .error (.nonZeroExit _ 7 _ _), .ok floatPhiOutput, .error (.nonZeroExit _ 42 _ _), .error (.nonZeroExit _ 42 _ _), .error (.nonZeroExit _ 45 _ _), .error (.nonZeroExit _ 43 _ _), .error (.nonZeroExit _ 53 _ _) => joinOutput.exitCode == 0 && floatPhiOutput.exitCode == 0 && floatPhiOutput.stdout.toList == "2\n".toUTF8.toList
        | _, _, _, _, _, _, _, _, _, _, _, _ => false
      let stdout := match runStdout with | .ok output => output.stdout.toList == "neco-lean stdout\n".toUTF8.toList | _ => false
      if !exitStatuses then IO.println "llvm-exit-status mismatch"
      if !stdout then IO.println "llvm-stdout mismatch"
      report "llvm-execution" (mustTailExecutionPassed && irFiles && irMatches && exitStatuses && stdout && runtimeSourceFiles && runtimeArtifacts && nullExecutionPassed && allocatorExecutionPassed && callableStructExecutionPassed) "typed LLVM execution mismatch"
    | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => report "llvm-execution" false "clang compile failed"
  | _, _, _, _, _, _, _, _, _, _, _ => report "llvm-execution" false "typed LLVM module rejected"

private def fixpointCheck : IO Bool := do
  let subsetRefl (bits : NecoLean.Fixpoint.BitMask) : NecoLean.Fixpoint.isSubset bits bits := by
    apply Nat.eq_of_testBit_eq
    intro index
    change (bits &&& bits).testBit index = bits.testBit index
    simp
  let identityMap : NecoLean.Fixpoint.MonotoneMap 7 := {
    apply := id
    monotone := fun _ _ contained => contained
  }
  let outsideMap : NecoLean.Fixpoint.MonotoneMap 7 := {
    apply := fun _ => 8
    monotone := fun _ _ _ => subsetRefl 8
  }
  let growingMap : NecoLean.Fixpoint.MonotoneMap 7 := {
    apply := fun _ => 1
    monotone := fun _ _ _ => subsetRefl 1
  }
  let initialOutside : NecoLean.Fixpoint.ClosureInput :=
    { universeMask := 7, initialBits := 8, monotoneMap := identityMap }
  let mappedOutside : NecoLean.Fixpoint.ClosureInput :=
    { universeMask := 7, initialBits := 0, monotoneMap := outsideMap }
  let growingInput : NecoLean.Fixpoint.ClosureInput :=
    { universeMask := 7, initialBits := 0, monotoneMap := growingMap }
  let growingResult := NecoLean.Fixpoint.computeClosure growingInput
  let initialFailure := NecoLean.Fixpoint.computeClosure initialOutside
  let mappedFailure := NecoLean.Fixpoint.computeClosure mappedOutside
  let expectedTrace : NecoLean.Fixpoint.ClosureTrace := [
    { currentBits := 0, mappedBits := 1, nextBits := 1,
      remainingMeasure := { currentBitCount := 0, universeBitCount := 3 } },
    { currentBits := 1, mappedBits := 1, nextBits := 1,
      remainingMeasure := { currentBitCount := 1, universeBitCount := 3 } }
  ]
  let rec traceMeasuresStrict : NecoLean.Fixpoint.ClosureTrace → Bool
    | [] => true
    | [_] => true
    | leftEntry :: rightEntry :: remainingEntries =>
      (NecoLean.Fixpoint.remainingBitCount rightEntry.remainingMeasure <
        NecoLean.Fixpoint.remainingBitCount leftEntry.remainingMeasure) &&
      traceMeasuresStrict (rightEntry :: remainingEntries)
  let representativeMonotonicity : NecoLean.Fixpoint.isSubset
      (growingMap.apply 0) (growingMap.apply 1) :=
    growingMap.monotone (by decide) (by decide) (by decide)
  let leastRepresentative : ∀ result, NecoLean.Fixpoint.computeClosure growingInput = .ok result →
      NecoLean.Fixpoint.isSubset result.closureBits 1 := fun result computed =>
    NecoLean.Fixpoint.computeClosure_least_preFixpoint growingInput result 1
      computed (by decide) (by decide) (by decide)
  let resultPassed := match growingResult with
    | .ok result =>
      result.closureBits == 1 && result.trace == expectedTrace &&
      result.trace.getLast?.map (fun entry => entry.nextBits == entry.currentBits) == some true &&
      traceMeasuresStrict result.trace &&
      decide (NecoLean.Fixpoint.isSubset growingInput.initialBits result.closureBits) &&
      decide (NecoLean.Fixpoint.isSubset (growingMap.apply result.closureBits) result.closureBits) &&
      match NecoLean.Fixpoint.computeClosure { growingInput with initialBits := result.closureBits } with
      | .ok repeated => repeated.closureBits == result.closureBits
      | .error _ => false
    | .error _ => false
  let failuresPassed := (match initialFailure with | .error .initialOutsideUniverse => true | _ => false) &&
    match mappedFailure with | .error .mapResultOutsideUniverse => true | _ => false
  let popcountPassed := NecoLean.Fixpoint.popcount 0 == 0 && NecoLean.Fixpoint.popcount 7 == 3
  report "fixpoint" (resultPassed && failuresPassed && popcountPassed)
    "closure failure, ordered trace, monotonicity, least pre-fixpoint, or idempotence mismatch"

private def kdlParseCheck : IO Bool := do
  let source := "/- skipped\n(meta)root (tag)\"arg\" key=#true {\n child 42\n}\n".toUTF8
  let invalidUtf8 := NecoLean.Kdl.parse [255].toByteArray
  let parsed := NecoLean.Kdl.parse source
  let utf8Passed := match invalidUtf8 with
    | .error (.invalidUtf8 0) => true
    | _ => false
  let parsePassed := match parsed with
    | .ok result =>
      result.plain == result.positioned.toPlain &&
      match result.positioned, result.plain with
      | .make [.make (some "meta") "root" entries (some (.make children)) span],
        .make [.make (some "meta") "root" plainEntries (some (.make plainChildren))] =>
          span.start == { line := 2, column := 1, byteOffset := 11 } &&
          span.end.byteOffset == source.size - 1 &&
          match entries, children, plainEntries, plainChildren with
          | [.argument argument, .property property],
            [.make none "child" [.argument childArgument] none _],
            [.argument plainArgument, .property plainProperty],
            [.make none "child" [.argument plainChildArgument] none] =>
              argument.typeAnnotation == some "tag" && argument.value == .string "arg" &&
              property.name == "key" && property.value == .boolean true &&
              NecoLean.Kdl.Value.rawNumber? childArgument.value == some "42" &&
              NecoLean.Kdl.Value.asInt? childArgument.value == some 42 &&
              NecoLean.Kdl.Value.asFloat? childArgument.value == some 42.0 &&
              plainArgument.value == argument.value && plainProperty.value == property.value &&
              plainChildArgument.value == childArgument.value
          | _, _, _, _ => false
      | _, _ => false
    | .error _ => false
  let operationsPassed := match parsed with
    | .ok result =>
      match NecoLean.Kdl.encode result.plain, NecoLean.Kdl.normalize result.plain with
      | .ok encoded, .ok normalized =>
        let encodedRoundtrip := match NecoLean.Kdl.parse encoded.toUTF8 with
          | .ok reparsed => reparsed.plain == result.plain
          | .error _ => false
        let normalizedRoundtrip := match NecoLean.Kdl.parse normalized.toUTF8 with
          | .ok _ => true
          | .error _ => false
        let value : NecoLean.Kdl.GenericValue := .object [("name", .string "x"), ("count", .integer 2)]
        let valueRoundtrip := match NecoLean.Kdl.valueToDocument value with
          | .ok document => match NecoLean.Kdl.documentToValue document with
            | .ok actual => actual == value
            | .error _ => false
          | .error _ => false
        encodedRoundtrip && normalizedRoundtrip && valueRoundtrip &&
          match NecoLean.Kdl.firstNode result.plain with
          | some node => NecoLean.Kdl.nodeName node == "root" && NecoLean.Kdl.propertyValue? node "key" == some (.boolean true)
          | none => false
      | _, _ => false
    | .error _ => false
  let builderPassed :=
    (match NecoLean.Kdl.makeNumber "1" with
    | .ok number => number.raw == "1" && number.asInt == some 1 && number.asFloat == some 1.0
    | _ => false) &&
    (match NecoLean.Kdl.makeNumber "0x2a" with
    | .ok number => number.raw == "0x2a" && number.asInt == none && number.asFloat == none
    | _ => false) &&
    (match NecoLean.Kdl.makeNumber "#inf" with
    | .ok number => number.raw == "#inf" && number.asInt == none && number.asFloat == none
    | _ => false) &&
    (match NecoLean.Kdl.makeNumber "1_000" with
    | .ok number => number.asInt == some 1000 && number.asFloat == some 1000.0
    | _ => false) &&
    (match NecoLean.Kdl.makeNumber "" with
    | .error .emptyNumber => true
    | _ => false) &&
    (match NecoLean.Kdl.makeNumber "not-a-number" with
    | .error (.invalidNumber "not-a-number") => true
    | _ => false) &&
    NecoLean.Kdl.emptyDocument == .make [] &&
    NecoLean.Kdl.makeNode "root" == .make none "root" [] none
  report "kdl" (utf8Passed && parsePassed && operationsPassed && builderPassed)
    "KDL UTF-8, positioned document, encode, normalize, Value, query, or builder mismatch"

private def kdlAstCheck : IO Bool := do
  let path := NecoLean.Kdl.Ast.NamespacePath.parse "alpha.beta"
  let reference := NecoLean.Kdl.Ast.CrossReference.parse "alpha.beta#item"
  let structured := NecoLean.Kdl.parse "kind \"name.id\"\nplain\n".toUTF8
  let structuredPassed := match structured with
    | .ok parsed =>
      match NecoLean.Kdl.documentNodes parsed.plain with
      | first :: second :: _ =>
        match NecoLean.Kdl.Ast.structuredNameFormX first,
            NecoLean.Kdl.Ast.structuredNameFormY second with
        | .ok formX, .ok formY =>
          formX.kind.map NecoLean.Kdl.Ast.NamespacePath.display == some "kind" &&
            NecoLean.Kdl.Ast.NamespacePath.display formX.identifier == "name.id" &&
            formY.kind == none && NecoLean.Kdl.Ast.NamespacePath.display formY.identifier == "plain"
        | _, _ => false
      | _ => false
    | .error _ => false
  let transformFailure := NecoLean.Kdl.parse ".procedure\n".toUTF8
  let transformFailed := match transformFailure with
    | .ok parsed =>
      match NecoLean.Kdl.Ast.expandDotChain parsed.plain "procedure" with
      | .error (.depthJump 0 1) => true
      | _ => false
    | .error _ => false
  let passed := (match path with
    | .ok value => NecoLean.Kdl.Ast.NamespacePath.display value == "alpha.beta"
    | .error _ => false) &&
    (match reference with
    | .ok value => value.path == (NecoLean.Kdl.Ast.NamespacePath.parse "alpha.beta").toOption.getD .empty &&
        value.fragment == some "item"
    | .error _ => false) && structuredPassed && transformFailed
  report "kdl-ast" passed "KDL AST path, reference, structured form, or transform failure mismatch"

private def kdlVectorsCheck : IO Bool := do
  let corpusRoot : System.FilePath := "test/kdl-test-cases"
  let invalidManifest := NecoLean.Kdl.Vectors.parseManifest "invalid"
  let inspected : Except NecoLean.Kdl.Vectors.InspectionFailure NecoLean.Kdl.Vectors.CorpusEvidence ←
    NecoLean.Kdl.Vectors.inspectCorpus corpusRoot
  let manifestFailurePassed := match invalidManifest with
    | .error (.invalidManifestLine 1 "invalid") => true
    | _ => false
  let corpusPassed := match inspected with
    | .ok evidence =>
      evidence.aggregate.manifestEntries == 581 && evidence.aggregate.inputCases == 338 &&
        evidence.aggregate.expectedOutputs == 243 && evidence.aggregate.matchedParse == 243 &&
        evidence.aggregate.matchedReject == 95 && evidence.aggregate.mismatches == 0 &&
        evidence.aggregate.manifestCovered && evidence.aggregate.allMatched
    | .error _ => false
  report "kdl-vectors" (manifestFailurePassed && corpusPassed)
    "KDL vector manifest, corpus evidence, or inspection failure mismatch"

private def tuiCheck : IO Bool := do
  let decoded := NecoLean.Tui.decodeChunk "\u001b[Ax" {}
  let partialDecode := NecoLean.Tui.decodeChunk "\u001b[" {}
  let completed := NecoLean.Tui.decodeChunk "A" partialDecode.remainder
  let screen := NecoLean.Tui.rect 0 0 80 24
  let areas := NecoLean.Tui.frameAreas screen .right 32 8
  let left := NecoLean.Tui.rect 0 0 4 5
  let right := NecoLean.Tui.rect 4 0 3 5
  let geometryEdge := NecoLean.Tui.sharedEdge left right
  let geometryMoved := match geometryEdge with
    | some edge => NecoLean.Tui.applyEdgeDelta edge { amount := 2 } 1
    | none => .error .invalidSharedEdge
  let geometryRestored := match geometryMoved with
    | .ok edge => NecoLean.Tui.applyEdgeDelta edge { amount := -2 } 1
    | .error failure => .error failure
  let sizing := NecoLean.Tui.resolveSizes 9 [.length 3, .fill, .fill]
  let minimumSizing := NecoLean.Tui.resolveSizes 6 [.min 2, .min 2]
  let maximumSizing := NecoLean.Tui.resolveSizes 5 [.max 2, .max 3]
  let ratioSizing := NecoLean.Tui.resolveSizes 100 [.ratio 1 3, .ratio 2 3]
  let wide := NecoLean.Tui.setText (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 1 1)) { x := 0, y := 0 } "界"
  let wideSource := NecoLean.Tui.setText (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 2 1)) { x := 0, y := 0 } "界"
  let wideClipped := NecoLean.Tui.clip wideSource (NecoLean.Tui.rect 1 0 1 1)
  let clipped := NecoLean.Tui.clip
    (NecoLean.Tui.setText (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 3 1)) { x := 0, y := 0 } "abc")
    (NecoLean.Tui.rect 1 0 2 1)
  let logicalLines := NecoLean.Tui.layoutLogicalLine 4
    { linePrefix := { first := ">", continuation := "." }, text := "abcdef" }
  let logical := (List.range logicalLines.length).foldl (fun surface offset =>
    match logicalLines[offset]? with
    | some line => NecoLean.Tui.writeDrawingLine surface { x := 0, y := Int.ofNat offset } 4 line
    | none => surface) (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 4 2))
  let rounded := NecoLean.Tui.drawFrame (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 4 3)) true
  let horizontal := NecoLean.Tui.drawDivider (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 4 1)) (NecoLean.Tui.rect 0 0 4 1)
  let vertical := NecoLean.Tui.drawDivider (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 1 3)) (NecoLean.Tui.rect 0 0 1 3)
  let before := NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 1 1)
  let after := NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 2 1)
  let tree : NecoLean.Tui.Tree := {
    nodes := [{ id := "root", label := "Root", children := [{ id := "first", label := "First" }, { id := "second", label := "Second" }]}]
    expanded := ["root"]
    selected := "root"
  }
  let wrappedTree : NecoLean.Tui.Tree := {
    nodes := [{ id := "wrapped", label := "abcdefghijklmnopqrst", children := [{ id := "child", label := "Child" }] }]
    expanded := ["wrapped"]
    selected := "wrapped"
  }
  let duplicateTree : NecoLean.Tui.Tree := {
    nodes := [{ id := "same", label := "First" }, { id := "same", label := "Second" }]
    selected := "same"
  }
  let rec deepNode : Nat → NecoLean.Tui.UiNode
    | 0 => { id := "deep-0", label := "Deep" }
    | depth + 1 => { id := s!"deep-{depth + 1}", label := "Deep", children := [deepNode depth] }
  let deepExpanded := (List.range 129).map (fun depth => s!"deep-{depth}")
  let deepTree : NecoLean.Tui.Tree := { nodes := [deepNode 128], expanded := deepExpanded, selected := "deep-0" }
  let duplicateDeepTree : NecoLean.Tui.Tree := { nodes := [{ deepNode 128 with id := "deep-0" }], selected := "deep-0" }
  let rows := NecoLean.Tui.flatten tree
  let nextTree := NecoLean.Tui.selectNext tree
  let collapsedTree := NecoLean.Tui.toggleExpanded tree
  let treePassed :=
    (match NecoLean.Tui.validateTree tree with | .ok () => true | _ => false) &&
    (match NecoLean.Tui.validateTree duplicateTree with | .error (.duplicateTreeId "same") => true | _ => false) &&
    (match NecoLean.Tui.validateTree duplicateDeepTree with | .error (.duplicateTreeId "deep-0") => true | _ => false) &&
    (NecoLean.Tui.flatten deepTree).length == 129 &&
    (match NecoLean.Tui.selectById deepTree "deep-0" with | .ok selected => selected.selected == "deep-0" | _ => false) &&
    rows.map (·.id) == ["root", "first", "second"] && nextTree.selected == "first" &&
    (NecoLean.Tui.treeLogicalLine (rows.getD 0 { id := "", label := "", depth := 0, selected := false, expandable := false, expanded := false, linePrefix := { first := "" } })).linePrefix.first == "- " &&
    (NecoLean.Tui.flatten collapsedTree).map (·.id) == ["root"]
  let overlayState : NecoLean.Tui.OverlayState := {
    entries := [
      { id := "back", area := NecoLean.Tui.rect 0 0 3 1, visible := true, order := 0 },
      { id := "front", area := NecoLean.Tui.rect 1 0 2 1, visible := true, capture := true, order := 1 }
    ]
  }
  let restoreState : NecoLean.Tui.OverlayState := {
    entries := [
      { id := "tree", area := NecoLean.Tui.rect 0 0 3 1, visible := true, capture := true, order := 0 },
      { id := "help", area := NecoLean.Tui.rect 1 0 2 1, visible := true, capture := true, order := 1 }
    ]
    focus := some "tree"
  }
  let base := NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 3 1)
  let back := NecoLean.Tui.setText (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 0 0 3 1)) { x := 0, y := 0 } "abc"
  let front := NecoLean.Tui.setText (NecoLean.Tui.emptySurface (NecoLean.Tui.rect 1 0 2 1)) { x := 1, y := 0 } "XY"
  let composed := NecoLean.Tui.compose base overlayState [{ id := "back", surface := back }, { id := "front", surface := front }]
  let focused := NecoLean.Tui.focus overlayState "front"
  let restoredFocus := do
    let focused ← NecoLean.Tui.focus restoreState "help"
    NecoLean.Tui.setVisible focused "help" false
  let duplicateOverlay := NecoLean.Tui.register overlayState { id := "front", area := NecoLean.Tui.rect 0 0 1 1 }
  let viewportItems : List NecoLean.Tui.ViewportItem :=
    [{ id := "a", extent := 1 }, { id := "b", extent := 2 }, { id := "c", extent := 1 }, { id := "d", extent := 2 }]
  let viewport : NecoLean.Tui.ViewportState := { top := 0, anchor := "b", selected := "d", size := 3 }
  let refreshed := NecoLean.Tui.refresh viewport viewportItems
  let selectedViewport := NecoLean.Tui.select refreshed "d" viewportItems
  let viewportPassed := match selectedViewport with
    | .ok value =>
      let scrolled := NecoLean.Tui.scroll value (-1) viewportItems
      let missingAnchor := NecoLean.Tui.refresh { value with top := 3, anchor := "missing" } (viewportItems.take 3)
      match NecoLean.Tui.observe value 40 viewportItems with
      | .ok observed => refreshed.top == 1 && observed.selectionVisible && observed.top == 2 && observed.rows == ["c", "d"] &&
          scrolled.top == 1 && scrolled.anchor == "b" && missingAnchor.top == 2 && missingAnchor.anchor == "c"
      | _ => false
    | _ => false
  let modelResult := NecoLean.Tui.initializeModel tree
  let wrappedModelResult := NecoLean.Tui.initializeModel wrappedTree
  let wrappedPassed := match wrappedModelResult with
    | .ok model =>
      let narrow := { model with width := 20, height := 8, detailColumns := 0 }
      let narrowScreen := NecoLean.Tui.rect 0 0 20 8
      let frame := NecoLean.Tui.renderFrame narrow narrowScreen
      match NecoLean.Tui.update (.mousePress 7 3) narrow with
      | .ok selected =>
        selected.tree.selected == "child" &&
          NecoLean.Tui.cellSymbol (NecoLean.Tui.getCell frame { x := 7, y := 3 }) == "C" &&
          NecoLean.Tui.cellSymbol (NecoLean.Tui.getCell frame { x := 1, y := 7 }) == "─"
      | _ => false
    | _ => false
  let modelPassed := match modelResult with
    | .ok model =>
      let detailArea := NecoLean.Tui.rect 0 0 4 4
      let detailModel := { model with detailLines :=
        [{ linePrefix := { first := "a:" }, text := "123456" }, { linePrefix := { first := "b:" }, text := "x" }] }
      let detailSurface := NecoLean.Tui.renderDetail (NecoLean.Tui.emptySurface detailArea) detailArea detailModel
      let detailPassed := NecoLean.Tui.toAnsi detailSurface == "a:12\n  34\n  56\nb:x "
      let shrinkPassed := match NecoLean.Tui.update (.keyPress "-") { model with width := 40, height := 12, detailColumns := 10 } with
        | .ok shrunk =>
          let frame := NecoLean.Tui.renderFrame shrunk (NecoLean.Tui.rect 0 0 40 12)
          shrunk.detailColumns == 8 &&
            NecoLean.Tui.cellSymbol (NecoLean.Tui.getCell frame { x := 1, y := 11 }) == "─"
        | _ => false
      let ignoredKeys := ["j", "k", "p", " ", "=", "escape"]
      let ignoredPassed := ignoredKeys.all (fun key =>
        match NecoLean.Tui.update (.keyPress key) model with
        | .ok unchanged => unchanged == model
        | .error _ => false)
      match NecoLean.Tui.update (.keyPress "?") model with
      | .ok shown =>
        match NecoLean.Tui.update (.keyPress "down") shown, NecoLean.Tui.update (.keyPress "escape") shown,
            NecoLean.Tui.update (.keyPress "ctrl-c") model with
        | .ok captured, .ok closed, .ok stopped =>
          match NecoLean.Tui.update (.keyPress "down") closed, NecoLean.Tui.update (.keyPress "t") closed with
          | .ok selected, .ok moved =>
            match NecoLean.Tui.update (.keyPress "+") moved with
            | .ok grown =>
              detailPassed && shrinkPassed && ignoredPassed && shown.overlays.focus == some "help" && captured.tree.selected == "root" &&
                closed.overlays.focus.isNone && selected.tree.selected == "first" && moved.placement == .bottom &&
                grown.detailRows == moved.detailRows + 1 && stopped.quit &&
                (NecoLean.Tui.renderText shown screen).contains "↑/↓" &&
                (NecoLean.Tui.renderText shown screen).contains "escape" &&
                (NecoLean.Tui.renderText shown screen).contains "╭"
            | _ => false
          | _, _ => false
        | _, _, _ => false
      | _ => false
    | _ => false
  let modelBackend : NecoLean.Tui.TerminalBackend Bool := {
    init := pure (.ok false)
    render := fun state _ => pure (.ok state)
    poll := fun state _ => pure (.ok ({ text := if state then "" else "q" }, true))
    nextSize := fun state => pure (.ok ({ width := 80, height := 24 }, state))
    cleanup := fun _ => pure ()
  }
  let modelRun ← match modelResult with
    | .ok model => NecoLean.Tui.runModelWithBackend modelBackend model
    | .error failure => pure (.error failure)
  let idleSampler ← NecoLean.Tui.startSampler ((pure (.ok ()) : IO (Except String Unit))) 1000
  let idleSample ← NecoLean.Tui.takeLatest idleSampler
  NecoLean.Tui.stopSampler idleSampler
  let stoppedSample ← NecoLean.Tui.takeLatest idleSampler
  let errorSampler ← NecoLean.Tui.startSampler ((pure (.error "loader failure") : IO (Except String Unit))) 1000
  IO.sleep 10
  let errorSample ← NecoLean.Tui.takeLatest errorSampler
  NecoLean.Tui.stopSampler errorSampler
  let samplerPassed :=
    (match idleSample with | .ok .unavailable => true | _ => false) &&
    (match stoppedSample with | .error .stopped => true | _ => false) &&
    match errorSample with | .ok (.latest (.error "loader failure")) => true | _ => false
  let decodePassed := decoded.events == [.keyPress "up", .keyPress "x"] &&
    completed.events == [.keyPress "up"] && completed.remainder.text.isEmpty
  let geometryPassed := areas.main.size.width == 45 && areas.detail.size.width == 32 && areas.divider.size.width == 1 &&
    (match geometryRestored with | .ok edge => edge.first == left && edge.second == right | _ => false) &&
    (match sizing with | .ok values => values == [3, 3, 3] | _ => false) &&
    (match minimumSizing with | .ok values => values == [3, 3] | _ => false) &&
    (match maximumSizing with | .ok values => values == [2, 3] | _ => false) &&
    (match ratioSizing with | .ok values => values == [34, 66] | _ => false)
  let surfacePassed := NecoLean.Tui.getCell wide { x := 0, y := 0 } == NecoLean.Tui.emptyCell &&
    NecoLean.Tui.toAnsi wideClipped == " " && NecoLean.Tui.toAnsi clipped == "bc" && NecoLean.Tui.toAnsi logical == ">abc\n.def" &&
    NecoLean.Tui.toAnsi rounded == "╭──╮\n│  │\n╰──╯" && NecoLean.Tui.toAnsi horizontal == "────" &&
    NecoLean.Tui.toAnsi vertical == "│\n│\n│" && (match NecoLean.Tui.diffToAnsi before after with | .clear :: _ => true | _ => false)
  let overlayPassed := NecoLean.Tui.toAnsi composed == "aXY" && NecoLean.Tui.captureTarget overlayState == some "front" &&
    (match focused with | .ok state => state.focus == some "front" | _ => false) &&
    (match restoredFocus with | .ok state => state.focus == some "tree" | _ => false) &&
    match duplicateOverlay with | .error (.duplicateOverlayId "front") => true | _ => false
  let productionPassed := match modelRun with | .ok () => true | _ => false
  report "tui" (decodePassed && geometryPassed && surfacePassed && treePassed && overlayPassed && viewportPassed && wrappedPassed && modelPassed && samplerPassed && productionPassed)
    "TUI composition API, state separation, or terminal lifecycle mismatch"

private def tuiPosixCheck : IO Bool := do
  let clampPassed :=
    NecoLean.Tui.Posix.clampDeciseconds (-1) == 0 &&
      NecoLean.Tui.Posix.clampDeciseconds 0 == 0 &&
      NecoLean.Tui.Posix.clampDeciseconds 1 == 1 &&
      NecoLean.Tui.Posix.clampDeciseconds 100 == 1 &&
      NecoLean.Tui.Posix.clampDeciseconds 101 == 2 &&
      NecoLean.Tui.Posix.clampDeciseconds 25500 == 255 &&
      NecoLean.Tui.Posix.clampDeciseconds 25501 == 255
  let sizePassed :=
    (match NecoLean.Tui.Posix.parseTtySize "24 80\n" with
    | .ok size => size.width == 80 && size.height == 24
    | .error _ => false) &&
    (match NecoLean.Tui.Posix.parseTtySize "24" with | .error (.size _) => true | _ => false) &&
    (match NecoLean.Tui.Posix.parseTtySize "-1 80" with | .error (.size _) => true | _ => false) &&
    (match NecoLean.Tui.Posix.parseTtySize "24 eight" with | .error (.size _) => true | _ => false)
  let commandPassed := NecoLean.Tui.Posix.sttyCommand 101 == "stty raw -echo min 0 time 2 </dev/tty"
  let nonTty ← NecoLean.Tui.Posix.backend.init
  let nonTtyPassed := match nonTty with | .error (.unsupported _) => true | _ => false
  let systemSource ← NecoLean.System.readBytes "NecoLean/System.lean"
  let posixSource ← NecoLean.System.readBytes "NecoLean/Tui/Posix.lean"
  let systemText := match systemSource with | .ok bytes => String.fromUTF8! bytes | .error _ => ""
  let posixText := match posixSource with | .ok bytes => String.fromUTF8! bytes | .error _ => ""
  let stdinLocalityPassed :=
    systemText.contains "private def writeStdin" &&
      systemText.contains "spawned.takeStdin" &&
      systemText.contains "let stdoutTask ← IO.asTask" &&
      systemText.contains "let stderrTask ← IO.asTask" &&
      systemText.contains "let stdinTask ← IO.asTask" &&
      systemText.contains "handle.write stdin" &&
      systemText.contains "handle.flush" &&
      (systemText.splitOn "let stdinTask ← IO.asTask" |>.drop 1 |>.any (·.contains "child.wait"))
  let lifecyclePassed :=
    posixText.contains "savedModes : Option String" &&
      posixText.contains "rawModeStarted : Bool" &&
      posixText.contains "alternateScreenStarted : Bool" &&
      posixText.contains "cursorHideStarted : Bool" &&
      posixText.contains "mouseReportingStarted : Bool" &&
      posixText.contains "let started := { initial with mouseReportingStarted := false }" &&
      posixText.contains "let started := { afterMouse with cursorHideStarted := false }" &&
      posixText.contains "let started := { afterCursor with alternateScreenStarted := false }" &&
      posixText.contains "private def attempt" &&
      posixText.contains "attempt (disableMouse started.stdout)" &&
      posixText.contains "attempt (showCursor started.stdout)" &&
      posixText.contains "attempt (leaveAlternate started.stdout)" &&
      posixText.contains "let _ ← attempt afterAlternate.stdout.flush" &&
      posixText.contains "attempt (restoreTtyModes savedModes)" &&
      posixText.contains "let _ ← attempt afterModes.stdout.flush" &&
      (posixText.splitOn "attempt (disableMouse started.stdout)" |>.drop 1 |>.any (·.contains "attempt (showCursor started.stdout)")) &&
      (posixText.splitOn "attempt (showCursor started.stdout)" |>.drop 1 |>.any (·.contains "attempt (leaveAlternate started.stdout)")) &&
      (posixText.splitOn "attempt (leaveAlternate started.stdout)" |>.drop 1 |>.any (·.contains "let _ ← attempt afterAlternate.stdout.flush")) &&
      (posixText.splitOn "let _ ← attempt afterAlternate.stdout.flush" |>.drop 1 |>.any (·.contains "attempt (restoreTtyModes savedModes)")) &&
      (posixText.splitOn "attempt (restoreTtyModes savedModes)" |>.drop 1 |>.any (·.contains "let _ ← attempt afterModes.stdout.flush")) &&
      posixText.contains "restoreTerminal rawStarted" &&
      posixText.contains "restoreTerminal alternateStarted" &&
      posixText.contains "restoreTerminal cursorStarted" &&
      posixText.contains "restoreTerminal mouseStarted" &&
      posixText.contains "restoreTerminal { mouseStarted with size }" &&
      posixText.contains "cleanup := restoreTerminal" &&
      posixText.contains "cleanup := restoreTerminal"
  let modeRequestPassed :=
    posixText.contains "command := \"/bin/sh\"" &&
      posixText.contains "stty \\\"$(cat)\\\" </dev/tty" &&
      posixText.contains "stdin := savedModes.toUTF8"
  report "tui-posix" (clampPassed && sizePassed && commandPassed && nonTtyPassed &&
    stdinLocalityPassed && lifecyclePassed && modeRequestPassed)
    "POSIX helper, non-TTY init, stdin locality, saved mode request, or cleanup lifecycle mismatch"

private def scannerTokenCheck : IO Bool := do
  let delimiters := [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20].map (fun byte =>
    match NecoLean.Scanner.scanToken (NecoLean.Scanner.create ([byte, 0x61].toByteArray)) with
    | .ok (token, successor) => token == "a" && successor.position == 2
    | .error _ => false)
  let trailing := NecoLean.Scanner.scanToken (NecoLean.Scanner.create "word ".toUTF8)
  let invalidUtf8 := NecoLean.Scanner.scanToken (NecoLean.Scanner.create [255].toByteArray)
  let whitespace := NecoLean.Scanner.scanToken (NecoLean.Scanner.create " \t\n".toUTF8)
  let passed := delimiters.all id &&
    (match trailing with | .ok (token, successor) => token == "word" && successor.position == 4 | _ => false) &&
    (match invalidUtf8 with | .error .invalidUtf8 => true | _ => false) &&
    match whitespace with | .error .unexpectedEnd => true | _ => false
  report "scanner-token" passed "token delimiter, UTF-8, or end-of-input mismatch"

private def scannerPositionCheck : IO Bool := do
  let token := NecoLean.Scanner.scanToken (NecoLean.Scanner.create " a b".toUTF8)
  let integer := NecoLean.Scanner.scanInt (NecoLean.Scanner.create " 42 ".toUTF8)
  let line := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "a\r\nb\n".toUTF8)
  let passed :=
    (match token with | .ok (value, successor) => value == "a" && successor.position == 2 | _ => false) &&
    (match integer with | .ok (value, successor) => value == 42 && successor.position == 3 | _ => false) &&
    match line with | .ok (value, successor) => value == "a" && successor.position == 3 | _ => false
  report "scanner-position" passed "scanner successor position mismatch"

private def scannerFailureCheck : IO Bool := do
  let unsigned := NecoLean.Scanner.scanInt (NecoLean.Scanner.create "+1".toUTF8)
  let signedPlus := NecoLean.Scanner.scanSignedInt (NecoLean.Scanner.create "+1".toUTF8)
  let signOnly := NecoLean.Scanner.scanSignedInt (NecoLean.Scanner.create "-".toUTF8)
  let nonAscii := NecoLean.Scanner.scanInt (NecoLean.Scanner.create "１２".toUTF8)
  let arbitrary := NecoLean.Scanner.scanSignedInt (NecoLean.Scanner.create "123456789012345678901234567890".toUTF8)
  let unexpected := NecoLean.Scanner.scanToken (NecoLean.Scanner.create ByteArray.empty)
  let invalidUtf8 := NecoLean.Scanner.scanLine (NecoLean.Scanner.create [255, 10].toByteArray)
  let passed :=
    (match unsigned with | .error .invalidInteger => true | _ => false) &&
    (match signedPlus with | .error .invalidInteger => true | _ => false) &&
    (match signOnly with | .error .invalidInteger => true | _ => false) &&
    (match nonAscii with | .error .invalidInteger => true | _ => false) &&
    (match arbitrary with | .ok (value, _) => value == 123456789012345678901234567890 | _ => false) &&
    (match unexpected with | .error .unexpectedEnd => true | _ => false) &&
    match invalidUtf8 with | .error .invalidUtf8 => true | _ => false
  report "scanner-failure" passed "typed scanner failure or arbitrary precision mismatch"

private def printerCheck : IO Bool := do
  let printer := NecoLean.Printer.append (NecoLean.Printer.append NecoLean.Printer.empty "first".toUTF8) " second".toUTF8
  let path : NecoLean.System.FilePath := ".lake/neco-lean-printer.bin"
  let written ← NecoLean.Printer.writeTo path printer
  let read ← NecoLean.System.readBytes path
  let missing ← NecoLean.Printer.writeTo ".lake/neco-lean-printer-missing/output.bin" printer
  let expected := "first second".toUTF8
  let passed := NecoLean.Printer.finish NecoLean.Printer.empty == ByteArray.empty && NecoLean.Printer.finish printer == expected &&
    (match written with | .ok bytes => bytes == expected | _ => false) &&
    (match read with | .ok bytes => bytes == expected | _ => false) &&
    match missing with | .error (.file _ _) => true | _ => false
  report "printer" passed "printer accumulation or filesystem write mismatch"

private def scannerByteInputCheck : IO Bool := do
  let source := [0x31, 0x32, 0x20, 0xFF].toByteArray
  let first := NecoLean.Scanner.scanInt (NecoLean.Scanner.create source)
  let second := match first with | .ok (_, successor) => NecoLean.Scanner.scanToken successor | .error failure => .error failure
  let passed :=
    (match first with | .ok (value, successor) => value == 12 && successor.bytes == source && successor.position == 2 | _ => false) &&
    match second with | .error .invalidUtf8 => true | _ => false
  report "scanner-byte-input" passed "scanner did not preserve direct byte input"

private def scannerPrinterRoundtripCheck : IO Bool := do
  let values : List Int := [-10, 0, 7, 123456789012345678901234567890]
  let printer := values.foldl (fun current value => NecoLean.Printer.append current (s!"{value} ".toUTF8)) NecoLean.Printer.empty
  let rec scanValues (scanner : NecoLean.Scanner) (remaining : Nat) : Except NecoLean.Scanner.Failure (List Int) :=
    match remaining with
    | 0 => .ok []
    | count + 1 =>
      match NecoLean.Scanner.scanSignedInt scanner with
      | .error failure => .error failure
      | .ok (value, successor) =>
        match scanValues successor count with
        | .ok tail => .ok (value :: tail)
        | .error failure => .error failure
  let passed := match scanValues (NecoLean.Scanner.create (NecoLean.Printer.finish printer)) values.length with
    | .ok actual => actual == values
    | .error _ => false
  report "scanner-printer-roundtrip" passed "ASCII decimal printer and scanner roundtrip mismatch"

private def scannerLineCheck : IO Bool := do
  let lf := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "first\n".toUTF8)
  let crlf := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "first\r\n".toUTF8)
  let cr := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "first\r".toUTF8)
  let empty := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "\n".toUTF8)
  let unicode := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "あ\n".toUTF8)
  let final := NecoLean.Scanner.scanLine (NecoLean.Scanner.create "last".toUTF8)
  let passed :=
    (match lf with | .ok (value, successor) => value == "first" && successor.position == 6 | _ => false) &&
    (match crlf with | .ok (value, successor) => value == "first" && successor.position == 7 | _ => false) &&
    (match cr with | .ok (value, successor) => value == "first" && successor.position == 6 | _ => false) &&
    (match empty with | .ok (value, successor) => value.isEmpty && successor.position == 1 | _ => false) &&
    (match unicode with | .ok (value, successor) => value == "あ" && successor.position == 4 | _ => false) &&
    match final with | .error .unexpectedEnd => true | _ => false
  report "scanner-line" passed "line terminator or successor mismatch"

private def judgeRequest (directory : System.FilePath) (executable : System.FilePath) : NecoLean.Judge.JudgeRequest :=
  { executablePath := executable, arguments := [], testCaseDirectory := directory, timeLimitSeconds := 10.0 }

private def judgePair : NecoLean.Judge.CasePair :=
  { caseName := "alpha", inputPath := "fixture/alpha.in", expectedOutputPath := "fixture/alpha.out",
    inputBytes := "input".toUTF8, expectedOutput := "output".toUTF8 }

private def judgePairs : NecoLean.Judge.CasePairs :=
  { request := judgeRequest "fixture" "fixture/child", pairs := [judgePair] }

private def judgeEnumeration (fields : List String) : ByteArray :=
  fields.foldl (fun bytes field => bytes ++ field.toUTF8 ++ [0].toByteArray) ByteArray.empty

private def judgeRuntime
    (enumerate : IO (Except NecoLean.Judge.JudgeFailure ByteArray) := pure (.ok (judgeEnumeration ["F", "fixture/alpha.in", "F", "fixture/alpha.out"])))
    (read : System.FilePath -> IO (Except NecoLean.Judge.JudgeFailure ByteArray) := fun path =>
      pure (if path == "fixture/alpha.in" then .ok "input".toUTF8 else if path == "fixture/alpha.out" then .ok "output".toUTF8 else .ok ByteArray.empty))
    (platform : IO (Except NecoLean.Judge.JudgeFailure String) := pure (.ok "Linux"))
    (measurement : IO (Except NecoLean.Judge.JudgeFailure NecoLean.System.ProcessOutput) :=
      pure (.ok { stdout := "output".toUTF8, stderr := "__NECO_JUDGE_ELAPSED__=0.1\n__NECO_JUDGE_RSS_KIB__=1\n".toUTF8, exitCode := 0 }))
    (temporary : (System.FilePath -> IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.MeasuredCase)) -> IO (Except NecoLean.Judge.JudgeFailure NecoLean.Judge.MeasuredCase) :=
      fun callback => callback "fixture/stderr") : NecoLean.Judge.JudgeRuntime :=
  { enumerateCaseFiles := fun _ => enumerate
    readBytes := read
    platformName := fun _ => platform
    runMeasurement := fun _ => measurement
    withTemporaryStderrFile := temporary }

private def prepareJudgeFixtures : IO Bool := do
  match ← NecoLean.System.run { command := "/bin/sh", arguments := ["-c",
    "rm -rf .lake/judge-cases .lake/judge-missing .lake/judge-child.sh; mkdir -p .lake/judge-cases .lake/judge-missing; printf input > .lake/judge-cases/alpha.in; printf output > .lake/judge-cases/alpha.out; printf \"#!/bin/sh\\nprintf output\\nprintf 'child-stderr\\\\n99.0 real\\\\n' >&2\\nexit 3\\n\" > .lake/judge-child.sh; chmod +x .lake/judge-child.sh"] } with
  | .ok _ => return true
  | _ => return false

private def judgeCasePairingCheck : IO Bool := do
  let prepared ← prepareJudgeFixtures
  let paired ← NecoLean.Judge.discoverCasePairs (judgeRequest ".lake/judge-cases" ".lake/judge-child.sh")
  let missing ← NecoLean.Judge.discoverCasePairs (judgeRequest ".lake/judge-missing" ".lake/judge-child.sh")
  let passed := prepared &&
    (match paired with | .ok pairs => pairs.pairs.length == 1 && pairs.pairs.head?.map (·.caseName) == some "alpha" | _ => false) &&
    (match missing with | .ok pairs => pairs.pairs.isEmpty | _ => false)
  report "judge-case-pairing" passed "case pair discovery mismatch"

private def prepareJudgeTimeoutFixtures : IO Bool := do
  match ← NecoLean.System.run { command := "/bin/sh", arguments := ["-c",
    "rm -rf .lake/judge-timeout-cases .lake/judge-timeout-child.sh .lake/judge-timeout-pid; mkdir -p .lake/judge-timeout-cases; printf slow > .lake/judge-timeout-cases/slow.in; printf ignored > .lake/judge-timeout-cases/slow.out; printf fast > .lake/judge-timeout-cases/fast.in; printf accepted > .lake/judge-timeout-cases/fast.out; printf '#!/bin/sh\\ninput=$(cat)\\nif [ \"$input\" = fast ]; then printf accepted; exit 0; fi\\necho $$ > .lake/judge-timeout-pid\\nsleep 5\\nprintf late\\n' > .lake/judge-timeout-child.sh; chmod +x .lake/judge-timeout-child.sh"] } with
  | .ok _ => return true
  | _ => return false

private def judgeMeasurementCheck : IO Bool := do
  let prepared ← prepareJudgeFixtures
  let discovered ← NecoLean.Judge.discoverCasePairs (judgeRequest ".lake/judge-cases" ".lake/judge-child.sh")
  match discovered with
  | .error _ => report "judge-measurement" false "case discovery failed"
  | .ok pairs =>
    let measured ← NecoLean.Judge.executeMeasured pairs
    let passed := prepared && match measured with
      | .ok process => match process.measurements with
        | [measurement] => measurement.stderr == "child-stderr\n99.0 real\n".toUTF8 && measurement.exitCode == 3 &&
          measurement.maximumResidentMemoryBytes > 0 && measurement.elapsedSeconds.isFinite
        | _ => false
      | .error _ => false
    report "judge-measurement" passed "stream separation, deadline, reap, or measurement mismatch"

private def judgeDeadlineCheck : IO Bool := do
  let prepared ← prepareJudgeTimeoutFixtures
  let request : NecoLean.Judge.JudgeRequest :=
    { executablePath := ".lake/judge-timeout-child.sh", arguments := [], testCaseDirectory := ".lake/judge-timeout-cases", timeLimitSeconds := 0.3 }
  let judged ← NecoLean.Judge.judge request
  let pidLive ← NecoLean.System.run { command := "/bin/sh", arguments := ["-c", "test -s .lake/judge-timeout-pid && kill -0 \"$(cat .lake/judge-timeout-pid)\" 2>/dev/null"] }
  let passed := prepared && match judged with
    | .ok { verdict := .TimeLimitExceeded timeout, .. } =>
      timeout.timedOut && (match pidLive with | .error (.nonZeroExit _ _ _ _) => true | _ => false)
    | _ => false
  report "judge-deadline" passed "deadline enforcement, reap, or normal child verdict mismatch"

private def judgeVerdictCheck : IO Bool := do
  let pair (name : String) (expected : String) : NecoLean.Judge.CasePair :=
    { caseName := name, inputPath := "input", expectedOutputPath := "output", inputBytes := ByteArray.empty, expectedOutput := expected.toUTF8 }
  let measurement (name : String) (elapsed : Float) (exitCode : UInt32) (stdout : String) : NecoLean.Judge.MeasuredCase :=
    { casePair := pair name "ok", stdout := stdout.toUTF8, stderr := ByteArray.empty, exitCode, elapsedSeconds := elapsed,
      maximumResidentMemoryBytes := 1, timeLimitSeconds := 1.0 }
  let timedOut := { measurement "timeout" 0.1 3 "no" with timedOut := true }
  let reportValue := NecoLean.Judge.classifyVerdict { measurements := [measurement "accepted" 2.0 0 "ok", measurement "wrong" 0.1 0 "no", measurement "runtime" 0.1 3 "ok", timedOut] }
  let passed := match reportValue with
    | .ok { verdict := .TimeLimitExceeded selected, .. } => selected.casePair.caseName == "timeout"
    | _ => false
  report "judge-verdict" passed "verdict priority mismatch"

private def judgeNoMutationCheck : IO Bool := do
  let prepared ← prepareJudgeFixtures
  let beforeInput ← NecoLean.System.readBytes ".lake/judge-cases/alpha.in"
  let beforeOutput ← NecoLean.System.readBytes ".lake/judge-cases/alpha.out"
  let beforeExecutable ← NecoLean.System.readBytes ".lake/judge-child.sh"
  let judged ← NecoLean.Judge.judge (judgeRequest ".lake/judge-cases" ".lake/judge-child.sh")
  let afterInput ← NecoLean.System.readBytes ".lake/judge-cases/alpha.in"
  let afterOutput ← NecoLean.System.readBytes ".lake/judge-cases/alpha.out"
  let afterExecutable ← NecoLean.System.readBytes ".lake/judge-child.sh"
  let preserved := match beforeInput, beforeOutput, beforeExecutable, afterInput, afterOutput, afterExecutable with
    | .ok leftInput, .ok leftOutput, .ok leftExecutable, .ok rightInput, .ok rightOutput, .ok rightExecutable =>
      leftInput == rightInput && leftOutput == rightOutput && leftExecutable == rightExecutable
    | _, _, _, _, _, _ => false
  let passed := prepared && preserved && match judged with | .ok { verdict := .RuntimeError _, .. } => true | _ => false
  report "judge-no-mutation" passed "judge mutated fixture or executable"

private def judgeFailureCoverageCheck : IO Bool := do
  let request := judgeRequest "fixture" "fixture/child"
  let file ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (read := fun _ => pure (.error (.File "fixture/alpha.in" "read")))) request
  let processStart ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.error (.ProcessStart "/usr/bin/find" "start")))) request
  let temporary ← NecoLean.Judge.withRuntimeExecuteMeasured
    (judgeRuntime (platform := pure (.ok "Darwin")) (temporary := fun _ => pure (.error (.TemporaryStderrFile "temporary")))) judgePairs
  let directory ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.error (.DirectoryEnumerationFailure "/usr/bin/find" 1 "out".toUTF8 "err".toUTF8)))) request
  let malformedDirectory ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.ok "F".toUTF8))) request
  let nonregular ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.ok (judgeEnumeration ["N", "fixture/alpha.in"])))) request
  let invalidName ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.ok (judgeEnumeration ["F", "fixture/alpha.txt"])))) request
  let duplicate ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.ok (judgeEnumeration ["F", "fixture/alpha.in", "F", "fixture/alpha.in"])))) request
  let missing ← NecoLean.Judge.withRuntimeDiscoverCasePairs
    (judgeRuntime (enumerate := pure (.ok (judgeEnumeration ["F", "fixture/alpha.in"])))) request
  let unavailable ← NecoLean.Judge.withRuntimeExecuteMeasured
    (judgeRuntime (platform := pure (.ok "Other"))) judgePairs
  let malformedMeasurement ← NecoLean.Judge.withRuntimeExecuteMeasured
    (judgeRuntime
      (read := fun path => pure (if path == "fixture/stderr" then .ok ByteArray.empty else if path == "fixture/alpha.in" then .ok "input".toUTF8 else .ok "output".toUTF8))
      (measurement := pure (.ok { stdout := "output".toUTF8, stderr := "__NECO_JUDGE_ELAPSED__=invalid\n__NECO_JUDGE_RSS_KIB__=1\n".toUTF8, exitCode := 0 }))) judgePairs
  let passed :=
    (match file with | .error (.File path message) => path == "fixture/alpha.in" && message == "read" | _ => false) &&
    (match processStart with | .error (.ProcessStart command message) => command == "/usr/bin/find" && message == "start" | _ => false) &&
    (match temporary with | .error (.TemporaryStderrFile message) => message == "temporary" | _ => false) &&
    (match directory with | .error (.DirectoryEnumerationFailure command exitCode stdout stderr) => command == "/usr/bin/find" && exitCode == 1 && stdout == "out".toUTF8 && stderr == "err".toUTF8 | _ => false) &&
    (match malformedDirectory with | .error (.MalformedDirectoryEnumeration text) => text == "F" | _ => false) &&
    (match nonregular with | .error (.NonregularCaseFile path) => path == "fixture/alpha.in" | _ => false) &&
    (match invalidName with | .error (.InvalidCaseFileName path) => path == "fixture/alpha.txt" | _ => false) &&
    (match duplicate with | .error (.DuplicateCaseSuffix caseName suffix) => caseName == "alpha" && suffix == ".in" | _ => false) &&
    (match missing with | .error (.MissingCaseCounterpart caseName suffix) => caseName == "alpha" && suffix == ".out" | _ => false) &&
    (match unavailable with | .error (.MeasurementUnavailable caseName field) => caseName == "alpha" && field == "platform" | _ => false) &&
    match malformedMeasurement with | .error (.MalformedMeasurement caseName field text) => caseName == "alpha" && field == "elapsedSeconds" && text == "invalid" | _ => false
  report "judge-failure-coverage" passed "JudgeFailure constructor or payload mismatch"


private def binary64DecimalBits (input : NecoLean.Binary64.Decimal) (expected : Nat) : Bool :=
  match input.toBits with
  | .ok bits => bits.toNat == expected
  | .error _ => false

private def binary64DecimalOverflow (input : NecoLean.Binary64.Decimal) : Bool :=
  match input.toBits with
  | .error (.overflow observed) => observed == input
  | .ok _ => false

private def binary64DecimalSameOutcome (left right : NecoLean.Binary64.Decimal) : Bool :=
  match left.toBits, right.toBits with
  | .ok leftBits, .ok rightBits => leftBits == rightBits
  | .error (.overflow leftInput), .error (.overflow rightInput) => leftInput == left && rightInput == right
  | _, _ => false

private def binary64DecimalRoundingCheck : IO Bool := do
  let minSubnormalMantissa := 5
  let maxSubnormalMantissa := (2 ^ 52 - 1) * (5 ^ 1074)
  let minNormalMantissa := (2 ^ 52) * (5 ^ 1074)
  let minNormalTieMantissa := (2 ^ 53 - 1) * (5 ^ 1075)
  let normalTieUnit := 5 ^ 53
  let maxFiniteMantissa := (2 ^ 53 - 1) * (2 ^ 971)
  let maxOverflowMidpoint := (2 ^ 54 - 1) * (2 ^ 970)
  let firstOverflowInteger := 2 ^ 1024
  let positiveZero := binary64DecimalBits { negative := false, mantissa := 0, exponent := 0 } 0x0000000000000000
  let negativeZero := binary64DecimalBits { negative := true, mantissa := 0, exponent := 0 } 0x8000000000000000
  let ordinary :=
    binary64DecimalBits { negative := false, mantissa := 1, exponent := 0 } 0x3ff0000000000000 &&
    binary64DecimalBits { negative := false, mantissa := 1, exponent := -3 } 0x3f50624dd2f1a9fc &&
    binary64DecimalBits { negative := false, mantissa := 10, exponent := 0 } 0x4024000000000000 &&
    binary64DecimalBits { negative := false, mantissa := 36893488147419107329, exponent := 0 } 0x4400000000000001
  let subnormal :=
    binary64DecimalBits { negative := false, mantissa := minSubnormalMantissa, exponent := -324 } 0x0000000000000001 &&
    binary64DecimalBits { negative := false, mantissa := maxSubnormalMantissa, exponent := -1074 } 0x000fffffffffffff &&
    binary64DecimalBits { negative := false, mantissa := minNormalMantissa, exponent := -1074 } 0x0010000000000000 &&
    binary64DecimalBits { negative := false, mantissa := minNormalTieMantissa, exponent := -1075 } 0x0010000000000000
  let normalTies :=
    binary64DecimalBits { negative := false, mantissa := (2 ^ 53 + 1) * normalTieUnit, exponent := -53 } 0x3ff0000000000000 &&
    binary64DecimalBits { negative := false, mantissa := (2 ^ 53 + 3) * normalTieUnit, exponent := -53 } 0x3ff0000000000002
  let overflow :=
    binary64DecimalBits { negative := false, mantissa := maxFiniteMantissa, exponent := 0 } 0x7fefffffffffffff &&
    binary64DecimalOverflow { negative := false, mantissa := maxOverflowMidpoint, exponent := 0 } &&
    binary64DecimalOverflow { negative := false, mantissa := firstOverflowInteger, exponent := 0 } &&
    binary64DecimalOverflow { negative := true, mantissa := firstOverflowInteger, exponent := 0 } &&
    binary64DecimalOverflow { negative := false, mantissa := firstOverflowInteger + 1, exponent := 0 } &&
    binary64DecimalOverflow { negative := true, mantissa := firstOverflowInteger + 1, exponent := 0 } &&
    binary64DecimalOverflow { negative := false, mantissa := 1, exponent := 1000000000 }
  let underflow :=
    binary64DecimalBits { negative := false, mantissa := 1, exponent := -325 } 0x0000000000000000 &&
    binary64DecimalBits { negative := true, mantissa := 1, exponent := -1000000000 } 0x8000000000000000 &&
    binary64DecimalBits { negative := true, mantissa := 0, exponent := 1000000000 } 0x8000000000000000
  let equivalent :=
    binary64DecimalSameOutcome
      { negative := false, mantissa := 36893488147419107329, exponent := 0 }
      { negative := false, mantissa := 368934881474191073290, exponent := -1 } &&
    binary64DecimalSameOutcome
      { negative := false, mantissa := 1, exponent := 1000000000 }
      { negative := false, mantissa := 10, exponent := 999999999 }
  let passed := positiveZero && negativeZero && ordinary && subnormal && normalTies && overflow && underflow && equivalent
  report "binary64-decimal-rounding" passed "decimal to binary64 rounding mismatch"

private def consumerPackageCheck : IO Bool := do
  match ← NecoLean.System.run { command := "lake", arguments := ["--dir", "test/consumer", "exe", "neco-lean-consumer"] } with
  | .ok _ => report "consumer-package" true ""
  | .error (.nonZeroExit _ code _ stderr) => report "consumer-package" false s!"exit {code}: {(String.fromUTF8? stderr).getD "stderr is not UTF-8"}"
  | .error failure => report "consumer-package" false (mustTailSystemFailureText failure)

private structure Selection where
  names : List String
  run : IO Bool

private def selections : List Selection :=
  [{ names := ["consumer-package"], run := consumerPackageCheck },
   { names := ["binary64-decimal-rounding"], run := binary64DecimalRoundingCheck },
   { names := ["system-filesystem"], run := systemFilesystemCheck },
   { names := ["system-process"], run := systemProcessCheck },
   { names := ["diagnostic"], run := diagnosticCheck },
   { names := ["cli"], run := cliCheck },
   { names := ["json-roundtrip", "json-canonical", "json-invalid"], run := jsonCheck },
   { names := ["digest"], run := digestCheck },
   { names := ["fixpoint"], run := fixpointCheck },
   { names := ["scanner-token"], run := scannerTokenCheck },
   { names := ["scanner-position"], run := scannerPositionCheck },
   { names := ["scanner-failure"], run := scannerFailureCheck },
   { names := ["printer"], run := printerCheck },
   { names := ["scanner-byte-input"], run := scannerByteInputCheck },
   { names := ["scanner-printer-roundtrip"], run := scannerPrinterRoundtripCheck },
   { names := ["scanner-line"], run := scannerLineCheck },
   { names := ["judge-case-pairing"], run := judgeCasePairingCheck },
   { names := ["judge-measurement"], run := judgeMeasurementCheck },
   { names := ["judge-deadline"], run := judgeDeadlineCheck },
   { names := ["judge-verdict"], run := judgeVerdictCheck },
   { names := ["judge-no-mutation"], run := judgeNoMutationCheck },
   { names := ["judge-failure-coverage"], run := judgeFailureCoverageCheck },
   { names := ["kdl", "kdl-parse"], run := kdlParseCheck },
   { names := ["kdl-ast"], run := kdlAstCheck },
   { names := ["kdl-vectors"], run := kdlVectorsCheck },
   { names := ["tui"], run := tuiCheck },
   { names := ["tui-posix"], run := tuiPosixCheck },
   { names := ["llvm-validation"], run := do
      let base ← llvmValidationCheck
      let scalar ← report "llvm-scalar-validation" scalarValidationPassed "scalar instruction validation mismatch"
      return base && scalar },
   { names := ["llvm-pointer-equality"], run := llvmPointerEqualityCheck },
   { names := ["llvm-scalar-instructions"], run := llvmScalarInstructionCheck },
   { names := ["llvm-determinism"], run := do
      let base ← llvmDeterminismCheck
      let scalar ← report "llvm-scalar-determinism" scalarDeterminismPassed "scalar instruction encoding mismatch"
      return base && scalar },
   { names := ["llvm-runtime-unit-optimization"], run := llvmRuntimeUnitOptimizationCheck },
   { names := ["llvm-platform-prerequisite"], run := llvmPlatformPrerequisiteCheck },
   { names := ["llvm-static-library"], run := llvmStaticLibraryCheck },
   { names := ["llvm-execution"], run := do
      let objectCompilationPassed ← llvmObjectCompilationCheck
      let objectOptimizationPassed ← llvmObjectOptimizationCheck
      let objectLinkPassed ← llvmObjectLinkCheck
      let executionPassed ← llvmExecutionCheck
      let truthTablePassed ← llvmFcmpTruthTableExecutionCheck
      let scalarPassed ← scalarExecutionPassed
      let scalarPassed ← report "llvm-scalar-execution" scalarPassed "scalar instruction execution mismatch"
      return objectCompilationPassed && objectOptimizationPassed && objectLinkPassed && executionPassed && truthTablePassed && scalarPassed }]

private def selected (selector : String) : IO Bool := do
  if selector == "all" then
    let results ← selections.mapM Selection.run
    return results.all id
  match selections.find? (fun selection => selection.names.contains selector) with
  | some selection => selection.run
  | none =>
    IO.eprintln s!"failed: unknown selector {selector}"
    return false

def main (arguments : List String) : IO UInt32 := do
  match arguments.dropWhile (· == "--") with
  | ["llvm-compile-probe", outputPath] => llvmCompileProbe outputPath
  | selector :: _ => return if ← selected selector then 0 else 1
  | [] => return if ← selected "all" then 0 else 1
