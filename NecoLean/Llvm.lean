import NecoLean.System
import NecoLean.Digest
import Init.Data.Nat.Bitwise
import Std.Data.HashMap
import Std.Data.HashSet

set_option autoImplicit false

namespace NecoLean.Llvm

structure ResultId where
  value : Nat
  deriving Repr, BEq, DecidableEq

inductive ValueType where
  | void
  | integer (bits : Nat)
  | float64
  | pointer (pointee : Option ValueType)
  | functionPointer (parameters : List ValueType) (result : ValueType) (variadic : Bool)
  | constructor
  | array (elementType : ValueType) (length : Nat)
  | struct (fields : List ValueType)
  deriving Repr, BEq

structure CallableSignature where
  parameters : List ValueType
  result : ValueType
  variadic : Bool := false
  deriving Repr, BEq

mutual
  private def decEqValueType : (left right : ValueType) → Decidable (left = right)
    | .void, .void => isTrue rfl
    | .integer left, .integer right =>
      match decEq left right with
      | isTrue same => isTrue (by cases same; rfl)
      | isFalse different => isFalse (by intro same; cases same; exact different rfl)
    | .float64, .float64 => isTrue rfl
    | .pointer left, .pointer right =>
      match decEqValueTypeOption left right with
      | isTrue same => isTrue (by cases same; rfl)
      | isFalse different => isFalse (by intro same; cases same; exact different rfl)
    | .functionPointer leftParameters leftResult leftVariadic, .functionPointer rightParameters rightResult rightVariadic =>
      match decEqValueTypeList leftParameters rightParameters, decEqValueType leftResult rightResult, decEq leftVariadic rightVariadic with
      | isTrue sameParameters, isTrue sameResult, isTrue sameVariadic =>
        isTrue (by cases sameParameters; cases sameResult; cases sameVariadic; rfl)
      | isFalse differentParameters, _, _ =>
        isFalse (by intro same; cases same; exact differentParameters rfl)
      | _, isFalse differentResult, _ =>
        isFalse (by intro same; cases same; exact differentResult rfl)
      | _, _, isFalse differentVariadic =>
        isFalse (by intro same; cases same; exact differentVariadic rfl)
    | .constructor, .constructor => isTrue rfl
    | .array leftType leftLength, .array rightType rightLength =>
      match decEqValueType leftType rightType, decEq leftLength rightLength with
      | isTrue sameType, isTrue sameLength =>
        isTrue (by cases sameType; cases sameLength; rfl)
      | isFalse differentType, _ =>
        isFalse (by intro same; cases same; exact differentType rfl)
      | _, isFalse differentLength =>
        isFalse (by intro same; cases same; exact differentLength rfl)
    | .struct leftFields, .struct rightFields =>
      match decEqValueTypeList leftFields rightFields with
      | isTrue same => isTrue (by cases same; rfl)
      | isFalse different => isFalse (by intro same; cases same; exact different rfl)
    | .void, .integer _ => isFalse (by intro same; cases same)
    | .void, .float64 => isFalse (by intro same; cases same)
    | .void, .pointer _ => isFalse (by intro same; cases same)
    | .void, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .void, .constructor => isFalse (by intro same; cases same)
    | .void, .array _ _ => isFalse (by intro same; cases same)
    | .integer _, .void => isFalse (by intro same; cases same)
    | .integer _, .float64 => isFalse (by intro same; cases same)
    | .integer _, .pointer _ => isFalse (by intro same; cases same)
    | .integer _, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .integer _, .constructor => isFalse (by intro same; cases same)
    | .integer _, .array _ _ => isFalse (by intro same; cases same)
    | .float64, .void => isFalse (by intro same; cases same)
    | .float64, .integer _ => isFalse (by intro same; cases same)
    | .float64, .pointer _ => isFalse (by intro same; cases same)
    | .float64, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .float64, .constructor => isFalse (by intro same; cases same)
    | .float64, .array _ _ => isFalse (by intro same; cases same)
    | .pointer _, .void => isFalse (by intro same; cases same)
    | .pointer _, .integer _ => isFalse (by intro same; cases same)
    | .pointer _, .float64 => isFalse (by intro same; cases same)
    | .pointer _, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .pointer _, .constructor => isFalse (by intro same; cases same)
    | .pointer _, .array _ _ => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .void => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .integer _ => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .float64 => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .pointer _ => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .constructor => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .array _ _ => isFalse (by intro same; cases same)
    | .constructor, .void => isFalse (by intro same; cases same)
    | .constructor, .integer _ => isFalse (by intro same; cases same)
    | .constructor, .float64 => isFalse (by intro same; cases same)
    | .constructor, .pointer _ => isFalse (by intro same; cases same)
    | .constructor, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .constructor, .array _ _ => isFalse (by intro same; cases same)
    | .array _ _, .void => isFalse (by intro same; cases same)
    | .array _ _, .integer _ => isFalse (by intro same; cases same)
    | .array _ _, .float64 => isFalse (by intro same; cases same)
    | .array _ _, .pointer _ => isFalse (by intro same; cases same)
    | .array _ _, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .array _ _, .constructor => isFalse (by intro same; cases same)
    | .struct _, .void => isFalse (by intro same; cases same)
    | .struct _, .integer _ => isFalse (by intro same; cases same)
    | .struct _, .float64 => isFalse (by intro same; cases same)
    | .struct _, .pointer _ => isFalse (by intro same; cases same)
    | .struct _, .functionPointer _ _ _ => isFalse (by intro same; cases same)
    | .struct _, .constructor => isFalse (by intro same; cases same)
    | .struct _, .array _ _ => isFalse (by intro same; cases same)
    | .void, .struct _ => isFalse (by intro same; cases same)
    | .integer _, .struct _ => isFalse (by intro same; cases same)
    | .float64, .struct _ => isFalse (by intro same; cases same)
    | .pointer _, .struct _ => isFalse (by intro same; cases same)
    | .functionPointer _ _ _, .struct _ => isFalse (by intro same; cases same)
    | .constructor, .struct _ => isFalse (by intro same; cases same)
    | .array _ _, .struct _ => isFalse (by intro same; cases same)

  private def decEqValueTypeOption : (left right : Option ValueType) → Decidable (left = right)
    | none, none => isTrue rfl
    | some left, some right =>
      match decEqValueType left right with
      | isTrue same => isTrue (by cases same; rfl)
      | isFalse different => isFalse (by intro same; cases same; exact different rfl)
    | none, some _ => isFalse (by intro same; cases same)
    | some _, none => isFalse (by intro same; cases same)

  private def decEqValueTypeList : (left right : List ValueType) → Decidable (left = right)
    | [], [] => isTrue rfl
    | leftHead :: leftTail, rightHead :: rightTail =>
      match decEqValueType leftHead rightHead, decEqValueTypeList leftTail rightTail with
      | isTrue sameHead, isTrue sameTail =>
        isTrue (by cases sameHead; cases sameTail; rfl)
      | isFalse differentHead, _ =>
        isFalse (by intro same; cases same; exact differentHead rfl)
      | _, isFalse differentTail =>
        isFalse (by intro same; cases same; exact differentTail rfl)
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
end

instance : DecidableEq ValueType := decEqValueType

instance : DecidableEq CallableSignature := by
  intro left right
  cases left with
  | mk leftParameters leftResult leftVariadic =>
    cases right with
    | mk rightParameters rightResult rightVariadic =>
      match decEqValueTypeList leftParameters rightParameters, decEqValueType leftResult rightResult, decEq leftVariadic rightVariadic with
      | isTrue sameParameters, isTrue sameResult, isTrue sameVariadic =>
        exact isTrue (by cases sameParameters; cases sameResult; cases sameVariadic; rfl)
      | isFalse differentParameters, _, _ =>
        exact isFalse (by intro same; cases same; exact differentParameters rfl)
      | _, isFalse differentResult, _ =>
        exact isFalse (by intro same; cases same; exact differentResult rfl)
      | _, _, isFalse differentVariadic =>
        exact isFalse (by intro same; cases same; exact differentVariadic rfl)

inductive Operand where
  | parameter (index : Nat) (type : ValueType)
  | local (result : ResultId) (type : ValueType)
  | null (type : ValueType)
  | integer (bits : Nat) (value : Int)
  | float64 (bits : UInt64)
  | globalFunction (name : String) (type : ValueType)
  | globalString (name : String) (type : ValueType)
  deriving Repr, BEq

inductive FcmpPredicate where
  | false | oeq | ogt | oge | olt | ole | one | ord
  | uno | ueq | ugt | uge | ult | ule | une | true
  deriving Repr, BEq, DecidableEq

inductive Instruction where
  | alloca (result : ResultId) (type : ValueType)
  | store (value slot : Operand)
  | load (result : ResultId) (slot : Operand)
  | add (result : ResultId) (bits : Nat) (left right : Operand)
  | sub (result : ResultId) (bits : Nat) (left right : Operand)
  | mul (result : ResultId) (bits : Nat) (left right : Operand)
  | sdiv (result : ResultId) (bits : Nat) (left right : Operand)
  | srem (result : ResultId) (bits : Nat) (left right : Operand)
  | bitAnd (result : ResultId) (bits : Nat) (left right : Operand)
  | bitOr (result : ResultId) (bits : Nat) (left right : Operand)
  | bitXor (result : ResultId) (bits : Nat) (left right : Operand)
  | shl (result : ResultId) (bits : Nat) (left right : Operand)
  | lshr (result : ResultId) (bits : Nat) (left right : Operand)
  | ashr (result : ResultId) (bits : Nat) (left right : Operand)
  | icmpEq (result : ResultId) (bits : Nat) (left right : Operand)
  | icmpPtrEq (result : ResultId) (left right : Operand)
  | icmpSlt (result : ResultId) (bits : Nat) (left right : Operand)
  | icmpSle (result : ResultId) (bits : Nat) (left right : Operand)
  | icmpSgt (result : ResultId) (bits : Nat) (left right : Operand)
  | icmpSge (result : ResultId) (bits : Nat) (left right : Operand)
  | fadd (result : ResultId) (left right : Operand)
  | fsub (result : ResultId) (left right : Operand)
  | fmul (result : ResultId) (left right : Operand)
  | fdiv (result : ResultId) (left right : Operand)
  | fneg (result : ResultId) (source : Operand)
  | fcmp (result : ResultId) (predicate : FcmpPredicate) (left right : Operand)
  | makeConstructor (result : ResultId) (tag payload : Operand)
  | extractTag (result : ResultId) (source : Operand)
  | extractPayload (result : ResultId) (source : Operand)
  | call (result : Option ResultId) (callee : Operand) (arguments : List Operand)
  | phi (result : ResultId) (valueType : ValueType) (incoming : List (String × Operand))
  | zext (result : ResultId) (source : Operand) (targetWidth : Nat)
  | sext (result : ResultId) (source : Operand) (targetWidth : Nat)
  | trunc (result : ResultId) (source : Operand) (targetWidth : Nat)
  | bitcast (result : ResultId) (source : Operand) (target : ValueType)
  | getElementPtr (result : ResultId) (pointer : Operand) (indices : List Operand)
  deriving Repr, BEq

inductive Terminator where
  | ret (value : Option Operand)
  | branch (target : String)
  | condBranch (condition : Operand) (thenTarget elseTarget : String)
  | switch (condition : Operand) (defaultTarget : String) (cases : List (Operand × String))
  | mustTailCall (result : Option ResultId) (callee : Operand) (arguments : List Operand)
  | unreachable
  deriving Repr, BEq

structure Block where
  label : String
  instructions : List Instruction := []
  terminator : Option Terminator := none
  deriving Repr, BEq

structure FunctionSignature where
  name : String
  callable : CallableSignature
  deriving Repr, BEq

protected def FunctionSignature.result (signature : FunctionSignature) : ValueType :=
  signature.callable.result

protected def FunctionSignature.parameters (signature : FunctionSignature) : List ValueType :=
  signature.callable.parameters

protected def FunctionSignature.variadic (signature : FunctionSignature) : Bool :=
  signature.callable.variadic

inductive Function where
  | declaration (signature : FunctionSignature)
  | definition (signature : FunctionSignature) (blocks : List Block)
  deriving Repr, BEq

structure GlobalString where
  name : String
  value : String
  deriving Repr, BEq

structure Module where
  targetTriple : Option String := none
  globals : List GlobalString := []
  functions : List Function := []
  deriving Repr, BEq

structure SdkIdentity where
  path : System.FilePath
  settingsDigest : String
  deriving Repr, BEq

structure CompilerIdentity where
  executablePath : System.FilePath
  executableDigest : String
  versionBytes : ByteArray
  versionDigest : String
  targetTriple : String
  sdkIdentity : Option SdkIdentity
  deriving BEq

instance : Repr CompilerIdentity where
  reprPrec value _ := .text s!"CompilerIdentity(executablePath={value.executablePath},executableDigest={value.executableDigest},versionBytes={reprStr value.versionBytes.toList},versionDigest={value.versionDigest},targetTriple={reprStr value.targetTriple},sdkIdentity={reprStr value.sdkIdentity})"

inductive Failure where
  | invalidModule (message : String)
  | invalidUtf8 (source : String)
  | invalidRuntimeSourceName (name : String) (message : String)
  | duplicateRuntimeSourceName (name : String)
  | invalidRuntimeUnitOptimization (runtimeSourceIndex : Nat) (logicalName inputDigest : String) (reason : String)
  | runtimeSourceDirectoryCreation (message : String)
  | runtimeSourceWrite (name : String) (path : System.FilePath) (message : String)
  | artifactFile (operation : String) (path : System.FilePath) (message : String)
  | artifactDirectoryExists (path : System.FilePath)
  | artifactDirectoryAcquisition (path : System.FilePath) (message : String)
  | artifactCleanup (path : System.FilePath) (message : String) (prior : Option Failure)
  | emptyObjectLinkInput
  | compilerIdentityMismatch (expected actual : CompilerIdentity)
  | objectDigestMismatch (path : System.FilePath) (expected actual : String)
  | invalidLinkOutputPath (path : System.FilePath) (message : String)
  | linkPublication (operation : String) (path : System.FilePath) (message : String)
  | toolUnavailable (command : String)
  | toolRejected (command : String) (arguments : List String) (exitCode : UInt32) (stdout stderr : ByteArray)
  deriving BEq

inductive ValidModule where
  | private make (module : Module)

protected def ValidModule.module (valid : ValidModule) : Module :=
  match valid with
  | .make module => module

inductive RuntimeSourceKind where
  | header
  | compilationUnit
  deriving Repr, BEq, DecidableEq

inductive RuntimeSource where
  | private make (logicalName : String) (kind : RuntimeSourceKind) (bytes : ByteArray)
  deriving BEq

protected def RuntimeSource.logicalName : RuntimeSource → String
  | .make logicalName _ _ => logicalName

protected def RuntimeSource.kind : RuntimeSource → RuntimeSourceKind
  | .make _ kind _ => kind

protected def RuntimeSource.bytes : RuntimeSource → ByteArray
  | .make _ _ bytes => bytes

protected def RuntimeSource.digest (source : RuntimeSource) : String :=
  NecoLean.Digest.toHex (NecoLean.Digest.sha256 source.bytes)

private def invalidRuntimeSourceNameReason (name : String) : Option String :=
  if name.isEmpty then some "runtime source name is empty"
  else if name == "." || name == ".." then some "runtime source name is reserved"
  else if name.contains "/" || name.contains "\\" then some "runtime source name must be a relative file name"
  else if name.toList.any (fun character => character == '\u0000') then some "runtime source name contains nul"
  else none

protected def RuntimeSource.create (logicalName : String) (kind : RuntimeSourceKind) (bytes : ByteArray) : Except Failure RuntimeSource :=
  match invalidRuntimeSourceNameReason logicalName with
  | some reason => .error (.invalidRuntimeSourceName logicalName reason)
  | none => .ok (.make logicalName kind bytes)

structure RuntimeSourceArtifact where
  logicalName : String
  kind : RuntimeSourceKind
  digest : String
  path : System.FilePath
  deriving Repr, BEq

inductive RuntimeUnitOptimizationPolicy where
  | o2
  deriving Repr, BEq, DecidableEq

structure RuntimeUnitOptimization where
  runtimeSourceIndex : Nat
  logicalName : String
  inputDigest : String
  optimization : RuntimeUnitOptimizationPolicy
  deriving Repr, BEq

structure StaticLibraryInput where
  path : System.FilePath
  digest : String
  deriving Repr, BEq

structure CompileRequest where
  module : ValidModule
  outputPath : System.FilePath
  runtimeSources : List RuntimeSource := []
  includeDirectories : List System.FilePath := []
  staticLibraries : List StaticLibraryInput := []

structure CompileOutput where
  outputPath : System.FilePath
  process : NecoLean.System.ProcessOutput
  runtimeSources : List RuntimeSourceArtifact := []
  runtimeSourceBundleIdentity : String := ""

inductive ObjectModuleOptimization where
  | none
  | o1
  deriving Repr, BEq

structure ObjectCompileRequest where
  module : ValidModule
  outputDirectory : System.FilePath
  runtimeSources : List RuntimeSource := []
  runtimeUnitOptimizations : List RuntimeUnitOptimization := []
  moduleOptimization : ObjectModuleOptimization := .none
  includeDirectories : List System.FilePath := []

inductive ObjectInputRole where
  | llvmModule
  | runtimeCompilationUnit (runtimeSourceIndex : Nat) (logicalName : String)
  deriving Repr, BEq

inductive CompiledObjectArtifact where
  | private make
      (role : ObjectInputRole)
      (inputDigest : String)
      (outputPath : System.FilePath)
      (outputDigest : String)
      (arguments normalizedArguments : List String)
  deriving Repr, BEq

protected def CompiledObjectArtifact.role : CompiledObjectArtifact → ObjectInputRole
  | .make role _ _ _ _ _ => role

protected def CompiledObjectArtifact.inputDigest : CompiledObjectArtifact → String
  | .make _ digest _ _ _ _ => digest

protected def CompiledObjectArtifact.outputPath : CompiledObjectArtifact → System.FilePath
  | .make _ _ path _ _ _ => path

protected def CompiledObjectArtifact.outputDigest : CompiledObjectArtifact → String
  | .make _ _ _ digest _ _ => digest

protected def CompiledObjectArtifact.arguments : CompiledObjectArtifact → List String
  | .make _ _ _ _ arguments _ => arguments

protected def CompiledObjectArtifact.normalizedArguments : CompiledObjectArtifact → List String
  | .make _ _ _ _ _ arguments => arguments

structure ObjectLinkInput where
  path : System.FilePath
  digest : String
  deriving Repr, BEq

protected def CompiledObjectArtifact.linkInput (artifact : CompiledObjectArtifact) : ObjectLinkInput :=
  { path := artifact.outputPath, digest := artifact.outputDigest }

structure ObjectLinkRequest where
  compilerIdentity : CompilerIdentity
  orderedObjects : List ObjectLinkInput
  outputPath : System.FilePath
  staticLibraries : List StaticLibraryInput := []

inductive SystemLinkClosureIdentity where
  | unresolved (targetTriple : String) (sdkIdentity : Option SdkIdentity) (reason : String)
  deriving Repr, BEq

structure LinkOutputIdentity where
  compilerIdentity : CompilerIdentity
  orderedObjectDigests : List String
  normalizedArguments : List String
  executableDigest : String
  systemLinkClosureIdentity : SystemLinkClosureIdentity
  identityDigest : String
  deriving Repr, BEq

inductive LinkStagingOwnership where
  | private make
      (directory markerPath : System.FilePath)
      (token : String)
      (stagedExecutablePath : System.FilePath)
  deriving BEq

protected def LinkStagingOwnership.directory : LinkStagingOwnership → System.FilePath
  | .make directory _ _ _ => directory

protected def LinkStagingOwnership.markerPath : LinkStagingOwnership → System.FilePath
  | .make _ markerPath _ _ => markerPath

protected def LinkStagingOwnership.stagedExecutablePath : LinkStagingOwnership → System.FilePath
  | .make _ _ _ path => path

inductive OwnedLinkedOutput where
  | private make
      (identity : LinkOutputIdentity)
      (requestedOutputPath : System.FilePath)
      (arguments : List String)
      (process : NecoLean.System.ProcessOutput)
      (ownership : LinkStagingOwnership)
  deriving BEq

protected def OwnedLinkedOutput.identity : OwnedLinkedOutput → LinkOutputIdentity
  | .make identity _ _ _ _ => identity

protected def OwnedLinkedOutput.requestedOutputPath : OwnedLinkedOutput → System.FilePath
  | .make _ path _ _ _ => path

protected def OwnedLinkedOutput.arguments : OwnedLinkedOutput → List String
  | .make _ _ arguments _ _ => arguments

protected def OwnedLinkedOutput.process : OwnedLinkedOutput → NecoLean.System.ProcessOutput
  | .make _ _ _ process _ => process

protected def OwnedLinkedOutput.ownership : OwnedLinkedOutput → LinkStagingOwnership
  | .make _ _ _ _ ownership => ownership

protected def OwnedLinkedOutput.stagedExecutablePath (output : OwnedLinkedOutput) : System.FilePath :=
  output.ownership.stagedExecutablePath

structure PublishedLinkedOutput where
  identity : LinkOutputIdentity
  outputPath : System.FilePath
  arguments : List String
  process : NecoLean.System.ProcessOutput
  deriving BEq

structure OwnedLinkResidual where
  primary : Option Failure
  cleanup : Failure
  ownership : LinkStagingOwnership
  remainingPaths : List System.FilePath
  deriving BEq

inductive ObjectLinkResult where
  | linked (output : OwnedLinkedOutput)
  | failed (failure : Failure)
  | cleanupRetained (residual : OwnedLinkResidual)
  deriving BEq

inductive LinkCleanupResult where
  | released
  | retained (failure : Failure) (ownership : LinkStagingOwnership) (remainingPaths : List System.FilePath)
  deriving BEq

inductive LinkPublicationResult where
  | published (output : PublishedLinkedOutput)
  | notPublished (failure : Failure) (output : OwnedLinkedOutput)
  | finalCreatedUnverified
      (failure : Failure)
      (finalPath : System.FilePath)
      (expectedDigest : String)
      (output : OwnedLinkedOutput)
  | publishedWithResidual (output : PublishedLinkedOutput) (residual : OwnedLinkResidual)
  deriving BEq

inductive ObjectOutputOwnership where
  | private make (directory : System.FilePath) (token : String)
  deriving BEq

protected def ObjectOutputOwnership.directory : ObjectOutputOwnership → System.FilePath
  | .make directory _ => directory

inductive ObjectOutputRootState where
  | observedPresent
  | observedAbsent
  | observationFailed (failure : NecoLean.System.Failure)
  deriving BEq

structure ObjectOutputRootObservation where
  root : System.FilePath
  state : ObjectOutputRootState
  deriving BEq

structure OwnedObjectCleanupResidual where
  cleanup : Failure
  ownership : ObjectOutputOwnership
  rootObservation : ObjectOutputRootObservation
  deriving BEq

inductive ObjectCleanupResult where
  | released
  | retained (residual : OwnedObjectCleanupResidual)
  deriving BEq

inductive ObjectCompileFailure where
  | operation (failure : Failure)
  | cleanupRetained (primary : Failure) (residual : OwnedObjectCleanupResidual)
  deriving BEq

private inductive ObjectOutputAcquireResult where
  | acquired (ownership : ObjectOutputOwnership)
  | failed (failure : Failure)
  | cleanupRetained (primary : Failure) (residual : OwnedObjectCleanupResidual)

inductive ObjectCompileOutput where
  | private make
      (compilerIdentity : CompilerIdentity)
      (runtimeSources : List RuntimeSourceArtifact)
      (runtimeSourceBundleIdentity : String)
      (objects : List CompiledObjectArtifact)
      (ownership : ObjectOutputOwnership)
  deriving BEq

protected def ObjectCompileOutput.compilerIdentity : ObjectCompileOutput → CompilerIdentity
  | .make identity _ _ _ _ => identity

protected def ObjectCompileOutput.runtimeSources : ObjectCompileOutput → List RuntimeSourceArtifact
  | .make _ sources _ _ _ => sources

protected def ObjectCompileOutput.runtimeSourceBundleIdentity : ObjectCompileOutput → String
  | .make _ _ identity _ _ => identity

protected def ObjectCompileOutput.objects : ObjectCompileOutput → List CompiledObjectArtifact
  | .make _ _ _ objects _ => objects

protected def ObjectCompileOutput.ownership : ObjectCompileOutput → ObjectOutputOwnership
  | .make _ _ _ _ ownership => ownership

inductive Platform where
  | linux
  | macOS
  deriving BEq

protected def platformFromName (name : String) : Except Failure Platform :=
  match name.trimAscii.toString with
  | "Linux" => .ok .linux
  | "Darwin" => .ok .macOS
  | other => .error (.toolUnavailable s!"unsupported operating system: {other}")

protected def sdkArguments (platform : Platform) (sdkPath : Option String) : Except Failure (List String) :=
  match platform, sdkPath with
  | .linux, none => .ok []
  | .linux, some _ => .error (.toolUnavailable "Linux SDK path")
  | .macOS, some path => .ok ["-isysroot", path]
  | .macOS, none => .error (.toolUnavailable "xcrun")

private def systemLibraryArguments : Platform → List String
  | .linux => ["-lm"]
  | .macOS => []

protected def clangArguments (platform : Platform) (irPath outputPath : System.FilePath) (runtimeCompilePaths : List System.FilePath) (sdkPath : Option String) : Except Failure (List String) :=
  match NecoLean.Llvm.sdkArguments platform sdkPath with
  | .error failure => .error failure
  | .ok sdk => .ok ([irPath.toString] ++ runtimeCompilePaths.map System.FilePath.toString ++ ["-Wno-override-module"] ++ sdk ++ systemLibraryArguments platform ++ ["-o", outputPath.toString])

private def typeText : ValueType → String
  | .void => "void"
  | .integer bits => s!"i{bits}"
  | .float64 => "double"
  | .pointer _ => "ptr"
  | .functionPointer _ _ _ => "ptr"
  | .constructor => "i128"
  | .array elementType length => s!"[{length} x {typeText elementType}]"
  | .struct [] => "{}"
  | .struct fields =>
    let fieldsText := String.intercalate ", " (fields.map typeText)
    "{ " ++ fieldsText ++ " }"

private def resultText (result : ResultId) : String := s!"%r{result.value}"

private def parameterText (index : Nat) : String := s!"%p{index}"

private def signedIntegerText (bits : Nat) (value : Int) : String :=
  if bits == 1 then
    if value == 0 then "false" else "true"
  else
    s!"{value}"

private def uint64Hex (value : UInt64) : String :=
  let digit : Nat → Char
    | 0 => '0'
    | 1 => '1'
    | 2 => '2'
    | 3 => '3'
    | 4 => '4'
    | 5 => '5'
    | 6 => '6'
    | 7 => '7'
    | 8 => '8'
    | 9 => '9'
    | 10 => 'A'
    | 11 => 'B'
    | 12 => 'C'
    | 13 => 'D'
    | 14 => 'E'
    | _ => 'F'
  let rec loop : Nat → Nat → List Char → List Char
    | 0, _, characters => characters
    | count + 1, number, characters => loop count (number / 16) (digit (number % 16) :: characters)
  String.mk (loop 16 value.toNat [])

protected def integerText (bits : Nat) (value : Int) : String :=
  signedIntegerText bits value

private def operandText : Operand → String
  | .parameter index _ => parameterText index
  | .local result _ => resultText result
  | .null _ => "null"
  | .integer bits value => signedIntegerText bits value
  | .float64 bits => s!"0x{uint64Hex bits}"
  | .globalFunction name _ => s!"@{name}"
  | .globalString name _ => s!"@{name}"

private def operandType : Operand → ValueType
  | .parameter _ type => type
  | .local _ type => type
  | .null type => type
  | .integer bits _ => .integer bits
  | .float64 _ => .float64
  | .globalFunction _ type => type
  | .globalString _ type => type

private def typedOperand (operand : Operand) : String :=
  s!"{typeText (operandType operand)} {operandText operand}"

private def asciiLetter (character : Char) : Bool :=
  (character >= 'A' && character <= 'Z') || (character >= 'a' && character <= 'z')

private def asciiDigit (character : Char) : Bool := character >= '0' && character <= '9'

private def validIdentifier (name : String) : Bool :=
  match name.toList with
  | first :: rest =>
    let validFirst := asciiLetter first || first == '_' || first == '.' || first == '$'
    validFirst && rest.all (fun character => asciiLetter character || asciiDigit character || character == '_' || character == '.' || character == '$')
  | [] => false

private def validTargetTripleComponent (component : String) : Bool :=
  !component.isEmpty && component.toList.all (fun character =>
    asciiLetter character || asciiDigit character || character == '_' || character == '.')

private def validTargetTriple (triple : String) : Bool :=
  let components := triple.splitOn "-"
  components.length >= 3 && components.length <= 5 && components.all validTargetTripleComponent

private def integerValueRange (bits : Nat) : Option (Int × Int) :=
  if bits == 0 || bits > 128 then none
  else if bits == 1 then some (0, 1)
  else
    let magnitude := (2 : Int) ^ (bits - 1)
    some (-magnitude, magnitude - 1)

protected def validIntegerValue (bits : Nat) (value : Int) : Bool :=
  match integerValueRange bits with
  | none => false
  | some (minimum, maximum) => minimum ≤ value && value ≤ maximum

private def validIntegerWidth : Nat → Bool
  | 0 => false
  | bits => bits ≤ 128

private partial def validValueType : ValueType → Bool
  | .void => true
  | .integer bits => validIntegerWidth bits
  | .float64 => true
  | .pointer none => true
  | .pointer (some pointee) => pointee != .void && validValueType pointee
  | .functionPointer parameters result _ => validValueType result && parameters.all (fun type => type != .void && validValueType type)
  | .constructor => true
  | .array elementType _ => elementType != .void && validValueType elementType
  | .struct fields => fields.all (fun field => field != .void && validValueType field)

private def validStorageType : ValueType → Bool
  | .void => false
  | type => validValueType type

private def integerWidth? (type : ValueType) : Option Nat :=
  match type with
  | .integer width => some width
  | _ => none

private def callable? : ValueType → Option CallableSignature
  | .functionPointer parameters result variadic => some { parameters, result, variadic }
  | _ => none


private def gepResultPointee? (pointerType : ValueType) (indices : List Operand) : Option ValueType :=
  match pointerType with
  | .pointer (some basis) =>
    match indices with
    | [] => some basis
    | first :: rest =>
      if (integerWidth? (operandType first)).isNone then none
      else
        rest.foldl
          (fun current index =>
            match current, index with
            | some (.array elementType _), _ =>
              if (integerWidth? (operandType index)).isSome then some elementType else none
            | some (.struct fields), .integer 32 field =>
              if field < 0 then none else fields[field.toNat]?
            | _, _ => none)
          (some basis)
  | _ => none

private def resultType (instruction : Instruction) : Option (ResultId × ValueType) :=
  match instruction with
  | .alloca result type => some (result, .pointer (some type))
  | .store _ _ => none
  | .load result slot =>
    match operandType slot with
    | .pointer (some pointee) => some (result, pointee)
    | _ => none
  | .add result bits _ _ => some (result, .integer bits)
  | .sub result bits _ _ => some (result, .integer bits)
  | .mul result bits _ _ => some (result, .integer bits)
  | .sdiv result bits _ _ => some (result, .integer bits)
  | .srem result bits _ _ => some (result, .integer bits)
  | .bitAnd result bits _ _ => some (result, .integer bits)
  | .bitOr result bits _ _ => some (result, .integer bits)
  | .bitXor result bits _ _ => some (result, .integer bits)
  | .shl result bits _ _ => some (result, .integer bits)
  | .lshr result bits _ _ => some (result, .integer bits)
  | .ashr result bits _ _ => some (result, .integer bits)
  | .icmpEq result _ _ _ => some (result, .integer 1)
  | .icmpPtrEq result _ _ => some (result, .integer 1)
  | .icmpSlt result _ _ _ => some (result, .integer 1)
  | .icmpSle result _ _ _ => some (result, .integer 1)
  | .icmpSgt result _ _ _ => some (result, .integer 1)
  | .icmpSge result _ _ _ => some (result, .integer 1)
  | .fadd result _ _ => some (result, .float64)
  | .fsub result _ _ => some (result, .float64)
  | .fmul result _ _ => some (result, .float64)
  | .fdiv result _ _ => some (result, .float64)
  | .fneg result _ => some (result, .float64)
  | .fcmp result _ _ _ => some (result, .integer 1)
  | .makeConstructor result _ _ => some (result, .constructor)
  | .extractTag result _ => some (result, .integer 64)
  | .extractPayload result _ => some (result, .integer 64)
  | .call result callee _ =>
    match result, callable? (operandType callee) with
    | some item, some signature => if signature.result == .void then none else some (item, signature.result)
    | _, _ => none
  | .phi result valueType _ => some (result, valueType)
  | .zext result _ targetWidth => some (result, .integer targetWidth)
  | .sext result _ targetWidth => some (result, .integer targetWidth)
  | .trunc result _ targetWidth => some (result, .integer targetWidth)
  | .bitcast result _ target => some (result, target)
  | .getElementPtr result pointer indices => (gepResultPointee? (operandType pointer) indices).map (fun pointee => (result, .pointer (some pointee)))

private def terminatorResult : Terminator → Option ResultId
  | .mustTailCall (some result) _ _ => some result
  | _ => none

private structure Definition where
  result : ResultId
  type : ValueType
  block : String
  position : Nat

private abbrev DefinitionIndex := Std.HashMap Nat Definition

private def buildDefinitionIndex (definitions : List Definition) : DefinitionIndex :=
  definitions.foldl
    (fun result definition => result.insert definition.result.value definition)
    (Std.HashMap.emptyWithCapacity definitions.length)

private def findDefinition (definitions : DefinitionIndex) (result : ResultId) : Option Definition :=
  definitions[result.value]?

private def globalStringType (global : GlobalString) : ValueType :=
  .pointer (some (.array (.integer 8) (global.value.toUTF8.size + 1)))

private def findGlobal (globals : List GlobalString) (name : String) : Option GlobalString :=
  globals.find? (fun item => item.name == name)

private def findParameterType : List ValueType → Nat → Option ValueType
  | [], _ => none
  | type :: _, 0 => some type
  | _ :: rest, index + 1 => findParameterType rest index

private structure DominatorIndex where
  indices : Std.HashMap String Nat
  dominatedBy : Nat → Nat → Bool

private abbrev LabelIndex := Std.HashSet String

private def buildLabelIndex (labels : List String) : LabelIndex :=
  labels.foldl (fun index label => index.insert label) Std.HashSet.emptyWithCapacity

private def dominates (dominators : DominatorIndex) (definitionBlock useBlock : String) : Bool :=
  match dominators.indices[useBlock]?, dominators.indices[definitionBlock]? with
  | some useIndex, some definitionIndex => dominators.dominatedBy useIndex definitionIndex
  | _, _ => false

private def availableDefinition (dominators : DominatorIndex) (definition : Definition) (block : String) (position : Nat) : Bool :=
  if definition.block == block then definition.position < position else dominates dominators definition.block block

private def findSignature (signatures : List FunctionSignature) (name : String) : Option FunctionSignature :=
  signatures.find? (fun signature => signature.name == name)

private def validateOperand (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : String) (position : Nat) (operand : Operand) : Bool :=
  match operand with
  | .parameter index type => match findParameterType parameters index with | some expected => expected == type && expected != ValueType.void | none => false
  | .local result type => match findDefinition definitions result with | some definition => definition.type == type && availableDefinition dominators definition block position | none => false
  | .null type => match type with | .pointer _ => validValueType type | _ => false
  | .integer bits value => NecoLean.Llvm.validIntegerValue bits value
  | .float64 _ => true
  | .globalFunction name type =>
    validIdentifier name && validValueType type &&
      match findSignature signatures name, callable? type with
      | some signature, some callable => signature.callable == callable
      | _, _ => false
  | .globalString name type =>
    validIdentifier name && validValueType type &&
      match findGlobal globals name with
      | some global => globalStringType global == type
      | none => false

private def validateOperandList (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : String) (position : Nat) (operands : List Operand) : Bool :=
  operands.all (validateOperand signatures parameters globals definitions dominators block position)

private def sameArgumentTypes (expected : List ValueType) (arguments : List Operand) : Bool :=
  match expected, arguments with
  | [], [] => true
  | expectedType :: expectedRest, argument :: argumentRest => expectedType == operandType argument && sameArgumentTypes expectedRest argumentRest
  | _, _ => false



private def validateCall (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : String) (position : Nat) (result : Option ResultId) (callee : Operand) (arguments : List Operand) : Bool :=
  if !validateOperand signatures parameters globals definitions dominators block position callee || !validateOperandList signatures parameters globals definitions dominators block position arguments then false
  else
    match callable? (operandType callee) with
    | none => false
    | some signature =>
      let fixedArguments := arguments.take signature.parameters.length
      let countValid := if signature.variadic then arguments.length >= signature.parameters.length else arguments.length == signature.parameters.length
      let resultValid := match result with | none => true | some _ => signature.result != .void
      countValid && sameArgumentTypes signature.parameters fixedArguments && resultValid

private def validCast (source : Operand) (targetWidth : Nat) (direction : Bool) : Bool :=
  match integerWidth? (operandType source) with
  | none => false
  | some sourceWidth =>
    validIntegerWidth targetWidth && if direction then sourceWidth < targetWidth else targetWidth < sourceWidth

private def validIntegerBinary (bits : Nat) (left right : Operand) : Bool :=
  validIntegerWidth bits && operandType left == .integer bits && operandType right == .integer bits

private def validBitcast (source target : ValueType) : Bool :=
  match source, target with
  | .integer 64, .float64 => true
  | .float64, .integer 64 => true
  | _, _ => false

private def validateInstruction (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : String) (position : Nat) : Instruction → Bool
  | .alloca _ type => validStorageType type
  | .store value slot =>
    validateOperand signatures parameters globals definitions dominators block position value &&
      validateOperand signatures parameters globals definitions dominators block position slot &&
      match operandType slot with
      | .pointer (some pointee) => operandType value == pointee
      | _ => false
  | .load _ slot =>
    validateOperand signatures parameters globals definitions dominators block position slot &&
      match operandType slot with
      | .pointer (some pointee) => validStorageType pointee
      | _ => false
  | .add _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .sub _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .mul _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .sdiv _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .srem _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .bitAnd _ bits left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && validIntegerBinary bits left right
  | .bitOr _ bits left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && validIntegerBinary bits left right
  | .bitXor _ bits left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && validIntegerBinary bits left right
  | .shl _ bits left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && validIntegerBinary bits left right
  | .lshr _ bits left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && validIntegerBinary bits left right
  | .ashr _ bits left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && validIntegerBinary bits left right
  | .icmpEq _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .icmpPtrEq _ left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && match operandType left, operandType right with | .pointer _, .pointer _ => true | _, _ => false
  | .icmpSlt _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .icmpSle _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .icmpSgt _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .icmpSge _ bits left right => validIntegerWidth bits && validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .integer bits && operandType right == .integer bits
  | .fadd _ left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .float64 && operandType right == .float64
  | .fsub _ left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .float64 && operandType right == .float64
  | .fmul _ left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .float64 && operandType right == .float64
  | .fdiv _ left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .float64 && operandType right == .float64
  | .fneg _ source => validateOperand signatures parameters globals definitions dominators block position source && operandType source == .float64
  | .fcmp _ _ left right => validateOperand signatures parameters globals definitions dominators block position left && validateOperand signatures parameters globals definitions dominators block position right && operandType left == .float64 && operandType right == .float64
  | .makeConstructor _ tag payload => validateOperand signatures parameters globals definitions dominators block position tag && validateOperand signatures parameters globals definitions dominators block position payload && operandType tag == .integer 64 && operandType payload == .integer 64
  | .extractTag _ source => validateOperand signatures parameters globals definitions dominators block position source && operandType source == .constructor
  | .extractPayload _ source => validateOperand signatures parameters globals definitions dominators block position source && operandType source == .constructor
  | .call result callee arguments => validateCall signatures parameters globals definitions dominators block position result callee arguments
  | .phi _ _ _ => true
  | .zext _ source targetWidth => validateOperand signatures parameters globals definitions dominators block position source && validCast source targetWidth true
  | .sext _ source targetWidth => validateOperand signatures parameters globals definitions dominators block position source && validCast source targetWidth true
  | .trunc _ source targetWidth => validateOperand signatures parameters globals definitions dominators block position source && validCast source targetWidth false
  | .bitcast _ source target => validateOperand signatures parameters globals definitions dominators block position source && validBitcast (operandType source) target
  | .getElementPtr _ pointer indices =>
    validateOperand signatures parameters globals definitions dominators block position pointer &&
      validateOperandList signatures parameters globals definitions dominators block position indices &&
      (gepResultPointee? (operandType pointer) indices).isSome

private def labelsOf (blocks : List Block) : List String := blocks.map Block.label

private def stringCounts (values : List String) : Std.HashMap String Nat :=
  values.foldl (fun counts value => counts.insert value ((counts.getD value 0) + 1))
    (Std.HashMap.emptyWithCapacity values.length)

private def hasDuplicateString (values : List String) : Bool :=
  let counts := stringCounts values
  values.any (fun value => (counts.getD value 0) > 1)

private def firstDuplicateString? (values : List String) : Option String :=
  let counts := stringCounts values
  values.find? (fun value => (counts.getD value 0) > 1)

private def hasDuplicateResult (values : List ResultId) : Bool :=
  let counts := values.foldl (fun counts value =>
    counts.insert value.value ((counts.getD value.value 0) + 1))
    (Std.HashMap.emptyWithCapacity values.length)
  values.any (fun value => (counts.getD value.value 0) > 1)

private def hasDuplicateOperand (values : List Operand) : Bool :=
  values.any (fun value => (values.filter (· == value)).length > 1)

private def terminatorTargets : Option Terminator → List String
  | none => []
  | some (.ret _) => []
  | some (.branch target) => [target]
  | some (.condBranch _ thenTarget elseTarget) => [thenTarget, elseTarget]
  | some (.switch _ defaultTarget cases) => defaultTarget :: cases.map Prod.snd
  | some (.mustTailCall _ _ _) => []
  | some .unreachable => []

private abbrev BlockIndex := Std.HashMap String Block
private abbrev LabelSet := Std.HashMap String Unit

private def buildBlockIndex (blocks : List Block) : BlockIndex :=
  blocks.foldl
    (fun result block => result.insert block.label block)
    (Std.HashMap.emptyWithCapacity blocks.length)

private partial def visitReachable
    (blockIndex : BlockIndex) (pending : List String) (visited : LabelSet) : LabelSet :=
  match pending with
  | [] => visited
  | label :: rest =>
    if visited.contains label then
      visitReachable blockIndex rest visited
    else
      let visited := visited.insert label ()
      match blockIndex[label]? with
      | some block => visitReachable blockIndex (terminatorTargets block.terminator ++ rest) visited
      | none => visitReachable blockIndex rest visited

private def discardPhiIncoming (discardedLabels : LabelSet) : Instruction → Instruction
  | .phi result valueType incoming =>
    .phi result valueType (incoming.filter (fun item => !(discardedLabels.contains item.1)))
  | instruction => instruction

def blocksReachableFromEntry (blocks : List Block) : List Block :=
  match blocks with
  | [] => []
  | entry :: _ =>
    let blockIndex := buildBlockIndex blocks
    let emptyVisited : LabelSet := Std.HashMap.emptyWithCapacity blocks.length
    let visited := visitReachable blockIndex [entry.label] emptyVisited
    let discardedLabels : LabelSet :=
      blocks.foldl
        (fun result block =>
          if visited.contains block.label then result else result.insert block.label ())
        (Std.HashMap.emptyWithCapacity blocks.length)
    blocks.filter (fun block => visited.contains block.label) |>.map (fun block =>
      { block with instructions := block.instructions.map (discardPhiIncoming discardedLabels) })

private def predecessorsOf (blocks : List Block) (target : String) : List String :=
  blocks.filterMap (fun block => if (terminatorTargets block.terminator).any (· == target) then some block.label else none)

private abbrev PredecessorIndex := Std.HashMap String (List String)

private def buildPredecessorIndex (blocks : List Block) : PredecessorIndex :=
  let reversed := blocks.foldl (fun index block =>
      ((terminatorTargets block.terminator).foldl
        (fun (state : PredecessorIndex × List String) target =>
          if state.2.any (· == target) then state
          else (state.1.insert target (block.label :: state.1.getD target []), target :: state.2))
        (index, [])).1)
    (Std.HashMap.emptyWithCapacity blocks.length)
  reversed.fold (fun result label predecessors => result.insert label predecessors.reverse)
    (Std.HashMap.emptyWithCapacity blocks.length)

private structure PhiIndex where
  predecessors : PredecessorIndex
  positions : Std.HashMap String Nat

private def buildPhiIndex (blocks : List Block) : PhiIndex :=
  { predecessors := buildPredecessorIndex blocks
    positions := blocks.foldl (fun index block =>
        if index.contains block.label then index
        else index.insert block.label block.instructions.length)
      (Std.HashMap.emptyWithCapacity blocks.length) }

private def predecessorSuccessorIndices (blocks : List Block) (labels : List String) :
    List (List Nat) × List (List Nat) :=
  let labelIndex : Std.HashMap String Nat :=
    (labels.zip (List.range labels.length)).foldl
      (fun result entry => result.insert entry.1 entry.2)
      (Std.HashMap.emptyWithCapacity labels.length)
  let collected : Std.HashMap Nat (List Nat) × Std.HashMap Nat (List Nat) :=
    (blocks.zip (List.range blocks.length)).foldl
      (fun result entry =>
        (terminatorTargets entry.1.terminator).eraseDups.foldl
          (fun result target =>
            match labelIndex[target]? with
            | some targetIndex =>
              (result.1.insert targetIndex (entry.2 :: result.1.getD targetIndex []),
               result.2.insert entry.2 (targetIndex :: result.2.getD entry.2 []))
            | none => result)
          result)
      (Std.HashMap.emptyWithCapacity blocks.length, Std.HashMap.emptyWithCapacity blocks.length)
  ((List.range blocks.length).map (fun index => (collected.1.getD index []).reverse),
   (List.range blocks.length).map (fun index => (collected.2.getD index []).reverse))

private partial def reversePostOrderVisit (successors : Array (List Nat)) (index : Nat)
    (state : Array Bool × List Nat) : Array Bool × List Nat :=
  if state.1.getD index false then state
  else
    let visited := state.1.set! index true
    let after := (successors.getD index []).foldl
      (fun state successor => reversePostOrderVisit successors successor state) (visited, state.2)
    (after.1, index :: after.2)

private inductive DominatorBlockKind where
  | full
  | tree
  deriving BEq

private structure DominatorTree where
  idom : Array Nat
  enter : Array Nat
  exit : Array Nat
  kinds : Array DominatorBlockKind
  count : Nat

private partial def dominatorIntersect (idom rpoNumber : Array Nat) (left right : Nat) : Option Nat :=
  if left == right then some left
  else if rpoNumber.getD left 0 > rpoNumber.getD right 0 then
    let next := idom.getD left left
    if next == left then none else dominatorIntersect idom rpoNumber next right
  else
    let next := idom.getD right right
    if next == right then none else dominatorIntersect idom rpoNumber left next

private def dominatorIdomPass (predecessors : Array (List Nat)) (rpoNumber : Array Nat)
    (undefined : Nat) (order : List Nat) (idom : Array Nat) : Array Nat × Bool :=
  order.foldl (fun state index =>
    let candidate := (predecessors.getD index []).foldl (fun selected predecessor =>
      if state.1.getD predecessor undefined == undefined then selected
      else match selected with
        | none => some (some predecessor)
        | some none => some none
        | some (some current) => some (dominatorIntersect state.1 rpoNumber current predecessor)) none
    match candidate with
    | none => state
    | some none =>
      if state.1.getD index undefined == index then state else (state.1.set! index index, true)
    | some (some chosen) =>
      if state.1.getD index undefined == chosen then state
      else (state.1.set! index chosen, true)) (idom, false)

private partial def dominatorIdomLoop (predecessors : Array (List Nat)) (rpoNumber : Array Nat)
    (undefined : Nat) (order : List Nat) (fuel : Nat) (idom : Array Nat) : Array Nat :=
  match fuel with
  | 0 => idom
  | fuel + 1 =>
    let (next, changed) := dominatorIdomPass predecessors rpoNumber undefined order idom
    if changed then dominatorIdomLoop predecessors rpoNumber undefined order fuel next else next

private partial def dominatorTreeNumberVisit (children : Array (List Nat)) (index : Nat)
    (state : Array Nat × Array Nat × Nat) : Array Nat × Array Nat × Nat :=
  let enter := state.1.set! index state.2.2
  let after := (children.getD index []).foldl
    (fun state child => dominatorTreeNumberVisit children child state)
    (enter, state.2.1, state.2.2 + 1)
  (after.1, after.2.1.set! index after.2.2, after.2.2 + 1)

private def computeDominatorTree (blocks : List Block) : DominatorTree :=
  let labels := labelsOf blocks
  let count := labels.length
  let (predecessorList, successorList) := predecessorSuccessorIndices blocks labels
  let predecessors := predecessorList.toArray
  let successors := successorList.toArray
  let roots := (List.range count).filter (fun index =>
    index == 0 || (predecessors.getD index []).isEmpty)
  let (_, order) := roots.foldr (fun root state => reversePostOrderVisit successors root state)
    (Array.replicate count false, ([] : List Nat))
  let rpoNumber := (order.zip (List.range order.length)).foldl
    (fun numbers item => numbers.set! item.1 item.2) (Array.replicate count count)
  let undefined := count
  let initial := roots.foldl (fun idom root => idom.set! root root) (Array.replicate count undefined)
  let interior := order.filter (fun index => !roots.contains index)
  let idom := dominatorIdomLoop predecessors rpoNumber undefined interior (count + 2) initial
  let children := order.foldl (fun children index =>
    let parent := idom.getD index undefined
    if parent == undefined || parent == index then children
    else children.set! parent (children.getD parent [] ++ [index]))
    (Array.replicate count ([] : List Nat))
  let treeRoots := (List.range count).filter (fun index => idom.getD index undefined == index)
  let (enter, exitNumbers, _) := treeRoots.foldl
    (fun state root => dominatorTreeNumberVisit children root state)
    (Array.replicate count 0, Array.replicate count 0, 1)
  let kinds := (List.range count).foldl (fun kinds index =>
    let kind :=
      if idom.getD index undefined == undefined then DominatorBlockKind.full
      else DominatorBlockKind.tree
    kinds.set! index kind) (Array.replicate count DominatorBlockKind.tree)
  { idom, enter, exit := exitNumbers, kinds, count }

private def dominatorTreeDominates (tree : DominatorTree) (useIndex definitionIndex : Nat) : Bool :=
  if useIndex == definitionIndex then true
  else match tree.kinds.getD useIndex .full with
    | .full => true
    | .tree =>
      match tree.kinds.getD definitionIndex .full with
      | .full => false
      | .tree =>
        tree.enter.getD definitionIndex 0 <= tree.enter.getD useIndex 0 &&
          tree.exit.getD useIndex 0 <= tree.exit.getD definitionIndex 0

private def computeDominatorIndex (blocks : List Block) : DominatorIndex :=
  let labels := labelsOf blocks
  let tree := computeDominatorTree blocks
  let indices := (labels.zip (List.range labels.length)).foldl
    (fun index item => index.insert item.1 item.2) (Std.HashMap.emptyWithCapacity labels.length)
  { indices, dominatedBy := dominatorTreeDominates tree }

private def computeDominators (blocks : List Block) : List (String × List String) :=
  let labels := labelsOf blocks
  let tree := computeDominatorTree blocks
  let labelArray := labels.toArray
  labels.mapIdx (fun index label =>
    let others := match tree.kinds.getD index .full with
      | .full => labels
      | .tree =>
        (List.range tree.count).filterMap (fun candidate =>
          if candidate != index && dominatorTreeDominates tree index candidate then
            labelArray[candidate]?
          else none)
    (label, label :: others))

private def collectBlockDefinitions (block : Block) : List Definition :=
  block.instructions.mapIdx (fun position instruction =>
    match resultType instruction with
    | some (result, type) => some { result, type, block := block.label, position }
    | none => none) |>.filterMap id

private def collectDefinitions : List Block → List Definition
  | [] => []
  | block :: rest => collectBlockDefinitions block ++ collectDefinitions rest

private def validatePhiIncoming (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (phiIndex : PhiIndex) (predecessors : List String) (valueType : ValueType) (incoming : List (String × Operand)) : Bool :=
  let incomingLabels := incoming.map Prod.fst
  incoming.length == predecessors.length && !hasDuplicateString incomingLabels &&
    incomingLabels.all (fun label => predecessors.any (· == label)) &&
    predecessors.all (fun label => incomingLabels.any (· == label)) &&
    incoming.all (fun item =>
      validIdentifier item.1 && operandType item.2 == valueType &&
        validateOperand signatures parameters globals definitions dominators item.1 (phiIndex.positions.getD item.1 0) item.2)

private def isPhi : Instruction → Bool
  | .phi _ _ _ => true
  | _ => false

private def validatePhiFailure? (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (phiIndex : PhiIndex) (block : Block) : Option (Nat × Instruction) :=
  let predecessors := phiIndex.predecessors.getD block.label []
  let rec loop : List Instruction → Option (Nat × Instruction)
    | [] => none
    | .phi result valueType incoming :: rest =>
      if !validStorageType valueType then some (0, .phi result valueType incoming)
      else if !validatePhiIncoming signatures parameters globals definitions dominators phiIndex predecessors valueType incoming then some (0, .phi result valueType incoming)
      else
        match loop rest with
        | some (position, instruction) => some (position + 1, instruction)
        | none => none
    | instruction :: rest => if rest.any isPhi then some (0, instruction) else none
  match loop block.instructions with
  | some (position, instruction) => some (position, instruction)
  | none => none

private def validatePhi (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (phiIndex : PhiIndex) (block : Block) : Bool :=
  (validatePhiFailure? signatures parameters globals definitions dominators phiIndex block).isNone

private def validateMustTailCall (signatures : List FunctionSignature) (caller : CallableSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : String) (position : Nat) (result : Option ResultId) (callee : Operand) (arguments : List Operand) : Bool :=
  if !validateOperand signatures parameters globals definitions dominators block position callee || !validateOperandList signatures parameters globals definitions dominators block position arguments then false
  else
    match callable? (operandType callee) with
    | none => false
    | some signature =>
      !caller.variadic && !signature.variadic && caller == signature &&
        sameArgumentTypes signature.parameters arguments &&
        match result, signature.result with
        | none, .void => true
        | some _, .void => false
        | none, _ => false
        | some _, _ => true

private def validateTerminator (signatures : List FunctionSignature) (functionSignature : CallableSignature) (labels : LabelIndex) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : String) (position : Nat) : Terminator → Bool
  | .ret none => functionSignature.result == .void
  | .ret (some value) => functionSignature.result != .void && validateOperand signatures parameters globals definitions dominators block position value && operandType value == functionSignature.result
  | .branch target => validIdentifier target && labels.contains target
  | .condBranch condition thenTarget elseTarget => validateOperand signatures parameters globals definitions dominators block position condition && operandType condition == .integer 1 && validIdentifier thenTarget && validIdentifier elseTarget && labels.contains thenTarget && labels.contains elseTarget
  | .switch condition defaultTarget cases =>
    match integerWidth? (operandType condition) with
    | none => false
    | some width =>
      validateOperand signatures parameters globals definitions dominators block position condition &&
        validIdentifier defaultTarget && labels.contains defaultTarget &&
        !hasDuplicateOperand (cases.map Prod.fst) && !hasDuplicateString (cases.map Prod.snd) &&
        cases.all (fun item =>
          match item.1 with
          | .integer caseWidth value =>
            caseWidth == width && validIntegerWidth width && NecoLean.Llvm.validIntegerValue width value &&
              validIdentifier item.2 && labels.contains item.2
          | _ => false)
  | .mustTailCall result callee arguments => validateMustTailCall signatures functionSignature functionSignature.parameters globals definitions dominators block position result callee arguments
  | .unreachable => true

private def functionSignature : Function → FunctionSignature
  | .declaration signature => signature
  | .definition signature _ => signature

private def validateInstructions (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : Block) : Bool :=
  let rec loop : Nat → List Instruction → Bool
    | _, [] => true
    | position, instruction :: rest => validateInstruction signatures parameters globals definitions dominators block.label position instruction && loop (position + 1) rest
  loop 0 block.instructions

private def firstDuplicateResult? (values : List ResultId) : Option ResultId :=
  let counts := values.foldl (fun counts value =>
    counts.insert value.value ((counts.getD value.value 0) + 1))
    (Std.HashMap.emptyWithCapacity values.length)
  values.find? (fun value => (counts.getD value.value 0) > 1)

private def firstInvalidInstructionInBlock? (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (block : Block) : Option (Nat × Instruction) :=
  let rec loop : Nat → List Instruction → Option (Nat × Instruction)
    | _, [] => none
    | position, instruction :: rest =>
      if validateInstruction signatures parameters globals definitions dominators block.label position instruction then
        loop (position + 1) rest
      else
        some (position, instruction)
  loop 0 block.instructions

private def firstInvalidInstruction? (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) : List Block → Nat → Option (Nat × Block × Nat × Instruction)
  | [], _ => none
  | block :: rest, blockIndex =>
    match firstInvalidInstructionInBlock? signatures parameters globals definitions dominators block with
    | some (position, instruction) => some (blockIndex, block, position, instruction)
    | none => firstInvalidInstruction? signatures parameters globals definitions dominators rest (blockIndex + 1)

private def firstInvalidPhi? (signatures : List FunctionSignature) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) (phiIndex : PhiIndex) : List Block → Nat → Option (Nat × Block × Nat × Instruction)
  | [], _ => none
  | block :: rest, blockIndex =>
    match validatePhiFailure? signatures parameters globals definitions dominators phiIndex block with
    | some (position, instruction) => some (blockIndex, block, position, instruction)
    | none => firstInvalidPhi? signatures parameters globals definitions dominators phiIndex rest (blockIndex + 1)

private def firstInvalidTerminator? (signatures : List FunctionSignature) (functionSignature : CallableSignature) (labels : LabelIndex) (parameters : List ValueType) (globals : List GlobalString) (definitions : DefinitionIndex) (dominators : DominatorIndex) : List Block → Nat → Option (Nat × Block × Option Terminator)
  | [], _ => none
  | block :: rest, blockIndex =>
    match block.terminator with
    | none => some (blockIndex, block, none)
    | some terminator =>
      if validateTerminator signatures functionSignature labels parameters globals definitions dominators block.label block.instructions.length terminator then
        firstInvalidTerminator? signatures functionSignature labels parameters globals definitions dominators rest (blockIndex + 1)
      else
        some (blockIndex, block, some terminator)

private def firstInvalidBlock? : List Block → Nat → Option (Nat × Block × String)
  | [], _ => none
  | block :: rest, blockIndex =>
    if !validIdentifier block.label then
      some (blockIndex, block, "invalid-label")
    else if block.terminator.isNone then
      some (blockIndex, block, "missing-terminator")
    else
      firstInvalidBlock? rest (blockIndex + 1)

private def validateFunction (signatures : List FunctionSignature) (globals : List GlobalString) : Function → Option String
  | .declaration signature =>
    if !validIdentifier signature.name then
      some s!"function={signature.name};stage=declaration-name"
    else if !validValueType signature.callable.result then
      some s!"function={signature.name};stage=declaration-result-type"
    else if !signature.callable.parameters.all (fun type => validStorageType type) then
      some s!"function={signature.name};stage=declaration-parameter-type"
    else
      none
  | .definition signature blocks =>
    let labels := labelsOf blocks
    let dominators := computeDominatorIndex blocks
    let definitions := collectDefinitions blocks
    let resultIds := definitions.map Definition.result ++ blocks.filterMap (fun block => block.terminator.bind terminatorResult)
    if !validValueType signature.callable.result then
      some s!"function={signature.name};stage=result-type"
    else if !signature.callable.parameters.all (fun type => validStorageType type) then
      some s!"function={signature.name};stage=parameter-type"
    else if blocks.isEmpty then
      some s!"function={signature.name};stage=blocks-empty"
    else if !validIdentifier signature.name then
      some s!"function={signature.name};stage=function-name"
    else
      match firstDuplicateString? labels with
      | some label => some s!"function={signature.name};stage=duplicate-block-label;block={label}"
      | none =>
        match firstInvalidBlock? blocks 0 with
        | some (blockIndex, block, stage) => some s!"function={signature.name};stage={stage};blockIndex={blockIndex};block={block.label}"
        | none =>
          match firstDuplicateResult? resultIds with
          | some result => some s!"function={signature.name};stage=duplicate-result;result={repr result}"
          | none =>
            let definitionIndex := buildDefinitionIndex definitions
            match firstInvalidInstruction? signatures signature.callable.parameters globals definitionIndex dominators blocks 0 with
            | some (blockIndex, block, position, instruction) =>
              some s!"function={signature.name};stage=instruction;blockIndex={blockIndex};block={block.label};instructionIndex={position};instruction={repr instruction}"
            | none =>
              match firstInvalidPhi? signatures signature.callable.parameters globals definitionIndex dominators (buildPhiIndex blocks) blocks 0 with
              | some (blockIndex, block, position, instruction) => some s!"function={signature.name};stage=phi;blockIndex={blockIndex};block={block.label};instructionIndex={position};instruction={repr instruction}"
              | none =>
                match firstInvalidTerminator? signatures signature.callable (buildLabelIndex labels) signature.callable.parameters globals definitionIndex dominators blocks 0 with
                | some (blockIndex, block, none) => some s!"function={signature.name};stage=terminator;blockIndex={blockIndex};block={block.label};terminator=missing"
                | some (blockIndex, block, some terminator) => some s!"function={signature.name};stage=terminator;blockIndex={blockIndex};block={block.label};terminator={repr terminator}"
                | none => none

private def firstInvalidFunction? (signatures : List FunctionSignature) (globals : List GlobalString) : List Function → Nat → Option (Nat × String)
  | [], _ => none
  | function :: rest, functionIndex =>
    match validateFunction signatures globals function with
    | some message => some (functionIndex, message)
    | none => firstInvalidFunction? signatures globals rest (functionIndex + 1)

private def hexDigit : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'A'
  | 11 => 'B'
  | 12 => 'C'
  | 13 => 'D'
  | 14 => 'E'
  | _ => 'F'

private def byteText (value : UInt8) : String :=
  let number := value.toNat
  s!"\\{hexDigit (number / 16)}{hexDigit (number % 16)}"

private def globalText (global : GlobalString) : String :=
  let bytes := global.value.toUTF8.toList.map byteText
  let body := String.intercalate "" bytes ++ "\\00"
  let length := global.value.toUTF8.size + 1
  s!"@{global.name} = private unnamed_addr constant [{length} x i8] c\"{body}\""

private def signatureParametersText (signature : FunctionSignature) : String :=
  let fixed := signature.callable.parameters.mapIdx (fun index type => s!"{typeText type} {parameterText index}")
  let items := if signature.callable.variadic then fixed ++ ["..."] else fixed
  String.intercalate ", " items

private def signatureText (signature : FunctionSignature) : String :=
  s!"{typeText signature.callable.result} @{signature.name}({signatureParametersText signature})"

private def callableTypeText (signature : CallableSignature) : String :=
  let fixed := signature.parameters.map typeText
  let items := if signature.variadic then fixed ++ ["..."] else fixed
  s!"{typeText signature.result} ({String.intercalate ", " items})"

private def fcmpPredicateText : FcmpPredicate → String
  | .false => "false"
  | .oeq => "oeq"
  | .ogt => "ogt"
  | .oge => "oge"
  | .olt => "olt"
  | .ole => "ole"
  | .one => "one"
  | .ord => "ord"
  | .uno => "uno"
  | .ueq => "ueq"
  | .ugt => "ugt"
  | .uge => "uge"
  | .ult => "ult"
  | .ule => "ule"
  | .une => "une"
  | .true => "true"

private def instructionText : Instruction → String
  | .alloca result type => s!"  {resultText result} = alloca {typeText type}"
  | .store value slot => s!"  store {typedOperand value}, {typedOperand slot}"
  | .load result slot =>
    match operandType slot with
    | .pointer (some pointee) => s!"  {resultText result} = load {typeText pointee}, {typedOperand slot}"
    | _ => s!"  {resultText result} = load void, {typedOperand slot}"
  | .add result bits left right => s!"  {resultText result} = add i{bits} {operandText left}, {operandText right}"
  | .sub result bits left right => s!"  {resultText result} = sub i{bits} {operandText left}, {operandText right}"
  | .mul result bits left right => s!"  {resultText result} = mul i{bits} {operandText left}, {operandText right}"
  | .sdiv result bits left right => s!"  {resultText result} = sdiv i{bits} {operandText left}, {operandText right}"
  | .srem result bits left right => s!"  {resultText result} = srem i{bits} {operandText left}, {operandText right}"
  | .bitAnd result bits left right => s!"  {resultText result} = and i{bits} {operandText left}, {operandText right}"
  | .bitOr result bits left right => s!"  {resultText result} = or i{bits} {operandText left}, {operandText right}"
  | .bitXor result bits left right => s!"  {resultText result} = xor i{bits} {operandText left}, {operandText right}"
  | .shl result bits left right => s!"  {resultText result} = shl i{bits} {operandText left}, {operandText right}"
  | .lshr result bits left right => s!"  {resultText result} = lshr i{bits} {operandText left}, {operandText right}"
  | .ashr result bits left right => s!"  {resultText result} = ashr i{bits} {operandText left}, {operandText right}"
  | .icmpEq result bits left right => s!"  {resultText result} = icmp eq i{bits} {operandText left}, {operandText right}"
  | .icmpPtrEq result left right => s!"  {resultText result} = icmp eq ptr {operandText left}, {operandText right}"
  | .icmpSlt result bits left right => s!"  {resultText result} = icmp slt i{bits} {operandText left}, {operandText right}"
  | .icmpSle result bits left right => s!"  {resultText result} = icmp sle i{bits} {operandText left}, {operandText right}"
  | .icmpSgt result bits left right => s!"  {resultText result} = icmp sgt i{bits} {operandText left}, {operandText right}"
  | .icmpSge result bits left right => s!"  {resultText result} = icmp sge i{bits} {operandText left}, {operandText right}"
  | .fadd result left right => s!"  {resultText result} = fadd double {operandText left}, {operandText right}"
  | .fsub result left right => s!"  {resultText result} = fsub double {operandText left}, {operandText right}"
  | .fmul result left right => s!"  {resultText result} = fmul double {operandText left}, {operandText right}"
  | .fdiv result left right => s!"  {resultText result} = fdiv double {operandText left}, {operandText right}"
  | .fneg result source => s!"  {resultText result} = fneg double {operandText source}"
  | .fcmp result predicate left right => s!"  {resultText result} = fcmp {fcmpPredicateText predicate} double {operandText left}, {operandText right}"
  | .makeConstructor result tag payload =>
    let tagName := s!"%r{result.value}.tag"
    let payloadName := s!"%r{result.value}.payload"
    let shiftedName := s!"%r{result.value}.shifted"
    String.intercalate "\n" [s!"  {tagName} = zext i64 {operandText tag} to i128", s!"  {payloadName} = zext i64 {operandText payload} to i128", s!"  {shiftedName} = shl i128 {payloadName}, 64", s!"  {resultText result} = or i128 {tagName}, {shiftedName}"]
  | .extractTag result source => s!"  {resultText result} = trunc i128 {operandText source} to i64"
  | .extractPayload result source =>
    let shiftedName := s!"%r{result.value}.payload.shifted"
    String.intercalate "\n" [s!"  {shiftedName} = lshr i128 {operandText source}, 64", s!"  {resultText result} = trunc i128 {shiftedName} to i64"]
  | .call result callee arguments =>
    let callPrefix := match result with | none => "  " | some item => s!"  {resultText item} = "
    let values := arguments.map typedOperand
    let callType := match callable? (operandType callee) with
      | some signature => if signature.variadic then callableTypeText signature else typeText signature.result
      | none => "void"
    s!"{callPrefix}call {callType} {operandText callee}({String.intercalate ", " values})"
  | .phi result valueType incoming =>
    let values := incoming.map (fun item => s!"[ {operandText item.2}, %{item.1} ]")
    s!"  {resultText result} = phi {typeText valueType} {String.intercalate ", " values}"
  | .zext result source targetWidth => s!"  {resultText result} = zext {typeText (operandType source)} {operandText source} to i{targetWidth}"
  | .sext result source targetWidth => s!"  {resultText result} = sext {typeText (operandType source)} {operandText source} to i{targetWidth}"
  | .trunc result source targetWidth => s!"  {resultText result} = trunc {typeText (operandType source)} {operandText source} to i{targetWidth}"
  | .bitcast result source target => s!"  {resultText result} = bitcast {typeText (operandType source)} {operandText source} to {typeText target}"
  | .getElementPtr result pointer indices =>
    let indexText := indices.map (fun index => s!", {typedOperand index}")
    match operandType pointer with
    | .pointer (some basis) => s!"  {resultText result} = getelementptr {typeText basis}, {typedOperand pointer}{String.intercalate "" indexText}"
    | _ => s!"  {resultText result} = getelementptr void, {typedOperand pointer}{String.intercalate "" indexText}"

private def terminatorText : Terminator → String
  | .ret none => "  ret void"
  | .ret (some value) => s!"  ret {typeText (operandType value)} {operandText value}"
  | .branch target => s!"  br label %{target}"
  | .condBranch condition thenTarget elseTarget => s!"  br i1 {operandText condition}, label %{thenTarget}, label %{elseTarget}"
  | .switch condition defaultTarget cases =>
    let caseText := cases.map (fun item => s!"    {typeText (operandType item.1)} {operandText item.1}, label %{item.2}")
    s!"  switch {typeText (operandType condition)} {operandText condition}, label %{defaultTarget} [\n{String.intercalate "\n" caseText}\n  ]"
  | .mustTailCall result callee arguments =>
    let values := arguments.map typedOperand
    let callable := callable? (operandType callee)
    let resultType := match callable with | some signature => signature.result | none => .void
    let callType := match callable with
      | some signature => if signature.variadic then callableTypeText signature else typeText signature.result
      | none => "void"
    let callPrefix := match result with | none => "  " | some item => s!"  {resultText item} = "
    let callText := s!"{callPrefix}musttail call {callType} {operandText callee}({String.intercalate ", " values})"
    let returnText := match result with
      | none => "  ret void"
      | some item => s!"  ret {typeText resultType} {resultText item}"
    callText ++ "\n" ++ returnText
  | .unreachable => "  unreachable"

private def blockText (block : Block) : String :=
  let instructions := String.intercalate "\n" (block.instructions.map instructionText)
  let terminator := match block.terminator with | none => "" | some value => terminatorText value
  if instructions.isEmpty then s!"{block.label}:\n{terminator}" else s!"{block.label}:\n{instructions}\n{terminator}"

private def functionText : Function → String
  | .declaration signature => s!"declare {signatureText signature}"
  | .definition signature blocks =>
    let blockLines := String.intercalate "\n" (blocks.map blockText)
    "define " ++ signatureText signature ++ " {\n" ++ blockLines ++ "\n}"

protected def validate (module : Module) : Except Failure ValidModule :=
  let signatures := module.functions.map functionSignature
  let functionNames := signatures.map FunctionSignature.name
  let globalNames := module.globals.map GlobalString.name
  let duplicateFunctions := hasDuplicateString functionNames
  let duplicateGlobals := hasDuplicateString globalNames
  let duplicateSymbols := hasDuplicateString (functionNames ++ globalNames)
  let invalidGlobals := module.globals.any (fun global => !validIdentifier global.name)
  let invalidTriple := module.targetTriple.any (fun triple => !validTargetTriple triple)
  if duplicateFunctions then .error (.invalidModule "duplicate function name")
  else if duplicateGlobals then .error (.invalidModule "duplicate global string name")
  else if duplicateSymbols then .error (.invalidModule "duplicate global symbol name")
  else if invalidGlobals then .error (.invalidModule "global string name is empty")
  else if invalidTriple then .error (.invalidModule "target triple contains unsafe characters")
  else
    match firstInvalidFunction? signatures module.globals module.functions 0 with
    | some (functionIndex, message) => .error (.invalidModule s!"functionIndex={functionIndex};{message}")
    | none => .ok (.make module)

protected def encode (valid : ValidModule) : ByteArray :=
  let module := valid.module
  let header := match module.targetTriple with | none => "" | some triple => s!"target triple = \"{triple}\""
  let globals := String.intercalate "\n" (module.globals.map globalText)
  let functions := String.intercalate "\n\n" (module.functions.map functionText)
  let sections := [header, globals, functions].filter (· != "")
  (String.intercalate "\n\n" sections ++ "\n").toUTF8

private def processFailure (arguments : List String) : NecoLean.System.Failure → Failure
  | .processStart command _ => .toolUnavailable command
  | .nonZeroExit command exitCode stdout stderr => .toolRejected command arguments exitCode stdout stderr
  | .file _ _ => .toolUnavailable "filesystem"

private def detectPlatform : IO (Except Failure Platform) := do
  let arguments := ["-s"]
  match ← NecoLean.System.run { command := "uname", arguments } with
  | .error failure => return .error (processFailure arguments failure)
  | .ok output =>
    match String.fromUTF8? output.stdout with
    | none => return .error (.invalidUtf8 "uname stdout")
    | some name => return NecoLean.Llvm.platformFromName name

private def sdkPath (platform : Platform) : IO (Except Failure (Option String)) := do
  match platform with
  | .linux => return .ok none
  | .macOS =>
    let arguments := ["--show-sdk-path"]
    match ← NecoLean.System.run { command := "xcrun", arguments } with
    | .error failure => return .error (processFailure arguments failure)
    | .ok output =>
      match String.fromUTF8? output.stdout with
      | none => return .error (.invalidUtf8 "xcrun stdout")
      | some path => return .ok (some path.trimAscii.toString)

private def runtimeSourceKindText : RuntimeSourceKind → String
  | .header => "header"
  | .compilationUnit => "compilation-unit"

protected def runtimeSourceBundleIdentity (sources : List RuntimeSource) : String :=
  let entries := sources.map (fun source => s!"{runtimeSourceKindText source.kind}\u0000{source.logicalName}\u0000{source.digest}\n")
  NecoLean.Digest.toHex (NecoLean.Digest.sha256 (String.intercalate "" entries).toUTF8)

private def runtimeSourcePath (directory : System.FilePath) (source : RuntimeSource) : System.FilePath :=
  directory.toString ++ "/" ++ source.logicalName

private def createRuntimeSourceDirectory : IO (Except Failure System.FilePath) := do
  try
    let directory ← IO.FS.createTempDir
    return .ok directory
  catch error =>
    return .error (.runtimeSourceDirectoryCreation (IO.Error.toString error))

private def writeRuntimeSource (directory : System.FilePath) (source : RuntimeSource) : IO (Except Failure RuntimeSourceArtifact) := do
  let path := runtimeSourcePath directory source
  match ← NecoLean.System.writeBytes path source.bytes with
  | .ok () => return .ok { logicalName := source.logicalName, kind := source.kind, digest := source.digest, path }
  | .error (.file _ message) => return .error (.runtimeSourceWrite source.logicalName path message)
  | .error _ => return .error (.runtimeSourceWrite source.logicalName path "filesystem")

private def validateRuntimeSources (sources : List RuntimeSource) : Except Failure Unit :=
  match firstDuplicateString? (sources.map RuntimeSource.logicalName) with
  | some name => .error (.duplicateRuntimeSourceName name)
  | none =>
    match sources.find? (fun source => (invalidRuntimeSourceNameReason source.logicalName).isSome) with
    | some source => .error (.invalidRuntimeSourceName source.logicalName ((invalidRuntimeSourceNameReason source.logicalName).getD "invalid runtime source name"))
    | none => .ok ()

protected def validateRuntimeUnitOptimizations
    (sources : List RuntimeSource)
    (optimizations : List RuntimeUnitOptimization) : Except Failure Unit := do
  let mut seenIndices := []
  for optimization in optimizations do
    if seenIndices.contains optimization.runtimeSourceIndex then
      throw (.invalidRuntimeUnitOptimization optimization.runtimeSourceIndex optimization.logicalName
        optimization.inputDigest "runtime source index is repeated")
    seenIndices := optimization.runtimeSourceIndex :: seenIndices
    match sources[optimization.runtimeSourceIndex]? with
    | none =>
      throw (.invalidRuntimeUnitOptimization optimization.runtimeSourceIndex optimization.logicalName
        optimization.inputDigest "runtime source index is out of range")
    | some source =>
      if source.kind != .compilationUnit then
        throw (.invalidRuntimeUnitOptimization optimization.runtimeSourceIndex optimization.logicalName
          optimization.inputDigest "runtime source index does not name a compilation unit")
      else if optimization.logicalName != source.logicalName then
        throw (.invalidRuntimeUnitOptimization optimization.runtimeSourceIndex optimization.logicalName
          optimization.inputDigest "runtime source logical name does not match")
      else if optimization.inputDigest != source.digest then
        throw (.invalidRuntimeUnitOptimization optimization.runtimeSourceIndex optimization.logicalName
          optimization.inputDigest "runtime source digest does not match")

private def writeRuntimeSourcesAt (directory : System.FilePath) (sources : List RuntimeSource) : IO (Except Failure (List RuntimeSourceArtifact)) := do
  match validateRuntimeSources sources with
  | .error failure => return .error failure
  | .ok () =>
    let rec loop : List RuntimeSource → List RuntimeSourceArtifact → IO (Except Failure (List RuntimeSourceArtifact))
      | [], artifacts => return .ok artifacts.reverse
      | source :: rest, artifacts => do
        match ← writeRuntimeSource directory source with
        | .error failure => return .error failure
        | .ok artifact => loop rest (artifact :: artifacts)
    loop sources []

private def writeRuntimeSources (sources : List RuntimeSource) : IO (Except Failure (String × List RuntimeSourceArtifact)) := do
  match validateRuntimeSources sources with
  | .error failure => return .error failure
  | .ok () =>
    let bundleIdentity := NecoLean.Llvm.runtimeSourceBundleIdentity sources
    if sources.isEmpty then
      return .ok (bundleIdentity, [])
    else
      match ← createRuntimeSourceDirectory with
      | .error failure => return .error failure
      | .ok directory =>
        match ← writeRuntimeSourcesAt directory sources with
        | .error failure => return .error failure
        | .ok artifacts => return .ok (bundleIdentity, artifacts)

private def digestBytes (bytes : ByteArray) : String :=
  NecoLean.Digest.toHex (NecoLean.Digest.sha256 bytes)

private def readArtifactBytes (operation : String) (path : System.FilePath) : IO (Except Failure ByteArray) := do
  match ← NecoLean.System.readBytes path with
  | .ok bytes => return .ok bytes
  | .error (.file _ message) => return .error (.artifactFile operation path message)
  | .error _ => return .error (.artifactFile operation path "filesystem")

private partial def findExecutable (name : String) (entries : List String) : IO (Except Failure System.FilePath) := do
  match entries with
  | [] => return .error (.toolUnavailable name)
  | entry :: rest =>
    let directory := if entry.isEmpty then "." else entry
    let candidate : System.FilePath := directory ++ "/" ++ name
    if ← candidate.pathExists then
      try
        return .ok (← IO.FS.realPath candidate)
      catch _ =>
        findExecutable name rest
    else
      findExecutable name rest

private def resolveExecutable (name : String) : IO (Except Failure System.FilePath) := do
  match ← IO.getEnv "PATH" with
  | none => return .error (.toolUnavailable name)
  | some path => findExecutable name (path.splitOn ":")

private structure CompilationEnvironment where
  platform : Platform
  compilerIdentity : CompilerIdentity

private def compilerQuery (path : System.FilePath) (arguments : List String) : IO (Except Failure NecoLean.System.ProcessOutput) := do
  match ← NecoLean.System.run { command := path.toString, arguments } with
  | .ok output => return .ok output
  | .error failure => return .error (processFailure arguments failure)

private def resolveCompilationEnvironment : IO (Except Failure CompilationEnvironment) := do
  match ← detectPlatform with
  | .error failure => return .error failure
  | .ok platform =>
    match ← resolveExecutable "clang" with
    | .error failure => return .error failure
    | .ok executablePath =>
      match ← readArtifactBytes "read-compiler" executablePath with
      | .error failure => return .error failure
      | .ok executableBytes =>
        match ← compilerQuery executablePath ["--version"] with
        | .error failure => return .error failure
        | .ok versionOutput =>
          match ← compilerQuery executablePath ["-dumpmachine"] with
          | .error failure => return .error failure
          | .ok targetOutput =>
            match String.fromUTF8? targetOutput.stdout with
            | none => return .error (.invalidUtf8 "clang -dumpmachine stdout")
            | some targetText =>
              match ← sdkPath platform with
              | .error failure => return .error failure
              | .ok sdk =>
                let sdkIdentityResult : Except Failure (Option SdkIdentity) ← match sdk with
                  | none => pure (.ok none)
                  | some pathText => do
                    let path : System.FilePath := pathText
                    try
                      let realPath ← IO.FS.realPath path
                      let settingsPath : System.FilePath := realPath.toString ++ "/SDKSettings.json"
                      match ← readArtifactBytes "read-sdk-settings" settingsPath with
                      | .error failure => pure (.error failure)
                      | .ok bytes => pure (.ok (some { path := realPath, settingsDigest := digestBytes bytes }))
                    catch error =>
                      pure (.error (.artifactFile "resolve-sdk" path (IO.Error.toString error)))
                match sdkIdentityResult with
                | .error failure => return .error failure
                | .ok sdkIdentity =>
                  return .ok {
                    platform
                    compilerIdentity := {
                      executablePath
                      executableDigest := digestBytes executableBytes
                      versionBytes := versionOutput.stdout
                      versionDigest := digestBytes versionOutput.stdout
                      targetTriple := targetText.trimAscii.toString
                      sdkIdentity
                    }
                  }

private def ownershipMarkerName : String := ".neco-object-output-owner"

protected def observeObjectOutputRoot (ownership : ObjectOutputOwnership) : IO ObjectOutputRootObservation := do
  let root := ownership.directory
  try
    return { root, state := if ← root.pathExists then .observedPresent else .observedAbsent }
  catch error =>
    return { root, state := .observationFailed (.file root (IO.Error.toString error)) }

private def retainedObjectCleanup (ownership : ObjectOutputOwnership) (cleanup : Failure) :
    IO OwnedObjectCleanupResidual := do
  let rootObservation ← NecoLean.Llvm.observeObjectOutputRoot ownership
  return { cleanup, ownership, rootObservation }

private def acquireObjectOutput (directory : System.FilePath) (inputDigest : String) : IO ObjectOutputAcquireResult := do
  match directory.parent with
  | some parent =>
    try IO.FS.createDirAll parent
    catch error => return .failed (.artifactDirectoryAcquisition directory (IO.Error.toString error))
  | none => pure ()
  try
    IO.FS.createDir directory
  catch error =>
    if ← directory.pathExists then
      return .failed (.artifactDirectoryExists directory)
    else
      return .failed (.artifactDirectoryAcquisition directory (IO.Error.toString error))
  let pid ← IO.Process.getPID
  let nanos ← IO.monoNanosNow
  let token := digestBytes s!"{pid}:{nanos}:{directory}:{inputDigest}".toUTF8
  let ownership := ObjectOutputOwnership.make directory token
  let marker : System.FilePath := directory.toString ++ "/" ++ ownershipMarkerName
  match ← NecoLean.System.writeBytes marker token.toUTF8 with
  | .ok () => return .acquired ownership
  | .error failure =>
    let primary := match failure with
      | .file _ message => Failure.artifactFile "write-owner-marker" marker message
      | _ => Failure.artifactFile "write-owner-marker" marker "filesystem"
    try
      IO.FS.removeDirAll directory
      return .failed primary
    catch error =>
      let cleanup := Failure.artifactCleanup directory (IO.Error.toString error) none
      return .cleanupRetained primary (← retainedObjectCleanup ownership cleanup)

protected def releaseObjectOutputs (ownership : ObjectOutputOwnership) : IO ObjectCleanupResult := do
  match ownership with
  | .make directory token =>
    let marker : System.FilePath := directory.toString ++ "/" ++ ownershipMarkerName
    match ← NecoLean.System.readBytes marker with
    | .error (.file _ message) =>
      return .retained (← retainedObjectCleanup ownership (.artifactCleanup marker message none))
    | .error _ =>
      return .retained (← retainedObjectCleanup ownership (.artifactCleanup marker "filesystem" none))
    | .ok bytes =>
      if bytes != token.toUTF8 then
        return .retained (← retainedObjectCleanup ownership
          (.artifactCleanup marker "ownership marker mismatch" none))
      else
        try
          IO.FS.removeDirAll directory
          return .released
        catch error =>
          return .retained (← retainedObjectCleanup ownership
            (.artifactCleanup directory (IO.Error.toString error) none))

private def cleanupObjectFailure {α : Type} (ownership : ObjectOutputOwnership) (prior : Failure) :
    IO (Except ObjectCompileFailure α) := do
  match ← NecoLean.Llvm.releaseObjectOutputs ownership with
  | .released => return .error (.operation prior)
  | .retained residual => return .error (.cleanupRetained prior residual)

private structure ObjectArgumentPlan where
  actual : List String
  normalized : List String

private def objectArgumentPlan
    (platform : Platform)
    (sdkPath : Option String)
    (role : ObjectInputRole)
    (moduleOptimization : ObjectModuleOptimization)
    (runtimeUnitOptimizations : List RuntimeUnitOptimization)
    (inputPath outputPath : System.FilePath)
    (inputName outputName : String) : Except Failure ObjectArgumentPlan := do
  let sdk ← NecoLean.Llvm.sdkArguments platform sdkPath
  let optimizationArguments := match role with
    | .llvmModule => match moduleOptimization with | .none => [] | .o1 => ["-O1"]
    | .runtimeCompilationUnit runtimeSourceIndex logicalName =>
      match runtimeUnitOptimizations.find? (fun optimization =>
          optimization.runtimeSourceIndex == runtimeSourceIndex && optimization.logicalName == logicalName) with
      | some optimization => match optimization.optimization with | .o2 => ["-O2"]
      | none => []
  let prefixActual := match role with
    | .llvmModule => ["-c", inputPath.toString, "-Wno-override-module"]
    | .runtimeCompilationUnit _ _ => ["-c", inputPath.toString, "-I", (inputPath.parent.getD inputPath).toString]
  let prefixNormalized := match role with
    | .llvmModule => ["-c", "$INPUTS/" ++ inputName, "-Wno-override-module"]
    | .runtimeCompilationUnit _ _ => ["-c", "$INPUTS/" ++ inputName, "-I", "$INPUTS"]
  return {
    actual := prefixActual ++ optimizationArguments ++ sdk ++ ["-o", outputPath.toString]
    normalized := prefixNormalized ++ optimizationArguments ++ sdk ++ ["-o", "$ARTIFACT/objects/" ++ outputName]
  }

private def ordinalText (ordinal : Nat) : String :=
  if ordinal < 10 then s!"00{ordinal}" else if ordinal < 100 then s!"0{ordinal}" else s!"{ordinal}"

private def compileObject
    (environment : CompilationEnvironment)
    (inputsDirectory objectsDirectory : System.FilePath)
    (role : ObjectInputRole)
    (moduleOptimization : ObjectModuleOptimization)
    (ordinal : Nat)
    (runtimeUnitOptimizations : List RuntimeUnitOptimization)
    (includeDirectories : List System.FilePath)
    (inputName : String)
    (inputPath : System.FilePath)
    (inputDigest : String) : IO (Except Failure CompiledObjectArtifact) := do
  let outputName := s!"object-{ordinalText ordinal}-{inputDigest}.o"
  let outputPath : System.FilePath := objectsDirectory.toString ++ "/" ++ outputName
  let sdk := environment.compilerIdentity.sdkIdentity.map (fun identity => identity.path.toString)
  match objectArgumentPlan environment.platform sdk role moduleOptimization runtimeUnitOptimizations inputPath outputPath inputName outputName with
  | .error failure => return .error failure
  | .ok plan =>
    let includes := includeDirectories.flatMap (fun path => ["-I", path.toString])
    let plan := { plan with actual := includes ++ plan.actual, normalized := includes ++ plan.normalized }
    match ← NecoLean.System.run { command := environment.compilerIdentity.executablePath.toString, arguments := plan.actual } with
    | .error failure => return .error (processFailure plan.actual failure)
    | .ok _ =>
      match ← readArtifactBytes "read-object" outputPath with
      | .error failure => return .error failure
      | .ok bytes => return .ok (.make role inputDigest outputPath (digestBytes bytes) plan.actual plan.normalized)

private def createOwnedSubdirectory (path : System.FilePath) : IO (Except Failure Unit) := do
  try
    IO.FS.createDir path
    return .ok ()
  catch error =>
    return .error (.artifactFile "create-directory" path (IO.Error.toString error))

protected def compileObjects (request : ObjectCompileRequest) : IO (Except ObjectCompileFailure ObjectCompileOutput) := do
  match validateRuntimeSources request.runtimeSources with
  | .error failure => return .error (.operation failure)
  | .ok () =>
    match NecoLean.Llvm.validateRuntimeUnitOptimizations request.runtimeSources request.runtimeUnitOptimizations with
    | .error failure => return .error (.operation failure)
    | .ok () =>
      match ← resolveCompilationEnvironment with
      | .error failure => return .error (.operation failure)
      | .ok environment =>
        let moduleBytes := NecoLean.Llvm.encode request.module
        let moduleDigest := digestBytes moduleBytes
        let bundleIdentity := NecoLean.Llvm.runtimeSourceBundleIdentity request.runtimeSources
        let inputDigest := digestBytes s!"{moduleDigest}\n{bundleIdentity}".toUTF8
        match ← acquireObjectOutput request.outputDirectory inputDigest with
        | .failed failure => return .error (.operation failure)
        | .cleanupRetained primary residual => return .error (.cleanupRetained primary residual)
        | .acquired ownership =>
          let inputsDirectory : System.FilePath := request.outputDirectory.toString ++ "/inputs"
          let objectsDirectory : System.FilePath := request.outputDirectory.toString ++ "/objects"
          match ← createOwnedSubdirectory inputsDirectory with
          | .error failure => return ← cleanupObjectFailure ownership failure
          | .ok () =>
            match ← createOwnedSubdirectory objectsDirectory with
            | .error failure => return ← cleanupObjectFailure ownership failure
            | .ok () =>
              let modulePath : System.FilePath := inputsDirectory.toString ++ "/module.ll"
              match ← NecoLean.System.writeBytes modulePath moduleBytes with
              | .error (.file _ message) => return ← cleanupObjectFailure ownership (.artifactFile "write-module" modulePath message)
              | .error _ => return ← cleanupObjectFailure ownership (.artifactFile "write-module" modulePath "filesystem")
              | .ok () =>
                match ← writeRuntimeSourcesAt inputsDirectory request.runtimeSources with
                | .error failure => return ← cleanupObjectFailure ownership failure
                | .ok runtimeArtifacts =>
                  match ← compileObject environment inputsDirectory objectsDirectory .llvmModule request.moduleOptimization 0 request.runtimeUnitOptimizations request.includeDirectories "module.ll" modulePath moduleDigest with
                  | .error failure => return ← cleanupObjectFailure ownership failure
                  | .ok moduleObject =>
                    let rec loop (remaining : List RuntimeSourceArtifact) (index : Nat) (objects : List CompiledObjectArtifact) : IO (Except Failure (List CompiledObjectArtifact)) := do
                      match remaining with
                      | [] => return .ok objects.reverse
                      | artifact :: rest =>
                        if artifact.kind == .header then
                          loop rest (index + 1) objects
                        else
                          match ← compileObject environment inputsDirectory objectsDirectory (.runtimeCompilationUnit index artifact.logicalName) .none (index + 1) request.runtimeUnitOptimizations request.includeDirectories artifact.logicalName artifact.path artifact.digest with
                          | .error failure => return .error failure
                          | .ok object => loop rest (index + 1) (object :: objects)
                    match ← loop runtimeArtifacts 0 [] with
                    | .error failure => return ← cleanupObjectFailure ownership failure
                    | .ok runtimeObjects =>
                      return .ok (.make environment.compilerIdentity runtimeArtifacts bundleIdentity (moduleObject :: runtimeObjects) ownership)

private structure ResolvedLinkInput where
  path : System.FilePath
  digest : String

private def linkOwnershipMarkerName : String := ".neco-link-output-owner"

private def linkClosureReason : String :=
  "clang emitted crt, linker, loader, and system library inputs are not content-addressed"

private def uint64BigEndian (value : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).reverse.map (fun index =>
    Nat.toUInt8 ((value / (2 ^ (index * 8))) % 256))).toArray

private def identityField (bytes : ByteArray) : ByteArray :=
  uint64BigEndian bytes.size ++ bytes

private def identityList (entries : List ByteArray) : ByteArray :=
  uint64BigEndian entries.length ++ entries.foldl (fun bytes entry => bytes ++ identityField entry) ByteArray.empty

private def sdkIdentityEncoding : Option SdkIdentity → ByteArray
  | none => identityField (ByteArray.mk #[0])
  | some identity =>
      identityField (ByteArray.mk #[1]) ++ identityField identity.path.toString.toUTF8 ++
        identityField identity.settingsDigest.toUTF8

private def linkIdentityBytes
    (compilerIdentity : CompilerIdentity)
    (orderedObjectDigests normalizedArguments : List String)
    (executableDigest : String)
    (systemLinkClosureIdentity : SystemLinkClosureIdentity) : ByteArray :=
  let closureBytes := match systemLinkClosureIdentity with
    | .unresolved targetTriple sdkIdentity reason =>
      identityField "unresolved-system-link-closure".toUTF8 ++
        identityField targetTriple.toUTF8 ++ sdkIdentityEncoding sdkIdentity ++
        identityField reason.toUTF8
  identityField "NCLINK1".toUTF8 ++
    identityField compilerIdentity.executablePath.toString.toUTF8 ++
    identityField compilerIdentity.executableDigest.toUTF8 ++
    identityField compilerIdentity.versionBytes ++
    identityField compilerIdentity.versionDigest.toUTF8 ++
    identityField compilerIdentity.targetTriple.toUTF8 ++
    sdkIdentityEncoding compilerIdentity.sdkIdentity ++
    identityList (orderedObjectDigests.map String.toUTF8) ++
    identityList (normalizedArguments.map String.toUTF8) ++
    identityField executableDigest.toUTF8 ++
    closureBytes

protected def LinkOutputIdentity.recomputeDigest (identity : LinkOutputIdentity) : String :=
  digestBytes (linkIdentityBytes identity.compilerIdentity identity.orderedObjectDigests
    identity.normalizedArguments identity.executableDigest identity.systemLinkClosureIdentity)

private def existingLinkPaths (ownership : LinkStagingOwnership) : IO (List System.FilePath) := do
  let candidates := [ownership.directory, ownership.markerPath, ownership.stagedExecutablePath]
  let rec loop (remaining : List System.FilePath) (paths : List System.FilePath) : IO (List System.FilePath) := do
    match remaining with
    | [] => return paths.reverse
    | path :: rest =>
      if ← path.pathExists then loop rest (path :: paths) else loop rest paths
  loop candidates []

protected def releaseLinkStaging (ownership : LinkStagingOwnership) : IO LinkCleanupResult := do
  match ownership with
  | .make directory markerPath token _ =>
    match ← NecoLean.System.readBytes markerPath with
    | .error (.file _ message) =>
      return .retained (.artifactCleanup markerPath message none) ownership (← existingLinkPaths ownership)
    | .error _ =>
      return .retained (.artifactCleanup markerPath "filesystem" none) ownership (← existingLinkPaths ownership)
    | .ok bytes =>
      if bytes != token.toUTF8 then
        return .retained (.artifactCleanup markerPath "ownership marker mismatch" none) ownership (← existingLinkPaths ownership)
      else
        try
          IO.FS.removeDirAll directory
          return .released
        catch error =>
          return .retained (.artifactCleanup directory (IO.Error.toString error) none) ownership (← existingLinkPaths ownership)

protected def releaseLinkedOutput (output : OwnedLinkedOutput) : IO LinkCleanupResult :=
  NecoLean.Llvm.releaseLinkStaging output.ownership

private def cleanupLinkFailure (ownership : LinkStagingOwnership) (primary : Failure) : IO ObjectLinkResult := do
  match ← NecoLean.Llvm.releaseLinkStaging ownership with
  | .released => return .failed primary
  | .retained cleanup retained paths =>
    return .cleanupRetained { primary := some primary, cleanup, ownership := retained, remainingPaths := paths }

private def resolveLinkInputs (inputs : List ObjectLinkInput) : IO (Except Failure (List ResolvedLinkInput)) := do
  let rec loop (remaining : List ObjectLinkInput) (resolved : List ResolvedLinkInput) : IO (Except Failure (List ResolvedLinkInput)) := do
    match remaining with
    | [] => return .ok resolved.reverse
    | input :: rest =>
      let pathResult : Except Failure System.FilePath ← try
        pure (.ok (← IO.FS.realPath input.path))
      catch error =>
        pure (.error (.artifactFile "resolve-link-object" input.path (IO.Error.toString error)))
      match pathResult with
      | .error failure => return .error failure
      | .ok path =>
        match ← readArtifactBytes "read-link-object" path with
        | .error failure => return .error failure
        | .ok bytes =>
          let actual := digestBytes bytes
          if actual != input.digest then
            return .error (.objectDigestMismatch input.path input.digest actual)
          else
            loop rest ({ path, digest := actual } :: resolved)
  loop inputs []

private def resolveLinkOutputPath (path : System.FilePath) : IO (Except Failure (System.FilePath × System.FilePath × String)) := do
  match path.fileName with
  | none => return .error (.invalidLinkOutputPath path "output path has no file name")
  | some name =>
    if path.toString.toList.any (fun character => character == '\u0000') then
      return .error (.invalidLinkOutputPath path "output path contains nul")
    else
      let parent := path.parent.getD "."
      if !(← parent.isDir) then
        return .error (.invalidLinkOutputPath path "output parent is not a readable directory")
      else
        try
          let realParent ← IO.FS.realPath parent
          return .ok (realParent, realParent / name, name)
        catch error =>
          return .error (.invalidLinkOutputPath path (IO.Error.toString error))

private inductive LinkStagingAcquireResult where
  | acquired (ownership : LinkStagingOwnership)
  | failed (failure : Failure)
  | cleanupRetained (residual : OwnedLinkResidual)

private def acquireLinkStaging
    (parent : System.FilePath)
    (outputName inputIdentity : String) : IO LinkStagingAcquireResult := do
  let pid ← IO.Process.getPID
  let nanos ← IO.monoNanosNow
  let token := digestBytes s!"{pid}:{nanos}:{parent}:{outputName}:{inputIdentity}".toUTF8
  let tokenPrefix := (token.take 24).copy
  let directory : System.FilePath := parent / s!".{outputName}.neco-link-{tokenPrefix}"
  let markerPath : System.FilePath := directory / linkOwnershipMarkerName
  let stagedExecutablePath : System.FilePath := directory / "executable"
  let ownership := LinkStagingOwnership.make directory markerPath token stagedExecutablePath
  try
    IO.FS.createDir directory
  catch error =>
    if ← directory.pathExists then
      return .failed (.artifactDirectoryExists directory)
    else
      return .failed (.artifactDirectoryAcquisition directory (IO.Error.toString error))
  match ← NecoLean.System.writeBytes markerPath token.toUTF8 with
  | .ok () => return .acquired ownership
  | .error (.file _ message) =>
    let primary := Failure.artifactFile "write-link-owner-marker" markerPath message
    match ← NecoLean.Llvm.releaseLinkStaging ownership with
    | .released => return .failed primary
    | .retained cleanup retained paths =>
      return .cleanupRetained { primary := some primary, cleanup, ownership := retained, remainingPaths := paths }
  | .error _ =>
    let primary := Failure.artifactFile "write-link-owner-marker" markerPath "filesystem"
    match ← NecoLean.Llvm.releaseLinkStaging ownership with
    | .released => return .failed primary
    | .retained cleanup retained paths =>
      return .cleanupRetained { primary := some primary, cleanup, ownership := retained, remainingPaths := paths }

protected def linkObjects (request : ObjectLinkRequest) : IO ObjectLinkResult := do
  if request.orderedObjects.isEmpty then
    return .failed .emptyObjectLinkInput
  match ← resolveLinkOutputPath request.outputPath with
  | .error failure => return .failed failure
  | .ok (outputParent, outputPath, outputName) =>
    let inputs := request.orderedObjects ++ request.staticLibraries.map (fun library =>
      { path := library.path, digest := library.digest : ObjectLinkInput })
    match ← resolveLinkInputs inputs with
    | .error failure => return .failed failure
    | .ok inputs =>
      match ← resolveCompilationEnvironment with
      | .error failure => return .failed failure
      | .ok environment =>
        if environment.compilerIdentity != request.compilerIdentity then
          return .failed (.compilerIdentityMismatch request.compilerIdentity environment.compilerIdentity)
        let sdkPath := environment.compilerIdentity.sdkIdentity.map (fun identity => identity.path.toString)
        match NecoLean.Llvm.sdkArguments environment.platform sdkPath with
        | .error failure => return .failed failure
        | .ok sdk =>
          let objectDigests := inputs.map (fun input => input.digest)
          let inputIdentity := digestBytes (String.intercalate "\n" objectDigests).toUTF8
          match ← acquireLinkStaging outputParent outputName inputIdentity with
          | .failed failure => return .failed failure
          | .cleanupRetained residual => return .cleanupRetained residual
          | .acquired ownership =>
            let actualArguments :=
              ["-target", environment.compilerIdentity.targetTriple] ++ sdk ++
                inputs.map (fun input => input.path.toString) ++ systemLibraryArguments environment.platform ++ ["-o", ownership.stagedExecutablePath.toString]
            let normalizedArguments :=
              ["-target", environment.compilerIdentity.targetTriple] ++ sdk ++
                inputs.mapIdx (fun index input => s!"$OBJECTS/{index}/{input.digest}.o") ++ systemLibraryArguments environment.platform ++ ["-o", "$STAGING/executable"]
            match ← NecoLean.System.run {
                command := environment.compilerIdentity.executablePath.toString
                arguments := actualArguments } with
            | .error failure => return ← cleanupLinkFailure ownership (processFailure actualArguments failure)
            | .ok process =>
              match ← readArtifactBytes "read-linked-executable" ownership.stagedExecutablePath with
              | .error failure => return ← cleanupLinkFailure ownership failure
              | .ok bytes =>
                let executableDigest := digestBytes bytes
                let closure := SystemLinkClosureIdentity.unresolved
                  environment.compilerIdentity.targetTriple environment.compilerIdentity.sdkIdentity linkClosureReason
                let identityBytes := linkIdentityBytes environment.compilerIdentity objectDigests normalizedArguments
                  executableDigest closure
                let identity : LinkOutputIdentity := {
                  compilerIdentity := environment.compilerIdentity
                  orderedObjectDigests := objectDigests
                  normalizedArguments
                  executableDigest
                  systemLinkClosureIdentity := closure
                  identityDigest := digestBytes identityBytes
                }
                return .linked (.make identity outputPath actualArguments process ownership)

protected def publishLinkedOutput (output : OwnedLinkedOutput) : IO LinkPublicationResult := do
  let ownership := output.ownership
  match ownership with
  | .make _ markerPath token stagedExecutablePath =>
    match ← NecoLean.System.readBytes markerPath with
    | .error (.file _ message) =>
      return .notPublished (.linkPublication "read-owner-marker" markerPath message) output
    | .error _ =>
      return .notPublished (.linkPublication "read-owner-marker" markerPath "filesystem") output
    | .ok markerBytes =>
      if markerBytes != token.toUTF8 then
        return .notPublished (.linkPublication "verify-owner-marker" markerPath "ownership marker mismatch") output
      match ← readArtifactBytes "read-staged-executable" stagedExecutablePath with
      | .error failure => return .notPublished failure output
      | .ok stagedBytes =>
        let expectedDigest := output.identity.executableDigest
        let stagedDigest := digestBytes stagedBytes
        if stagedDigest != expectedDigest then
          return .notPublished (.objectDigestMismatch stagedExecutablePath expectedDigest stagedDigest) output
        try
          IO.FS.hardLink stagedExecutablePath output.requestedOutputPath
        catch error =>
          return .notPublished (.linkPublication "hard-link" output.requestedOutputPath (IO.Error.toString error)) output
        match ← readArtifactBytes "read-published-executable" output.requestedOutputPath with
        | .error failure =>
          return .finalCreatedUnverified failure output.requestedOutputPath expectedDigest output
        | .ok finalBytes =>
          let actualDigest := digestBytes finalBytes
          if actualDigest != expectedDigest then
            return .finalCreatedUnverified
              (.objectDigestMismatch output.requestedOutputPath expectedDigest actualDigest)
              output.requestedOutputPath expectedDigest output
          let published : PublishedLinkedOutput := {
            identity := output.identity
            outputPath := output.requestedOutputPath
            arguments := output.arguments
            process := output.process
          }
          match ← NecoLean.Llvm.releaseLinkStaging ownership with
          | .released => return .published published
          | .retained cleanup retained paths =>
            return .publishedWithResidual published {
              primary := none
              cleanup
              ownership := retained
              remainingPaths := paths
            }

protected def compile (request : CompileRequest) : IO (Except Failure CompileOutput) := do
  for library in request.staticLibraries do
    match ← readArtifactBytes "read-static-library" library.path with
    | .error failure => return .error failure
    | .ok bytes =>
      let actual := digestBytes bytes
      if actual != library.digest then
        return .error (.objectDigestMismatch library.path library.digest actual)
  let irPath : System.FilePath := request.outputPath.toString ++ ".ll"
  match ← NecoLean.System.writeBytes irPath (NecoLean.Llvm.encode request.module) with
  | .error _ => return .error (.toolUnavailable "filesystem")
  | .ok () =>
    match ← writeRuntimeSources request.runtimeSources with
    | .error failure => return .error failure
    | .ok (runtimeSourceBundleIdentity, runtimeArtifacts) =>
      match ← detectPlatform with
      | .error failure => return .error failure
      | .ok platform =>
        match ← sdkPath platform with
        | .error failure => return .error failure
        | .ok sdk =>
          let compilePaths := runtimeArtifacts.filterMap (fun artifact => if artifact.kind == .compilationUnit then some artifact.path else none)
          match NecoLean.Llvm.clangArguments platform irPath request.outputPath compilePaths sdk with
          | .error failure => return .error failure
          | .ok arguments =>
            let arguments := request.includeDirectories.flatMap (fun path => ["-I", path.toString]) ++
              arguments ++ request.staticLibraries.map (fun library => library.path.toString)
            match ← NecoLean.System.run { command := "clang", arguments } with
            | .ok process => return .ok { outputPath := request.outputPath, process, runtimeSources := runtimeArtifacts, runtimeSourceBundleIdentity }
            | .error failure => return .error (processFailure arguments failure)

end NecoLean.Llvm
