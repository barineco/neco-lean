import NecoLean.Kdl

set_option autoImplicit false

namespace NecoLean.Kdl.Ast

inductive PathFailure where
  | emptySegment (index : Nat)
  | segmentContainsDot (segment : String)
  | segmentContainsHash (segment : String)
  deriving Repr, BEq, DecidableEq

structure NamespacePath where
  private segmentsValue : List String
  deriving Repr, BEq, DecidableEq

private def validateSegments (segments : List String) : Except PathFailure (List String) :=
  let rec loop (index : Nat) : List String → Except PathFailure (List String)
    | [] => .ok segments
    | segment :: rest =>
      if segment.isEmpty then .error (.emptySegment index)
      else if segment.contains '.' then .error (.segmentContainsDot segment)
      else if segment.contains '#' then .error (.segmentContainsHash segment)
      else loop (index + 1) rest
  loop 0 segments

def NamespacePath.empty : NamespacePath := ⟨[]⟩

def NamespacePath.fromSegments (segments : List String) : Except PathFailure NamespacePath := do
  let segments ← validateSegments segments
  .ok ⟨segments⟩

def NamespacePath.parse (value : String) : Except PathFailure NamespacePath :=
  if value.isEmpty then .ok .empty
  else NamespacePath.fromSegments (value.splitOn ".")

def NamespacePath.segments (path : NamespacePath) : List String := path.segmentsValue

def NamespacePath.isEmpty (path : NamespacePath) : Bool := path.segmentsValue.isEmpty

def NamespacePath.length (path : NamespacePath) : Nat := path.segmentsValue.length

def NamespacePath.first? (path : NamespacePath) : Option String := path.segmentsValue.head?

def NamespacePath.last? (path : NamespacePath) : Option String := path.segmentsValue.reverse.head?

def NamespacePath.parent? (path : NamespacePath) : Option NamespacePath :=
  match path.segmentsValue.reverse with
  | [] => none
  | _ :: rest => some ⟨rest.reverse⟩

def NamespacePath.child (path : NamespacePath) (segment : String) : Except PathFailure NamespacePath :=
  NamespacePath.fromSegments (path.segmentsValue ++ [segment])

def NamespacePath.startsWith (path prefixPath : NamespacePath) : Bool :=
  let rec loop : List String → List String → Bool
    | _, [] => true
    | [], _ :: _ => false
    | value :: values, expected :: expectedValues =>
      value == expected && loop values expectedValues
  loop path.segmentsValue prefixPath.segmentsValue

def NamespacePath.display (path : NamespacePath) : String := String.intercalate "." path.segmentsValue

def NamespacePath.toFsPath (path : NamespacePath) (extension : String := "") : String :=
  match path.segmentsValue.reverse with
  | [] => ""
  | leaf :: parents =>
    let extension := if extension.startsWith "." then extension.drop 1 else extension
    let file := if extension.isEmpty then leaf else leaf ++ "." ++ extension
    String.intercalate "/" (parents.reverse ++ [file])

inductive CrossReferenceFailure where
  | multipleHashes
  | emptyFragment
  | dotInFragment
  | invalidPath (failure : PathFailure)
  deriving Repr, BEq, DecidableEq

structure CrossReference where
  path : NamespacePath
  fragment : Option String
  deriving Repr, BEq, DecidableEq

private def validateFragment (fragment : String) : Except CrossReferenceFailure String :=
  if fragment.isEmpty then .error .emptyFragment
  else if fragment.contains '.' then .error .dotInFragment
  else .ok fragment

private def parseReferencePath (value : String) : Except CrossReferenceFailure NamespacePath :=
  match NamespacePath.parse value with
  | .ok path => .ok path
  | .error failure => .error (.invalidPath failure)

def CrossReference.parse (value : String) : Except CrossReferenceFailure CrossReference :=
  match value.splitOn "#" with
  | [path] => do
    let path ← parseReferencePath path
    .ok { path := path, fragment := none }
  | [path, fragment] => do
    let fragment ← validateFragment fragment
    let path ← parseReferencePath path
    .ok { path := path, fragment := some fragment }
  | _ => .error .multipleHashes

def CrossReference.fromPath (path : NamespacePath) : CrossReference :=
  { path := path, fragment := none }

def CrossReference.fromPathAndFragment (path : NamespacePath)
    (fragment : String) : Except CrossReferenceFailure CrossReference := do
  let fragment ← validateFragment fragment
  .ok { path := path, fragment := some fragment }

def CrossReference.hasFragment (reference : CrossReference) : Bool := reference.fragment.isSome

def CrossReference.isLocal (reference : CrossReference) : Bool :=
  reference.path.isEmpty && reference.fragment.isSome

def CrossReference.display (reference : CrossReference) : String :=
  match reference.fragment with
  | none => reference.path.display
  | some fragment => reference.path.display ++ "#" ++ fragment

structure StructuredName where
  kind : Option NamespacePath
  identifier : NamespacePath
  deriving Repr, BEq, DecidableEq

inductive StructuredFailure where
  | invalidNodeName (failure : PathFailure)
  | invalidIdentifier (failure : PathFailure)
  | invalidCrossReference (failure : CrossReferenceFailure)
  deriving Repr, BEq, DecidableEq

private def firstStringArgument? (node : Node) : Option String :=
  (nodeEntries node).findSome? fun
    | .argument argument => argument.value.asString?
    | .property _ => none

def nodeNameAsPath (node : Node) : Except StructuredFailure NamespacePath :=
  match NamespacePath.parse (nodeName node) with
  | .ok path => .ok path
  | .error failure => .error (.invalidNodeName failure)

def firstArgumentAsPath? (node : Node) : Except StructuredFailure (Option NamespacePath) :=
  match firstStringArgument? node with
  | none => .ok none
  | some value =>
    match NamespacePath.parse value with
    | .ok path => .ok (some path)
    | .error failure => .error (.invalidIdentifier failure)

def structuredNameFormX (node : Node) : Except StructuredFailure StructuredName := do
  let kind ← nodeNameAsPath node
  let identifier ← firstArgumentAsPath? node
  .ok { kind := some kind, identifier := identifier.getD .empty }

def structuredNameFormY (node : Node) : Except StructuredFailure StructuredName := do
  let identifier ← nodeNameAsPath node
  .ok { kind := none, identifier := identifier }

def structuredName (node : Node) : Except StructuredFailure StructuredName := do
  match ← firstArgumentAsPath? node with
  | some identifier =>
    let kind ← nodeNameAsPath node
    .ok { kind := some kind, identifier := identifier }
  | none => structuredNameFormY node

def structuredChildren (node : Node) : List Node :=
  match nodeChildren node with
  | none => []
  | some document => documentNodes document

def findChildKind (node : Node) (kind : NamespacePath) : List Node :=
  (structuredChildren node).filter fun child =>
    match nodeNameAsPath child with
    | .ok actual => actual == kind
    | .error _ => false

def crossReferenceArgument? (node : Node) : Except StructuredFailure (Option CrossReference) :=
  match firstStringArgument? node with
  | none => .ok none
  | some value =>
    match CrossReference.parse value with
    | .ok reference => .ok (some reference)
    | .error failure => .error (.invalidCrossReference failure)

def crossReferenceArguments (node : Node) : Except StructuredFailure (List CrossReference) := do
  let values := (nodeEntries node).filterMap fun
    | .argument argument => argument.value.asString?
    | .property _ => none
  values.mapM fun value =>
    match CrossReference.parse value with
    | .ok reference => .ok reference
    | .error failure => .error (.invalidCrossReference failure)

def crossReferenceProperty? (node : Node) (key : String) : Except StructuredFailure (Option CrossReference) :=
  match propertyValue? node key >>= Value.asString? with
  | none => .ok none
  | some value =>
    match CrossReference.parse value with
    | .ok reference => .ok (some reference)
    | .error failure => .error (.invalidCrossReference failure)

def attributeString? (node : Node) (key : String) : Option String :=
  match propertyValue? node key >>= Value.asString? with
  | some value => some value
  | none => findChild? node key >>= firstArgument? >>= Value.asString?

def attributeBool? (node : Node) (key : String) : Option Bool :=
  match propertyValue? node key >>= Value.asBool? with
  | some value => some value
  | none => findChild? node key >>= firstArgument? >>= Value.asBool?

def attributeInt? (node : Node) (key : String) : Option Int :=
  match propertyValue? node key >>= Value.asInt? with
  | some value => some value
  | none => findChild? node key >>= firstArgument? >>= Value.asInt?

private def countLeadingDots : List Char → Nat
  | '.' :: rest => countLeadingDots rest + 1
  | _ => 0

def dotChainDepth (node : Node) : Nat := countLeadingDots (nodeName node).toList

def dotChainKind (node : Node) : String := (nodeName node).drop (dotChainDepth node) |>.toString

partial def findByIdentifier? (document : Document) (identifier : NamespacePath) : Option Node :=
  (documentNodes document).findSome? fun node =>
    match structuredName node with
    | .ok name => if name.identifier == identifier then some node else
        nodeChildren node >>= fun children => findByIdentifier? children identifier
    | .error _ => nodeChildren node >>= fun children => findByIdentifier? children identifier

partial def resolve? (document : Document) (reference : CrossReference) : Option Node :=
  match reference.isLocal, reference.fragment with
  | true, some fragment =>
    match NamespacePath.parse fragment with
    | .ok identifier => findByIdentifier? document identifier
    | .error _ => none
  | false, none => findByIdentifier? document reference.path
  | false, some fragment =>
    findByIdentifier? document reference.path >>= fun entity =>
      let rec findFragment (node : Node) : Option Node :=
        (structuredChildren node).findSome? fun child =>
          match structuredName child with
          | .ok name => if name.identifier.display == fragment || nodeName child == fragment then some child
            else findFragment child
          | .error _ => if nodeName child == fragment then some child else findFragment child
      findFragment entity
  | _, _ => none

inductive Marker where
  | kind (name : String)
  | prefix (value : Char)
  deriving Repr, BEq, DecidableEq

inductive AxisForm where
  | off
  | expand
  | collapse
  | expandWithMarker (marker : Marker)
  | collapseWithMarker (marker : Marker)
  deriving Repr, BEq, DecidableEq

inductive PropertyChildForm where
  | off
  | expand
  | collapse
  deriving Repr, BEq, DecidableEq

structure Convention where
  markers : List Marker := []
  namespaceForm : AxisForm := .off
  procedureForm : AxisForm := .off
  propertyChildForm : PropertyChildForm := .off
  typeAnnotationForm : AxisForm := .off
  kindKeywordForm : AxisForm := .off
  deriving Repr, BEq, DecidableEq

def Convention.default : Convention := {}

def Convention.withMarker (convention : Convention) (marker : Marker) : Convention :=
  { convention with markers := convention.markers ++ [marker] }

def Convention.withNamespaceForm (convention : Convention) (form : AxisForm) : Convention :=
  { convention with namespaceForm := form }

def Convention.withProcedureForm (convention : Convention) (form : AxisForm) : Convention :=
  { convention with procedureForm := form }

def Convention.withPropertyChildForm (convention : Convention)
    (form : PropertyChildForm) : Convention :=
  { convention with propertyChildForm := form }

def Convention.withTypeAnnotationForm (convention : Convention) (form : AxisForm) : Convention :=
  { convention with typeAnnotationForm := form }

def Convention.withKindKeywordForm (convention : Convention) (form : AxisForm) : Convention :=
  { convention with kindKeywordForm := form }

private def markerMatches (marker : Marker) (name : String) : Bool :=
  match marker with
  | .kind kind => name == kind
  | .prefix prefixValue => name.startsWith (String.singleton prefixValue)

def Convention.isMarkerKind (convention : Convention) (name : String) : Bool :=
  convention.markers.any fun marker => markerMatches marker name

private def markerName (marker : Marker) (payload : String) : String :=
  match marker with
  | .kind kind => kind
  | .prefix prefixValue => String.singleton prefixValue ++ payload

private def markerPayload? (marker : Marker) (node : Node) : Option String :=
  match marker with
  | .kind _ => firstStringArgument? node
  | .prefix _ => some ((nodeName node).drop 1 |>.toString)

inductive TransformFailure where
  | invalidNamespace (name : String) (failure : PathFailure)
  | depthJump (fromDepth : Nat) (toDepth : Nat)
  | mixedChildKind (parent : String) (child : String)
  | childHasMultipleEntries (name : String)
  | malformedMarker (name : String)
  deriving Repr, BEq, DecidableEq

structure TransformResult where
  document : Document
  changed : Bool
  deriving Repr, BEq

private def replaceNode (node : Node) (name : String := nodeName node)
    (entries : List Entry := nodeEntries node) (children : Option Document := nodeChildren node)
    (typeAnnotation : Option String := nodeTypeAnnotation node) : Node :=
  .make typeAnnotation name entries children

private partial def transformNodes (nodes : List Node) (convention : Convention)
    (parentIsMarker : Bool) (transform : Node → Bool → Except TransformFailure (List Node × Bool)) :
    Except TransformFailure (List Node × Bool) := do
  let rec loop (remaining : List Node) (output : List Node) (changed : Bool) := do
    match remaining with
    | [] => .ok (output, changed)
    | node :: rest =>
      let childrenResult ← match nodeChildren node with
        | none => .ok (none, false)
        | some children => do
          let (children, childChanged) ← transformNodes (documentNodes children) convention
            (convention.isMarkerKind (nodeName node)) transform
          .ok (some (.make children), childChanged)
      let node := replaceNode node (children := childrenResult.1)
      let (replacement, nodeChanged) ← transform node parentIsMarker
      loop rest (output ++ replacement) (changed || childrenResult.2 || nodeChanged)
  loop nodes [] false

private def nestOne (node : Node) (skip : Bool) : Except TransformFailure (List Node × Bool) :=
  let name := nodeName node
  if skip || name.startsWith "." || !(name.contains '.') then .ok ([node], false)
  else
    match NamespacePath.parse name with
    | .error failure => .error (.invalidNamespace name failure)
    | .ok path =>
      match path.segments.reverse with
      | [] | [_] => .ok ([node], false)
      | leaf :: parents =>
        let leafNode := replaceNode node (name := leaf)
        let nested := parents.foldl (fun child segment =>
          (.make none segment [] (some (.make [child])) : Node)) leafNode
        .ok ([nested], true)

def nestNamespaces (document : Document) (convention : Convention := .default) :
    Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false nestOne
  .ok { document := .make nodes, changed := changed }

private partial def flattenPureChain (node : Node) (changed : Bool) : Node × Bool :=
  match nodeTypeAnnotation node, nodeEntries node, nodeChildren node with
  | none, [], some children =>
    match documentNodes children with
    | [child] =>
      let combined := replaceNode child (name := nodeName node ++ "." ++ nodeName child)
      flattenPureChain combined true
    | _ => (node, changed)
  | _, _, _ => (node, changed)

private def flattenOne (node : Node) (skip : Bool) : Except TransformFailure (List Node × Bool) :=
  if skip then .ok ([node], false) else
  let result := flattenPureChain node false
  .ok ([result.1], result.2)

def flattenNamespaces (document : Document) (convention : Convention := .default) :
    Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false flattenOne
  .ok { document := .make nodes, changed := changed }

private def appendNested (nodes : List Node) (depth : Nat) (node : Node) :
    Except TransformFailure (List Node) :=
  match depth with
  | 0 => .ok (nodes ++ [node])
  | depth + 1 =>
    match nodes.reverse with
    | [] => .error (.depthJump 0 (depth + 1))
    | parent :: previous => do
      let children := (nodeChildren parent).map documentNodes |>.getD []
      let children ← appendNested children depth node
      let parent := replaceNode parent (children := some (.make children))
      .ok (previous.reverse ++ [parent])

private partial def expandDotChainsInNodes (nodes : List Node) (kind : String)
    (convention : Convention) : Except TransformFailure (List Node × Bool) := do
  let rec mapChildren (remaining : List Node) (out : List Node) (changed : Bool) := do
    match remaining with
    | [] => .ok (out, changed)
    | node :: rest =>
      if convention.isMarkerKind (nodeName node) then
        mapChildren rest (out ++ [node]) changed
      else
        let childResult ← match nodeChildren node with
          | none => .ok (node, false)
          | some children => do
            let (children, childChanged) ← expandDotChainsInNodes (documentNodes children) kind convention
            .ok (replaceNode node (children := some (.make children)), childChanged)
        mapChildren rest (out ++ [childResult.1]) (changed || childResult.2)
  let (nodes, childChanged) ← mapChildren nodes [] false
  let rec loop (remaining : List Node) (out : List Node) (activeDepth : Option Nat)
      (changed : Bool) := do
    match remaining with
    | [] => .ok (out, changed || childChanged)
    | node :: rest =>
      let depth := dotChainDepth node
      let nodeKind := dotChainKind node
      if nodeKind != kind then loop rest (out ++ [node]) none changed
      else if depth == 0 then
        loop rest (out ++ [replaceNode node (name := nodeKind)]) (some 0) changed
      else
        match activeDepth with
        | none => .error (.depthJump 0 depth)
        | some previousDepth =>
          if depth > previousDepth + 1 then .error (.depthJump previousDepth depth)
          else do
            let out ← appendNested out depth (replaceNode node (name := nodeKind))
            loop rest out (some depth) true
  loop nodes [] none false

def expandDotChain (document : Document) (kind : String)
    (convention : Convention := .default) : Except TransformFailure TransformResult := do
  let (nodes, changed) ← expandDotChainsInNodes (documentNodes document) kind convention
  .ok { document := .make nodes, changed := changed }

private partial def collectChain (node : Node) (kind : String) (depth : Nat) :
    Except TransformFailure (List Node) := do
  let children := (nodeChildren node).map documentNodes |>.getD []
  for child in children do
    if nodeName child != kind then .error (.mixedChildKind (nodeName node) (nodeName child))
  let name := String.join (List.replicate depth ".") ++ nodeName node
  let root := replaceNode node (name := name) (children := none)
  let descendants ← children.mapM fun child => collectChain child kind (depth + 1)
  .ok (root :: descendants.flatten)

private partial def collapseDotChainsInNodes (nodes : List Node) (kind : String)
    (convention : Convention) : Except TransformFailure (List Node × Bool) := do
  let rec loop (remaining : List Node) (out : List Node) (changed : Bool) := do
    match remaining with
    | [] => .ok (out, changed)
    | node :: rest =>
      if nodeName node == kind then
        let chain ← collectChain node kind 0
        loop rest (out ++ chain) (changed || (nodeChildren node).isSome)
      else if convention.isMarkerKind (nodeName node) then
        loop rest (out ++ [node]) changed
      else
        match nodeChildren node with
        | none => loop rest (out ++ [node]) changed
        | some children =>
          let (children, childChanged) ← collapseDotChainsInNodes (documentNodes children) kind convention
          let node := replaceNode node (children := if children.isEmpty then none else some (.make children))
          loop rest (out ++ [node]) (changed || childChanged)
  loop nodes [] false

def collapseDotChain (document : Document) (kind : String)
    (convention : Convention := .default) : Except TransformFailure TransformResult := do
  let (nodes, changed) ← collapseDotChainsInNodes (documentNodes document) kind convention
  .ok { document := .make nodes, changed := changed }

private def expandPropertiesOne (node : Node) (skip : Bool) : Except TransformFailure (List Node × Bool) :=
  if skip then .ok ([node], false) else
  let (entries, propertyChildren) := (nodeEntries node).foldl (fun (entries, children) entry =>
    match entry with
    | .argument _ => (entries ++ [entry], children)
    | .property property =>
      let child : Node := .make none property.name
        [.argument { typeAnnotation := property.typeAnnotation, value := property.value }] none
      (entries, children ++ [child])) ([], [])
  let children := (nodeChildren node).map documentNodes |>.getD []
  .ok ([replaceNode node (entries := entries)
    (children := if children.isEmpty && propertyChildren.isEmpty then none
      else some (.make (children ++ propertyChildren)))], !propertyChildren.isEmpty)

def expandProperties (document : Document) (convention : Convention := .default) :
    Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false expandPropertiesOne
  .ok { document := .make nodes, changed := changed }

private def collapsePropertiesOne (node : Node) (skip : Bool) : Except TransformFailure (List Node × Bool) := do
  if skip then .ok ([node], false) else
  let rec classify (children : List Node) (entries : List Entry) (remaining : List Node)
      (changed : Bool) := do
    match children with
    | [] => .ok (entries, remaining, changed)
    | child :: rest =>
      match nodeTypeAnnotation child, nodeChildren child, nodeEntries child with
      | none, none, [.argument argument] =>
        let property : Entry := .property {
          typeAnnotation := argument.typeAnnotation, name := nodeName child, value := argument.value }
        classify rest (entries ++ [property]) remaining true
      | _, _, childEntries =>
        if childEntries.length > 1 then .error (.childHasMultipleEntries (nodeName child))
        else classify rest entries (remaining ++ [child]) changed
  let children := (nodeChildren node).map documentNodes |>.getD []
  let (entries, remaining, changed) ← classify children (nodeEntries node) [] false
  .ok ([replaceNode node (entries := entries)
    (children := if remaining.isEmpty then none else some (.make remaining))], changed)

def collapseProperties (document : Document) (convention : Convention := .default) :
    Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false collapsePropertiesOne
  .ok { document := .make nodes, changed := changed }

private def markerWrapper (marker : Marker) (payload : String) (child : Node) : Node :=
  match marker with
  | .kind kind => .make none kind
      [.argument { typeAnnotation := none, value := .string payload }] (some (.make [child]))
  | .prefix prefixValue => .make none (String.singleton prefixValue ++ payload) [] (some (.make [child]))

private def unwrapMarker (marker : Marker) (node : Node) : Except TransformFailure (Option (String × Node)) :=
  if !markerMatches marker (nodeName node) then .ok none
  else
    match markerPayload? marker node, nodeChildren node with
    | some payload, some children =>
      match documentNodes children with
      | [child] => .ok (some (payload, child))
      | _ => .error (.malformedMarker (nodeName node))
    | _, _ => .error (.malformedMarker (nodeName node))

private def expandTypeOne (marker : Marker) (node : Node) (skip : Bool) :
    Except TransformFailure (List Node × Bool) :=
  if skip then .ok ([node], false) else
  match nodeTypeAnnotation node with
  | none => .ok ([node], false)
  | some annotation =>
    .ok ([markerWrapper marker annotation (replaceNode node (typeAnnotation := none))], true)

private def collapseTypeOne (marker : Marker) (node : Node) (skip : Bool) :
    Except TransformFailure (List Node × Bool) := do
  if skip then .ok ([node], false) else
  match ← unwrapMarker marker node with
  | none => .ok ([node], false)
  | some (annotation, child) => .ok ([replaceNode child (typeAnnotation := some annotation)], true)

def expandTypeAnnotations (document : Document) (marker : Marker)
    (convention : Convention := .default) : Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false (expandTypeOne marker)
  .ok { document := .make nodes, changed := changed }

def collapseTypeAnnotations (document : Document) (marker : Marker)
    (convention : Convention := .default) : Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false (collapseTypeOne marker)
  .ok { document := .make nodes, changed := changed }

private def takeFirstUntypedString (entries : List Entry) : Option (String × List Entry) :=
  let rec loop (remaining output : List Entry) :=
    match remaining with
    | [] => none
    | .argument argument :: rest =>
      match argument.typeAnnotation, argument.value with
      | none, .string value => some (value, output ++ rest)
      | _, _ => loop rest (output ++ [.argument argument])
    | .property property :: rest => loop rest (output ++ [.property property])
  loop entries []

private def expandKindOne (marker : Marker) (node : Node) (skip : Bool) :
    Except TransformFailure (List Node × Bool) :=
  if skip then .ok ([node], false) else
  match takeFirstUntypedString (nodeEntries node) with
  | none => .ok ([node], false)
  | some (identifier, entries) =>
    let markerNode : Node := .make none (markerName marker identifier) [] (nodeChildren node)
    .ok ([replaceNode node (entries := entries) (children := some (.make [markerNode]))], true)

private def collapseKindOne (marker : Marker) (node : Node) (skip : Bool) :
    Except TransformFailure (List Node × Bool) := do
  if skip then .ok ([node], false) else
  match nodeChildren node with
  | some children =>
    match documentNodes children with
    | [markerNode] =>
      if markerMatches marker (nodeName markerNode) then
        match markerPayload? marker markerNode with
        | none => .error (.malformedMarker (nodeName markerNode))
        | some identifier =>
          let entry : Entry := .argument { typeAnnotation := none, value := .string identifier }
          .ok ([replaceNode node (entries := entry :: nodeEntries node)
            (children := nodeChildren markerNode)], true)
      else .ok ([node], false)
    | _ => .ok ([node], false)
  | none => .ok ([node], false)

def expandKindKeywords (document : Document) (marker : Marker)
    (convention : Convention := .default) : Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false (expandKindOne marker)
  .ok { document := .make nodes, changed := changed }

def collapseKindKeywords (document : Document) (marker : Marker)
    (convention : Convention := .default) : Except TransformFailure TransformResult := do
  let (nodes, changed) ← transformNodes (documentNodes document) convention false (collapseKindOne marker)
  .ok { document := .make nodes, changed := changed }

private def kindMarkers (convention : Convention) : List String :=
  convention.markers.filterMap fun
  | .kind name => some name
  | .prefix _ => none

def renderAs (document : Document) (convention : Convention) : Except TransformFailure Document := do
  let document ← match convention.kindKeywordForm with
    | .expandWithMarker marker => do
      let result ← expandKindKeywords document marker convention
      .ok result.document
    | .collapseWithMarker marker => do
      let result ← collapseKindKeywords document marker convention
      .ok result.document
    | _ => .ok document
  let document ← match convention.typeAnnotationForm with
    | .expandWithMarker marker => do
      let result ← expandTypeAnnotations document marker convention
      .ok result.document
    | .collapseWithMarker marker => do
      let result ← collapseTypeAnnotations document marker convention
      .ok result.document
    | _ => .ok document
  let document ← match convention.namespaceForm with
    | .expand => do
      let result ← nestNamespaces document convention
      .ok result.document
    | .collapse => do
      let result ← flattenNamespaces document convention
      .ok result.document
    | _ => .ok document
  let document ← match convention.procedureForm with
    | .expand => kindMarkers convention |>.foldlM (fun document kind => do
        let result ← expandDotChain document kind convention
        .ok result.document) document
    | .collapse => kindMarkers convention |>.foldlM (fun document kind => do
        let result ← collapseDotChain document kind convention
        .ok result.document) document
    | _ => .ok document
  match convention.propertyChildForm with
  | .expand => do
    let result ← expandProperties document convention
    .ok result.document
  | .collapse => do
    let result ← collapseProperties document convention
    .ok result.document
  | .off => .ok document

end NecoLean.Kdl.Ast
