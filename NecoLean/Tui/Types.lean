set_option autoImplicit false

namespace NecoLean.Tui

abbrev UnitValue := Unit

structure UiNode where
  id : String
  label : String := ""
  children : List UiNode := []
  deriving Repr, BEq, Inhabited

inductive DetailPlacement where
  | right
  | bottom
  deriving Repr, BEq, DecidableEq

inductive KeyAction where
  | selectPrevious
  | selectNext
  | toggleExpansion
  | togglePlacement
  | growDetail
  | shrinkDetail
  | showHelp
  | closeOverlay
  | quit
  deriving Repr, BEq, DecidableEq

structure KeyBinding where
  keys : List String
  display : String
  description : String
  action : KeyAction
  deriving Repr, BEq, DecidableEq

structure TerminalSize where
  width : Int
  height : Int
  deriving Repr, BEq, DecidableEq

structure InputRemainder where
  text : String := ""
  deriving Repr, BEq, DecidableEq

structure RawChunk where
  text : String
  deriving Repr, BEq, DecidableEq

inductive InputEvent where
  | keyPress (key : String)
  | resize (size : TerminalSize)
  | tick
  | mousePress (x : Int) (y : Int)
  | mouseScroll (delta : Int)
  deriving Repr, BEq, DecidableEq

structure DecodedChunk where
  events : List InputEvent
  remainder : InputRemainder
  deriving Repr, BEq, DecidableEq

instance : Inhabited DecodedChunk := ⟨{ events := [], remainder := {} }⟩

inductive GeometryFailure where
  | invalidSize (width height : Int)
  | invalidSharedEdge
  | edgeDeltaOutOfRange
  | constraintResolutionFailure
  deriving Repr, BEq, DecidableEq

inductive SurfaceFailure where
  | invalidSurfaceArea
  | invalidWrapWidth
  | invalidPrefixWidth
  deriving Repr, BEq, DecidableEq

inductive TreeFailure where
  | duplicateTreeId (id : String)
  | missingTreeNode (id : String)
  | disconnectedTree (id : String)
  | invalidSelection (id : String)
  deriving Repr, BEq, DecidableEq

inductive OverlayFailure where
  | duplicateOverlayId (id : String)
  | missingOverlayId (id : String)
  | invalidOverlayRect (id : String)
  | invalidFocusTarget (id : String)
  deriving Repr, BEq, DecidableEq

inductive ViewportFailure where
  | invalidViewportSize (size : Int)
  | selectedUnavailable (id : String)
  | anchorUnavailable (id : String)
  | invalidTop (top : Int)
  deriving Repr, BEq, DecidableEq

inductive RenderFailure where
  | areaMismatch
  | cellIndexFailure
  | ansiEncodingFailure
  deriving Repr, BEq, DecidableEq

inductive TerminalFailure where
  | unsupported (reason : String)
  | init (reason : String)
  | size (reason : String)
  | input (reason : String)
  | render (reason : String)
  | interrupted
  deriving Repr, BEq, DecidableEq

inductive RuntimeFailure where
  | sampler (reason : String)
  | stopped
  deriving Repr, BEq, DecidableEq

inductive NoDecodeFailure where
  | none
  deriving Repr, BEq, DecidableEq

inductive TuiFailure where
  | geometry (failure : GeometryFailure)
  | surface (failure : SurfaceFailure)
  | tree (failure : TreeFailure)
  | overlay (failure : OverlayFailure)
  | viewport (failure : ViewportFailure)
  | render (failure : RenderFailure)
  | terminal (failure : TerminalFailure)
  | runtime (failure : RuntimeFailure)
  deriving BEq

abbrev RuntimeLoader α := IO (Except String α)

inductive RuntimeSample α where
  | latest (value : Except String α)
  | unavailable

end NecoLean.Tui
