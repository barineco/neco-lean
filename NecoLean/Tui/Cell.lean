set_option autoImplicit false

namespace NecoLean.Tui

inductive CellContent where
  | content (symbol : String) (width : Nat)
  | continuation
  deriving Repr, BEq, DecidableEq

structure Cell where
  content : CellContent
  foreground : String := "default"
  background : String := "default"
  modifier : String := ""
  link : String := ""
  deriving Repr, BEq, DecidableEq

abbrev CellArray := Array Cell

def cellWidth (symbol : String) : Nat :=
  match symbol.toList with
  | [] => 0
  | character :: _ =>
    let code := character.toNat
    if (code >= 0x0300 && code <= 0x036f) ||
       (code >= 0x1ab0 && code <= 0x1aff) ||
       (code >= 0x1dc0 && code <= 0x1dff) ||
       (code >= 0xfe00 && code <= 0xfe0f) then 0
    else if (code >= 0x1100 && code <= 0x115f) ||
            (code >= 0x2e80 && code <= 0xa4cf) ||
            (code >= 0xac00 && code <= 0xd7a3) ||
            (code >= 0xf900 && code <= 0xfaff) ||
            (code >= 0xfe10 && code <= 0xfe6f) ||
            (code >= 0xff00 && code <= 0xff60) ||
            (code >= 0x1f300 && code <= 0x1faff) then 2
    else 1

def emptyCell : Cell :=
  { content := .content " " 1 }

def continuationCell : Cell :=
  { content := .continuation }

def isContinuation (cell : Cell) : Bool :=
  match cell.content with
  | .continuation => true
  | _ => false

def cellSymbol (cell : Cell) : String :=
  match cell.content with
  | .content symbol _ => symbol
  | .continuation => ""

def cellContentWidth (cell : Cell) : Nat :=
  match cell.content with
  | .content _ width => width
  | .continuation => 0

def contentCell (symbol : String) (foreground background modifier link : String) : Cell :=
  { content := .content symbol (cellWidth symbol)
    foreground := foreground
    background := background
    modifier := modifier
    link := link }

def cellsForString (text : String) : List Cell :=
  let rec loop (characters : List Char) : List Cell :=
    match characters with
    | [] => []
    | character :: rest =>
      let symbol := String.ofList [character]
      let width := cellWidth symbol
      let cell := { content := .content symbol width }
      if width >= 2 then cell :: continuationCell :: loop rest else cell :: loop rest
  loop text.toList

end NecoLean.Tui
