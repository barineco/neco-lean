import NecoLean.Tui.Types

set_option autoImplicit false

namespace NecoLean.Tui

def normalizeKey (key : String) : String :=
  match key with
  | "\r" | "\n" => "enter"
  | "\t" => "tab"
  | "\u007f" => "backspace"
  | "\u0003" => "ctrl-c"
  | value => value

def parseMouse (sequence : String) : Option InputEvent :=
  if sequence.startsWith "\u001b[<" && (sequence.endsWith "M" || sequence.endsWith "m") then
    let body := ((sequence.drop 3).dropEnd 1).toString
    match body.splitOn ";" with
    | [button, x, y] =>
      match button.toInt?, x.toInt?, y.toInt? with
      | some button, some x, some y =>
        if button == 64 then some (.mouseScroll (-1))
        else if button == 65 then some (.mouseScroll 1)
        else some (.mousePress (x - 1) (y - 1))
      | _, _, _ => none
    | _ => none
  else none

private def escapeEvent? (input : String) : Option (InputEvent × Nat) :=
  if input.startsWith "\u001b[A" then some (.keyPress "up", 3)
  else if input.startsWith "\u001b[B" then some (.keyPress "down", 3)
  else if input.startsWith "\u001b[C" then some (.keyPress "right", 3)
  else if input.startsWith "\u001b[D" then some (.keyPress "left", 3)
  else if input.startsWith "\u001b[H" then some (.keyPress "home", 3)
  else if input.startsWith "\u001b[F" then some (.keyPress "end", 3)
  else none

private def completeMouseLength? (input : String) : Option Nat :=
  let chars := input.toList
  let rec loop (remaining : List Char) (count : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | character :: rest =>
      if character == 'M' || character == 'm' then some (count + 1)
      else loop rest (count + 1)
  if input.startsWith "\u001b[<" then loop chars 0 else none

private partial def decodeLoop (remaining : String) (events : List InputEvent) : DecodedChunk :=
    if remaining.isEmpty then
      { events := events.reverse, remainder := {} }
    else if remaining.startsWith "\u001b" then
      match escapeEvent? remaining with
      | some (event, consumed) => decodeLoop (remaining.drop consumed).toString (event :: events)
      | none =>
        match completeMouseLength? remaining with
        | some consumed =>
          let sequence := (remaining.take consumed).toString
          let event := (parseMouse sequence).getD (.keyPress sequence)
          decodeLoop (remaining.drop consumed).toString (event :: events)
        | none =>
          if remaining.length <= 2 || remaining.startsWith "\u001b[<" then
            { events := events.reverse, remainder := { text := remaining } }
          else
            let symbol := String.ofList [remaining.toList.head!]
            decodeLoop (remaining.drop 1).toString (.keyPress symbol :: events)
    else
      let symbol := String.ofList [remaining.toList.head!]
      decodeLoop (remaining.drop 1).toString (.keyPress (normalizeKey symbol) :: events)

def decodeChunk (input : String) (remainder : InputRemainder) : DecodedChunk :=
  decodeLoop (remainder.text ++ input) []

end NecoLean.Tui
