import NecoLean.Cli

set_option autoImplicit false

inductive Command where
  | hello (name : String)

private def decodeCommand (result : NecoLean.Cli.DecodeResult) : Except NecoLean.Cli.Failure Command :=
  match result.command, result.positionals with
  | "hello", [name] => .ok (.hello name)
  | _, _ => .error (.invalidCommand "expected: hello <name>")

private def schema : NecoLean.Cli.Schema Command :=
  { commands := [{ name := "hello", positional := 1 }]
    decodeCommand }

def main (arguments : List String) : IO UInt32 := do
  match NecoLean.Cli.decode schema arguments with
  | .ok (.hello name) =>
    IO.println s!"hello, {name}"
    return 0
  | .error _ =>
    IO.eprintln "usage: neco-lean-example-cli hello <name>"
    return 2
