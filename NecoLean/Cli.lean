set_option autoImplicit false

namespace NecoLean.Cli

inductive ValueKind where
  | flag
  | required
  deriving Repr, BEq, DecidableEq

structure OptionSpec where
  name : String
  kind : ValueKind
  deriving Repr, BEq

structure CommandSpec where
  name : String
  options : List OptionSpec := []
  positional : Nat := 0
  deriving Repr, BEq

inductive Failure where
  | missingCommand
  | unknownCommand (name : String)
  | unknownOption (name : String)
  | missingValue (option : String)
  | unexpectedArgument (value : String)
  | unexpectedEnd
  | invalidCommand (message : String)
  deriving Repr, BEq

structure DecodedOption where
  name : String
  value : Option String
  deriving Repr, BEq

structure DecodeResult where
  command : String
  flags : List String
  options : List DecodedOption
  positionals : List String
  deriving Repr, BEq

structure Schema (command : Type) where
  commands : List CommandSpec
  decodeCommand : DecodeResult → Except Failure command

private def findCommand (commands : List CommandSpec) (name : String) : Option CommandSpec :=
  commands.find? (fun command => command.name == name)

private def findOption (options : List OptionSpec) (name : String) : Option OptionSpec :=
  options.find? (fun option => option.name == name)

private def consumeOptions (spec : CommandSpec) (arguments : List String) : Except Failure DecodeResult :=
  let rec loop (remaining : List String) (flags : List String) (options : List DecodedOption) (positionals : List String) : Except Failure DecodeResult :=
    match remaining with
    | [] =>
      if positionals.length == spec.positional then .ok { command := spec.name, flags := flags.reverse, options := options.reverse, positionals := positionals.reverse }
      else .error (.unexpectedEnd)
    | argument :: rest =>
      if argument.startsWith "--" then
        match findOption spec.options argument with
        | none => .error (.unknownOption argument)
        | some option =>
          match option.kind with
          | .flag => loop rest (argument :: flags) options positionals
          | .required =>
            match rest with
            | [] => .error (.missingValue option.name)
            | value :: tail =>
              if value.startsWith "--" then .error (.missingValue option.name)
              else loop tail flags ({ name := option.name, value := some value } :: options) positionals
      else if positionals.length < spec.positional then
        loop rest flags options (argument :: positionals)
      else
        .error (.unexpectedArgument argument)
  loop arguments [] [] []

protected def decode {command : Type} (schema : Schema command) (arguments : List String) : Except Failure command :=
  match arguments with
  | [] => .error .missingCommand
  | commandName :: rest =>
    match findCommand schema.commands commandName with
    | none => .error (.unknownCommand commandName)
    | some commandSpec =>
      match consumeOptions commandSpec rest with
      | .error failure => .error failure
      | .ok result => schema.decodeCommand { result with command := commandName }

end NecoLean.Cli
