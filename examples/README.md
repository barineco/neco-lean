# neco-lean examples

This directory contains small programs that compose the library modules. KDL
documents and other non-Lean inputs live under `assets/`.

Run each command from the repository root. `lake build` builds all three
examples.

## Command-line decoding

[CliBasic.lean](CliBasic.lean) defines the command form and its decoded result
type.

```sh
lake exe neco-lean-example-cli hello Ada
```

The command prints:

```text
hello, Ada
```

## Reading a KDL document

[KdlBasic.lean](KdlBasic.lean) reads a file as bytes, parses a KDL document, and
prints the names of its top-level nodes.

```sh
lake exe neco-lean-example-kdl examples/assets/document.kdl
```

This example connects:

- file input: `NecoLean.System`
- KDL parsing: `NecoLean.Kdl`

## Rendering a KDL tree in a terminal

[KdlTreeTui.lean](KdlTreeTui.lean) translates the KDL hierarchy into a TUI tree
and displays it in an interactive POSIX terminal.

```sh
lake exe neco-lean-example-kdl-tui examples/assets/document.kdl
```

The program performs these steps:

1. read the KDL file as bytes
2. parse the bytes into a KDL document
3. translate each KDL node into `NecoLean.Tui.UiNode`
4. initialize a screen model from `NecoLean.Tui.Tree`
5. connect the model to the terminal with `NecoLean.Tui.Posix.runModel`

`KdlTreeTui.lean` contains the complete transformation. Its input document is
`assets/document.kdl`.

The interface accepts these keys:

- `up`, `down`: move the selection
- `enter`: expand or collapse a node
- `t`: move the detail pane
- `+`, `-`: resize the detail pane
- `?`: show help
- `escape`: close help
- `q`: leave the interface
- `ctrl-c`: interrupt input and leave the interface
- mouse click: select a visible node
- mouse wheel: scroll the tree

Standard input and standard output must be TTY streams. Exit restores the
terminal display and input modes.
