# neco-lean

[日本語](README-ja.md)

`neco-lean` is a library for building command-line tools and TUIs (terminal user interfaces) in Lean 4.
It is extracted from a personal codebase.

## Features

The modules for each purpose, and what each of them does, are as follows.

| Purpose | Modules | Capabilities |
|---|---|---|
| Floating-point conversion | `NecoLean.Binary64` | convert decimal numbers to IEEE 754 double-precision bits, rounding half to even |
| Files and child processes | `NecoLean.System` | read and write bytes, run a given command |
| Command-line input and messages | `NecoLean.Cli`, `NecoLean.Diagnostic` | parse arguments, build messages with source positions |
| JSON | `NecoLean.Json` | parse, and output with a fixed key order (up to 128 levels of nesting) |
| KDL documents | `NecoLean.Kdl`, `NecoLean.Kdl.Ast` | parse and build documents, look up nodes, resolve references |
| Byte input | `NecoLean.Scanner` | read tokens, integers, and lines in sequence |
| Byte output and hashing | `NecoLean.Printer`, `NecoLean.Digest` | build output, compute SHA-256 |
| Iterative calculation | `NecoLean.Fixpoint` | compute fixed points with a history of each iteration |
| Local judging | `NecoLean.Judge` | find test cases, measure run time, judge results |
| LLVM IR | `NecoLean.Llvm` | build and validate IR, output it as text, compile it with `clang` |
| TUI | `NecoLean.Tui`, `NecoLean.Tui.Posix` | build screens and run them interactively on a POSIX terminal |

Every failure at run time is returned as a value of a result type.

## Build and test

The project uses Lean 4.32.1, and this version is specified in `lean-toolchain`.

```sh
cd path/to/neco-lean
elan show
lake --version
lake build
lake exe neco-lean-tests -- all
```

To run with the version given explicitly, use the following commands:

```sh
elan run leanprover/lean4:v4.32.1 lake build
elan run leanprover/lean4:v4.32.1 lake exe neco-lean-tests -- all
```

### Supported platforms

neco-lean runs on Linux and macOS.
Compiling LLVM IR requires `clang`.

## Importing

To use all the public modules together, write the following:

```lean
import NecoLean
```

You can also import only the modules you use:

```text
NecoLean.Binary64
NecoLean.System
NecoLean.Diagnostic
NecoLean.Cli
NecoLean.Json
NecoLean.Digest
NecoLean.Fixpoint
NecoLean.Scanner
NecoLean.Printer
NecoLean.Judge
NecoLean.Llvm
NecoLean.Kdl
NecoLean.Kdl.Ast
NecoLean.Tui
NecoLean.Tui.Posix
```

`import NecoLean` loads the modules listed above.
The test module `NecoLean.Kdl.Vectors`, which uses the official KDL test vectors, is imported on its own when needed.

## Examples

`examples/` contains examples that use the public modules.

```sh
lake exe neco-lean-example-cli hello Ada
lake exe neco-lean-example-kdl examples/assets/document.kdl
lake exe neco-lean-example-kdl-tui examples/assets/document.kdl
```

- [CliBasic.lean](examples/CliBasic.lean): parse command-line arguments
- [KdlBasic.lean](examples/KdlBasic.lean): read and parse a KDL file
- [KdlTreeTui.lean](examples/KdlTreeTui.lean): show a KDL document as a tree on the terminal screen

Each example is described in [examples/README.md](examples/README.md).

## License

neco-lean is released under the [MIT License](LICENSE).
The test data in `test/kdl-test-cases/` comes from the [official KDL test suite](https://github.com/kdl-org/kdl/tree/4e4c0af9333819aede3cd4867bbc8702dd78f96c/tests/test_cases) and is licensed under CC-BY-SA 4.0.
