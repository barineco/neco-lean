# Changelog

## 0.1.0

NecoLean provides fifteen public modules for command-line tools and terminal applications:

- `NecoLean.System`: byte-oriented file operations and caller-selected child processes with explicit failures.
- `NecoLean.Diagnostic`: validated half-open spans and source-positioned messages.
- `NecoLean.Cli`: schema-based command-line decoding.
- `NecoLean.Json`: JSON decoding, deterministic encoding, and typed failures.
- `NecoLean.Digest`: pure Lean SHA-256 calculation and hexadecimal formatting.
- `NecoLean.Fixpoint`: monotone closure calculation with validation and an ordered iteration trace.
- `NecoLean.Scanner`: token, integer, signed integer, and line scanning over byte input.
- `NecoLean.Printer`: ordered byte-output accumulation and filesystem writes.
- `NecoLean.Judge`: case discovery, measured execution, verdict generation, and explicit runtime injection.
- `NecoLean.Binary64`: rounding of finite decimal values to IEEE 754 binary64 bit patterns, with typed overflow failures.
- `NecoLean.Llvm`: typed LLVM IR construction, validation, deterministic encoding, and compilation.
- `NecoLean.Kdl`: KDL parsing, builders, and typed failures.
- `NecoLean.Kdl.Ast`: named-node lookup and reference resolution.
- `NecoLean.Tui`: terminal screen models, layout, rendering, input events, and runtime sampling.
- `NecoLean.Tui.Posix`: interactive POSIX terminal execution with terminal-state restoration.

A screen model runs through one of two entry points:

- `runModelWithBackend`: runs on a caller-supplied terminal backend.
- `Posix.runModel`: runs on a POSIX terminal.

LLVM IR construction covers these elements:

- binary64 values and operations
- function pointers and indirect calls
- typed pointers with struct and array field access, null pointers, and pointer comparison
- tail calls, bitwise and shift instructions, and bitcasts

Load, store, and address calculation take their types from the pointer operand. Compilation accepts runtime C sources, produces owned object files, and links them into an executable. Validation failures name the function, block, and instruction.

JSON decoding accepts arrays and objects of any length, nested up to 128 levels; a deeper collection fails with a nesting-limit failure. JSON roundtrips preserve value meaning. Encoding recursively orders object fields by Unicode scalar value and reports duplicate object keys as typed failures.

The package supports Linux and macOS. On Linux, LLVM compilation uses `clang` from the executable search path. On macOS, LLVM compilation uses Xcode Command Line Tools and obtains the active SDK path through `xcrun`.
