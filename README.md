LEAN with MLIR
==============

- clone submodule `lz`, which in-turn has submodule `llvm-project`.
- build llvm-project, enable MLIR. Add `bin` to path.
- build `lz`, using the MLIR build. Add `bin` to path.
- follow lean4 instructions to build this project
- export variable `LEAN4_PATH` to the root path of this project.
- go back to `lz/lean-linking-incantations`, and `make`.

- run `make test` to run all tests.
- to manually invoke tests, go into `build/release/stage1`, and run `ctest`.

Original Readme
===============

This is the repository for **Lean 4**, which is currently being released as milestone releases towards a first stable release.
[Lean 3](https://github.com/leanprover/lean) is still the latest stable release.

# About

- [Homepage](https://leanprover.github.io)
- [Manual](https://leanprover.github.io/lean4/doc/)
- [FAQ](https://leanprover.github.io/lean4/doc/faq.html)

# Installation

See [Setting Up Lean](https://leanprover.github.io/lean4/doc/setup.html).

# Contributing

Please read our [Contribution Guidelines](CONTRIBUTING.md) first.

# Building from Source

See [Building Lean](https://leanprover.github.io/lean4/doc/make/index.html).
