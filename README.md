# CWasmCert-Coq

CWasmCert-Coq is a Coq/Rocq formalization of **ColorWebAssembly (CWasm)**, an
extension of WebAssembly 1.0 with colored pointers and colored memory. It builds
on the WebAssembly 1.0 development of
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) and includes
**Iris-CWasm**, a program logic and logical relation for reasoning about known
code and interactions with unknown, well-typed code.

CWasm adds explicit allocation and deallocation, colored-memory loads and
stores, pointer arithmetic, and pointer demotion. Colors distinguish
allocations and their lifetimes; numeric/pointer tags protect pointer integrity.
Demotion removes a pointer copy's authority to free its allocation while
preserving its ability to read and write.

This repository contains both the inherited Wasm 1.0 theories and the CWasm
extension. The opam package name is `coq-cwasm`; the logical namespaces are
`Wasm`, `CWasm`, and `CWasm.iriscwasm.*`.

## Repository layout

- [`theories/`](theories/): inherited Wasm 1.0 formalization, including typing,
  operational semantics, metatheory, parsing, and interpretation (`Wasm`).
- [`theories/cwasmcert/`](theories/cwasmcert/): CWasm syntax, colored memory,
  operational semantics, typing, metatheory, and interpreter (`CWasm`).
- [`theories/iriscwasm/`](theories/iriscwasm/): Iris-CWasm resources, weakest
  preconditions, instantiation rules, logical relation, and examples.
- [`src/`](src/): extraction to OCaml and the interpreter command-line frontend.
- [`tests/`](tests/): Wasm binary examples and executable interpreter tests.

Some useful entry points are:

- [`color_ptr.v`](theories/cwasmcert/color_ptr.v) and
  [`colored_memory.v`](theories/cwasmcert/colored_memory.v): pointers, tagged
  bytes, and the allocator.
- [`iris_rules_cmem.v`](theories/iriscwasm/rules/iris_rules_cmem.v): colored-memory
  weakest-precondition rules.
- [`iris_logrel.v`](theories/iriscwasm/logrel/iris_logrel.v) and
  [`iris_fundamental.v`](theories/iriscwasm/logrel/iris_fundamental.v): the logical
  relation and fundamental theorem.
- [`buffer/`](theories/iriscwasm/examples/buffer/) and
  [`colstack/`](theories/iriscwasm/examples/colstack/): verified clients and their
  operational adequacy results.

## Installation

Install and initialize [opam](https://opam.ocaml.org/doc/Install.html) first,
and have Git available to fetch the Iris package repository.
Run the following commands **from this repository's root**.
The tested toolchain uses **OCaml 4.14.2 and Coq 8.17.1**;
the package requires Coq 8.17.x and Dune 3.21 or later.

### Creating a separate switch

For a fresh environment, create a switch before running the installation
commands below:

```bash
opam switch create cwasmcert-coq ocaml-base-compiler.4.14.2
eval "$(opam env --switch=cwasmcert-coq --set-switch)"
```

`opam install .` will then install Coq and the remaining dependencies into that
switch. If you already have a compatible switch, you can use it instead.

### Installing the package

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
opam install .
```

The package declares its dependencies, including the Iris and stdpp snapshots,
so they do not need to be installed individually. The additional `iris-dev`
repository is required because the development uses these specific snapshots:

- `coq-iris.dev.2024-02-05.0.a013468e`
- `coq-stdpp.dev.2024-02-02.1.a2456618`

If a repository is already configured in your switch, skip its `opam repo add`
command. These commands build and install the `coq-cwasm` package, including its
Coq libraries and the `wasm_coq_interpreter` executable. Installing dependencies
can require several GB of RAM; upstream recommends 4–8 GB. Use
`opam install . -j 2` to limit build parallelism on a smaller machine.

## Building and testing during development

To install the dependencies and build the working directory without installing
the project itself:

```bash
opam install . --deps-only
opam exec -- dune build
```

Use Dune to build the theories. It places compiled files under `_build/`.
[`_CoqProject`](_CoqProject) supplies editor load paths into that build tree;
it is not the build entry point.

Run the interpreter tests with:

```bash
opam exec -- dune runtest
```

The supplied binaries exercise inherited Wasm examples. They complement the
Coq proofs and are not a complete conformance suite for the CWasm extension.
The `bigrec` stress test performs 1,048,576 nested calls and can take a very long
time to finish; it is not part of a plain `dune build` or `opam install .`.

If a build cannot find `iris.proofmode`, `iris.algebra`, or `stdpp`, check the
active switch and install the declared dependencies there:

```bash
opam switch show
opam install . --deps-only
opam exec -- dune build
```

Installing dependencies in another switch does not make them available to this
one. `dune build` checks the sources but does not install opam dependencies.

Coq 8.16 is too old for the Iris-CWasm sources: it reports a syntax error at
class fields written with `::`. Running `opam install . --deps-only` also brings
Coq into the supported 8.17.x range; the package does not support Coq 8.18 or
later.

## Running the interpreter

After a local build:

```bash
opam exec -- dune exec -- wasm_coq_interpreter tests/floatmul.wasm -r main
```

Add `--vi` to display intermediate execution states:

```bash
opam exec -- dune exec -- wasm_coq_interpreter tests/floatmul.wasm -r main --vi
```

After `opam install .`, the installed executable is also available directly
inside the switch:

```bash
opam exec -- wasm_coq_interpreter tests/floatmul.wasm -r main
```

The executable is extracted from the CWasm theories. Its OCaml frontend supplies
a finite, 18-byte pointer representation in [`src/shim.ml`](src/shim.ml).

## Formalization status

The development includes type preservation, progress, allocator/memory
well-formedness preservation, and interpreter soundness results. Iris-CWasm
adds instruction specifications, a fundamental theorem of its logical relation,
and client-specific adequacy results for the buffer and colored-stack examples.
These adequacy results permit traps and divergence; they do not guarantee
termination or constitute a general trace-level robust-memory-safety theorem.

Results involving pointer serialization are parameterized by the abstract
`PointerBytes` interface. The finite representation used by the executable is
not a verified implementation of the interface for arbitrary unbounded
pointers. The experimental binary parser is also inherited from WasmCert;
parser correctness is not established here.

## Origins and license

The base Wasm formalization comes from
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq), described in
[Two Mechanisations of WebAssembly 1.0](https://doi.org/10.1007/978-3-030-90870-6_4).
Iris-CWasm builds on the approach developed in
[Iris-Wasm](https://doi.org/10.1145/3591265) and
[Iris-MSWasm](https://doi.org/10.1145/3689722).

The inherited copyright notice is (C) M. Bodin, P. Gardner, J. Pichon, C. Watt,
X. Rao, 2019–2023. See [LICENSE.txt](LICENSE.txt) for the MIT license. Quotations
from the WebAssembly standard marked `std-doc` belong to their respective
authors.
