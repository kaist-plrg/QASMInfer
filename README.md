# QASMInfer

Verified Exact Inference for Quantum Circuits

## Prereqs

- `dune` (tested with 3.20.x)
- `rocq`/`coq` (tested with Rocq 9.1.0)
- `ocaml` (the version used by your Rocq switch)

Suggested install via opam:

```bash
opam install dune rocq
```

## Layout

- `theories/`: Rocq theory (`Core.v`) plus extraction driver (`Extract.v`) and header fragments that get prepended to the generated files.
- `scripts/patch_extraction.sh`: simple helper that prepends a header file to a generated file.
- `src/lib/`: OCaml library that copies in the extracted sources and re-exports a small API.
- `src/bin/`: OCaml executable using the library.

## Build and run

```bash
dune build                # builds Rocq theory, extracts to OCaml, builds library + exe
dune exec ocaml/app/main.exe
```

## Customizing the injected headers

Edit `rocq/extraction_header.ml` / `rocq/extraction_header.mli` to add whatever lines you need at the top of every extracted file (e.g. warning controls, shared `open`s). The `scripts/patch_extraction.sh` script prepends them right after extraction.

## How it fits together

1. `theories/dune` builds the theory (with `include_subdirs qualified` so you can nest `theories/foo/*.v` and refer to them as `From QASMInfer.foo Require ...`) and runs `coqtop` on `Extract.v`, which drops `extracted/extracted.ml` into the build dir. Immediately after, the header snippets are prepended.
2. `src/lib/extracted/dune` copies that generated file into `src/lib/extracted/` (with `mode promote-until-clean` so editors/LSPs can see it) so the OCaml library can use it.
3. The library `qasminfer.extracted` exposes the generated module as `Extracted`.
4. `src/bin/main.ml` links against that library to produce the executable.

Running `dune clean` wipes everything under `_build/`; the extracted files are not checked in.
