# QASMInfer: Rocq extraction + OCaml executable with dune

This workspace shows how to:

- compile Rocq sources with dune,
- extract them to OCaml,
- prepend custom header lines to the generated `.ml/.mli`,
- consume the extracted modules from a regular OCaml library/executable.

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
1) `theories/dune` builds the theory (with `include_subdirs qualified` so you can nest `theories/foo/*.v` and refer to them as `From QASMInfer.foo Require ...`) and runs `coqtop` on `Extract.v`, which drops `Core.ml` / `Core.mli` into the build dir. Immediately after, the header snippets are prepended.
2) `src/lib/dune` copies those generated files into `src/lib/` (with `mode promote-until-clean` so editors/LSPs can see them) so the OCaml library can use them as modules.
3) The library is wrapped (`Qasminfer_logic`) and re-exports a friendly API from `logic.ml`.
4) `src/bin/main.ml` links against that library to produce the executable.

Running `dune clean` wipes everything under `_build/`; the extracted files are not checked in.
