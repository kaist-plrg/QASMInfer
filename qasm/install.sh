# check if opam local switch already exists
if [ ! -d "_opam" ]; then
  opam switch -y create . --deps-only --packages=ocaml-base-compiler.4.14.0 && \
  dune build && \
  opam install --deps-only .
else
  dune build && \
  opam install --deps-only .
fi
