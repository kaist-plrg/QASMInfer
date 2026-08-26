(lang dune 3.24)
(name qasminfer)

; Rocq integration
(using rocq 0.14)
(using menhir 3.0)

(package
 (name qasminfer)
 (synopsis "Example Rocq extraction + OCaml executable wired with dune")
 (description "Build Rocq proof artifacts, extract them to OCaml, patch the generated sources, and build a consumer executable in one dune workspace."))
