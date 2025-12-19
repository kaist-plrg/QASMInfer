(lang dune 3.20)
(name qasminfer)

; Coq/Rocq integration
(using coq 0.8)
(using menhir 3.0)

(package
 (name qasminfer)
 (synopsis "Example Rocq extraction + OCaml executable wired with dune")
 (description "Build Rocq proof artifacts, extract them to OCaml, patch the generated sources, and build a consumer executable in one dune workspace."))
