(lang dune 3.20)
(name qasminfer)

(using menhir 3.0)

(package
 (name qasminfer)
 (synopsis "Quantum circuit inference with bundled OCaml extracted from Rocq")
 (description "Build the bundled OCaml artifact extracted from the Rocq development together with the parser libraries and CLI, without requiring Rocq in the default dune workspace."))
