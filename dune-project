(lang dune 3.21)

(name ila)

(version 0.1.0)

(generate_opam_files true)

(source
 (github glassala/ila))

(authors "Will Sweet <avsqxm@gmail.com>")

(license MIT)

(package
 (name ila)
 (synopsis "A basic untyped λ-calculus.")
 (description
  "A minimal implementation of untyped λ-calculus with REPL.
  Syntax has the esoteric property of user-facing de Bruijn 1-indices.
  Abstractions take the form n.M where n is a positive integer and M
  is a λ-term; where 0.M ≡ M and t is a λ-term, β-reduction
  proceeds by the rule '(n.M) t ->β (n - 1).M[n := t].'")
 (depends ocaml)
 (tags ("λ-calculus")))