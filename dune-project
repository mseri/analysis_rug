(lang dune 3.21)
(using coq 0.8)
(using directory-targets 0.1)
(warnings (deprecated_coq_lang disabled))

(package
 (name coq-analysis)
 (synopsis "Formalized real analysis with Waterproof")
 (depends rocq-core rocq-stdlib coq-waterproof))
