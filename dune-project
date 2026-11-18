(lang dune 3.21)
(using coq 0.2)
(using mdx 0.2)
(name coq-cwasm)
(version 0.1)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq))

(package
  (name coq-cwasm)
  (synopsis "CWasm and Iris-CWasm formalisation based on WasmCert-Coq 1.0")
  (description "Colored-memory WebAssembly, its metatheory and extracted interpreter, and an Iris program logic and logical relation, extending WasmCert-Coq 1.0.")
  (depends
    (coq (and (>= 8.17) (< 8.18~)))
    (coq-compcert (>= 3.11))
    (coq-ext-lib (>= 0.13.1))
    (coq-stdpp (= dev.2024-02-02.1.a2456618))
    (coq-iris (= dev.2024-02-05.0.a013468e))
    (coq-mathcomp-ssreflect (and (>= 1.16.0) (<= 1.18.0)))
    (coq-itree (>= 3.1.0))
    (coq-parseque (>= 0.2.0))
    (cmdliner (>= 1.1.0))
    (linenoise (>= 1.4.0))
    zarith
    (mdx (>= 1.9.0))
  )
  (maintainers
    "Xiaojia Rao"
    "Martin Bodin"
  )
  (authors
    "Martin Bodin"
    "Philippa Gardner"
    "Jean Pichon"
    "Xiaojia Rao"
    "Conrad Watt"
  )
)

(warnings (deprecated_coq_lang disabled))
