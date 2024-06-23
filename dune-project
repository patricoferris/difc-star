(lang dune 3.15)

(using mdx 0.4)

(generate_opam_files true)

(license MIT)

(package
  (synopsis "A simple decentralised information flow control (DIFC) library extracted from FStar")
  (name difc)
  (depends
    fstar))
