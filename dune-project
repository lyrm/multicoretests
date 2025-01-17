(lang dune 2.9)
(name multicoretests)
(generate_opam_files true)

(source (github jmid/multicoretests))
(authors "Jan Midtgaard" "Olivier Nicole" "Nicolas Osborne")
(maintainers "Jan Midtgaard <mail@janmidtgaard.dk>")
(license BSD-2-clause)

(package
 (name multicoretests)
 (synopsis "Experimental multicore tests of OCaml 5.0")
 (authors "Multiple contributors")
 (description "This package contains a collection of randomized QCheck tests to exercise
the multicore run-time of OCaml 5.0.")
 (depends
  base-domains
  (domainslib           (>= "0.4.2"))
  (ppx_deriving         (>= "5.2.1"))
  (qcheck-core          (>= "0.19"))
  (ppx_deriving_qcheck  (>= "0.2.0"))
; (kcas                 (>= "0.14"))
  (lockfree             (>= "0.13"))
  (qcheck-lin           (= :version))
  (qcheck-stm           (= :version))))
  ;; note: pin-depends listed in multicoretests.opam.template

(package
 (name qcheck-stm)
 (synopsis "State-machine testing library for sequential and parallel model-based tests")
 (description "A state-machine testing library based on QCheck that can generate both
sequential and parallel tests against a declarative model.")
 (depends
  base-domains
  (qcheck-core           (>= "0.19"))
  (qcheck-multicoretests-util (= :version))))

(package
 (name qcheck-lin)
 (synopsis "Linearizability testing library for multicore OCaml")
 (description "A linearizability testing library based QCheck that generates parallel tests
and checks the observed behaviour for sequential consistency.")
 (depends
  base-domains
  (qcheck-core           (>= "0.19"))
  (qcheck-multicoretests-util (= :version))))

(package
 (name qcheck-multicoretests-util)
 (synopsis "Various utility functions for property-based testing of multicore programs")
 (description "A small library of utility functions for QCheck-based testing of
multicore programs.")
 (depends
  base-domains
  (qcheck-core           (>= "0.19"))))
