
This repository has the Redex implementations of the calculus,
as well as the testing suites and proofs mentioned in dissertation.


External Dependencies:
Racket v7.6.
The various dependencies of Bigloo Scheme and Hop.js.
The fork of the racket pict library https://github.com/florence/pict/tree/diss
The fork of the racket redex library: https://github.com/florence/redex/tree/holes

iPython/Jupyter:
  https://ipython.org/  
  The racket library https://github.com/rmculpepper/iracket
  which has the racket kernel for ipython.


Optional:
Agda version 2.5.2, and the Adga standard library version 0.13.


The racket libraries can be installed in the same way as
this repo, described below.

This directory must be installed as a Racket package, and must be
named `esterel-calculus`. Achieve that with the command:
  % raco pkg install esterel-calculus/
run from the parent directory of the repo checkout. The `raco`
command is included with Racket.


Directory Structure:

Makefile: targets are:
      `beforecommit`:
            basic tests to run before any commit.
      `racket-build`
            compile Racket files and paper.
      `front-end`:
            test the compiler from Racket to the Redex model
      `circuits`:
            test the circuit compiler
      `redex`:
            test the Redex code, including the circuit compiler.
      `long`:
            run the long running tests.
      `agda`:
            typecheck all Agda code, and ensure that there
            are no `postulate`s or `trustMe`s.
      `dissertation`:
         build the dissertation
      `all`:
            run Agda and the long running tests.


redex: The Redex implementation of the calculus and its tests.
       Some of these tests will be skipped because because
       Esterel V5 is not included here for licensing reasons.

      `pict.rkt` has a utility function for rendering the
                 calculus as it shows up in the paper.
      `test-short.sh` runs the basic Redex tests.

redex/model: The Redex model.
      `calculus.rkt`
            contains the calculus proper.
      `reduction.rkt`
            contains the reduction stratagy
      `eval.rkt`
            contains and eval function used for testing
      `shared.rkt`
            contains shared language grammar and helper
            metafunctions.
      `concrete.rkt`
            contains a translator from Redex terms to
            Esterel programs (used for testing).
      `potential-function.rkt`
            contains the implementation of Can.
      `instant.rkt`
            implements the inter-instant and evaluator
            used for testing.
      `lset.rkt`
            contains helpers for handling sets in Redex.
      `count.rkt`
            contains the S function, for estemating potential reduction
            sequence lengths
      `deps.rkt`
            generator for the causality graphs

redex/test: contains the testing harness and Redex tests
      `binding.rkt`:
            the Redex implementation of correct binding:
            used to test the property before it was
            proven in Agda.
      `church-rosser.rkt`:
            Redex file to test the Church-Rosser property.
            Used to test the property before it was
            proven in Agda.
      `sound.rkt`:
            Redex file to test overall soundness of the model.
      `external.rkt`:
            A bridge between Redex and Esterel v5.
      `generator.rkt`:
            A generator for Redex Esterel terms, plus
            a bridge to the COS model.
      `model-test.rkt`:
            The primary testing harness. Runs a fixed
            set of tests and a small set of random tests.
      `keep-A.rkt`
            Tests for properties about the reduction semantics
            and control varialbes
      `constructivitiy.rkt`
            Tests focused on constructivity

redex/test/long-test: contains harnesses for long running tests.
      `external.rkt`:
            Run 100000000000000000 tests between COS, Redex,
            Esterel v5, and Hiphop.js (if the latter two are
            available).
      `internal.rkt`:
            Run 100000000000000000 tests between COS and Redex.
            These tests run much faster than the external ones.
      `circuits.rkt`
           Run the same number of tests, but for the circuit compiler
           and soundness of the calculus. These tests are increadibly slow.
      `run-test.rkt`:
            Run 10000 tests between all four implementations.
            These run when `make` and `make redex` are run.
      `forever.rkt`:
            Like internal.rkt, but memory limits for the tests
            are disabled. This means some random tests will
            effectively never terminate.

`circuits`: the circuit semantics implemented in redex on top of circuitous
            Also has the ipython notebooks for some of the proofs.
      *.ipynb: the ipython notebooks
      `compiler.rkt`: The circuit semantics
      `tests/direct-tests.rkt`: unit tests which
           check internals of the compiler
      `tests/eval-tests.rkt`: tests against the circuit evaluator
      `tests/guard-tests.rkt`: tests of the guard procedure
      `tests/random-tests.rkt`: implementation of the random tests against the calculus
      `tests/regression.rkt`: various regression tests
      `tests/verification.rkt`: tests that verfy that equilities hold on compiled terms

final-tests: test harness and log files for major tests
             mentioned in the paper.
      logs/internal*.log :
            logs from the tests between COS and Esterel
            Calculus only.
      logs/external*.log :
            logs from the tests between COS, Esterel Calculus,
            Esterel V5, and Hiphop.js. Are test failures here are
            logged bugs or known differences between the COS
            semantics and Esterel V5 and Hiphop.js.
      logs/circuits*.log
        Logs from the tests between the circuit semantics
        and the calculus.

HipHop: compiler from the Redex implementation of Kernel Esterel
        to HipHop.js, used for running HipHops tests.
      `find.rkt`:
            helpers to locate Hiphop.js and its tests.
      `parse.rkt`:
            a parser for the Hiphop.js test cases, and the internal
            Hiphop.js debugging syntax.
      `pretty-print.rkt`:
            final stage of the Redex -> Hiphop.js compiler that takes
            a Hiphop.js program and prints it in a runnable format.
      `run-HipHop.rkt`:
            a harness to run a Hiphop.js program with some input.
      `run-tests.rkt`:
            a harness that runs the Hiphop.js tests against Redex.
      `skip.txt`:
            the set of forms in Hiphop.js we cannot compiler to
            the Redex language.
      `to-hiphop.rkt`:
            the actual Redex to Hiphop.js compiler.

install-prefix: install locations for HipHop.js (and its
                dependencies, Bigloo Scheme and Hop), and
                Esterel V5 (not included here, as it is not
                public). install-prefix/bin can be used to
                install Bigloo and Hop.js. Hiphop.js can be installed
                by initializing the git submodule. See
                `install-prefix/README.txt` for more information.

`cos-model.rkt` : Implementation of the COS semantics in Redex.

`front-end.rkt`, `front-end-tests.rkt`, `front-end-tester.rkt`:
                  A Racket compiler from a parenthesised version
                  of surface Esterel to the Redex implementation
                  of Kernel Esterel. Used for running the Hiphop.js
                  tests.

`agda-all.rkt`: build harness for running all of the Agda code.

`info.rkt`: Racket build file.

`cross-tests`: tests which check the redex model vs the agda code. now defunct.

`agda/`: The Agda implementation of the old version of the Esterel calculus.
         Somewhat defunct.
         See `agda/README.txt` for more details.

`wg28-2020/`: draft of Robby's talk for wg28



A diagram of how the various Esterel implementations can be
translated to each other, and where those transformations
are implemented.


Surface Esterel. <-------------------------------------------------------------------------------
   |                                                                                            |
   | `front-end.rkt`                                                                            |
   |                                                                                            |
   |                                                                                            | `hiphop/parse.rkt`
   v                                                                                            |
Redex Model.----------------------------------------------------------                          |
   |                             |                    |              |                          |
   | `redex/model/external.rkt`  | `cross-tests/`     | `circuits/`  | `hiphop/to-hiphop.rkt`   |
   |                             |                    |              |                          |
   |                             |                    |              |                          |
   V                             V                    V              V                          |
Esterel v5.                    Agda.               Circuits        Hiphop.js.---------------------


Note that `hiphop/parse.rkt` is not a total transformation
because of embedded javascript code. In addition `front-end.rkt`
may embed Racket code into the Redex model. Such programs
cannot be transformed into the other implementations.
