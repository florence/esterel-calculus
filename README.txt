This repository contains the software artifact for
the paper "A Calculus for Esterel"

It has the Redex and Agda implementations of the calculus,
as well as the testing suites and proofs mentioned in the paper.


External Dependencies:

Agda version 2.5.2, and the Adga standard library version 0.13.
Racket v7.0.
The various dependencies of Bigloo Scheme and Hop.js.

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
      `redex`:
            test the Redex code (which runs agains the Agda code).
      `long`:
            run the long running tests.
      `agda`:
            typecheck all Agda code, and ensure that there
            are no `postulate`s or `trustMe`s.
      `paper`:
            build the paper and check the statements of the
            proofs against the Agda codebase.
      `no-agda-paper`:
            build the paper but skip checking against Agda.
      `all`:
            run Agda and the long running tests.


agda: The Agda implementation of the Esterel calculus.
      See `agda/README.txt` for more details.

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
            contains the std reduction.
      `eval.rkt`
            contains and eval function used for testing and
            comparing to Agda.
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

redex/test/long-test: contains harnesses for long running tests.
      `external.rkt`:
            Run 100000000000000000 tests between COS, Redex,
            Esterel v5, and Hiphop.js (if the latter two are
            available).
      `internal.rkt`:
            Run 100000000000000000 tests between COS and Redex.
            These tests run much faster than the external ones.
      `run-test.rkt`:
            Run 10000 tests between all four implementations.
            These run when `make` and `make redex` are run.
      `forever.rkt`:
            Like internal.rkt, but memory limits for the tests
            are disabled. This means some random tests will
            effectively never terminate.


cross-tests: tests that check that the Agda and Redex models
             are defining the same calculus. See `cross-tests/
             README.txt` for more information.

final-tests: test harness and log files for major tests
             mentioned in the paper.
      logs/agda*.log :
            logs from the agda/redex cross tests
      logs/internal*.log :
            logs from the tests between COS and Esterel
            Calculus only.
      logs/external*.log :
            logs from the tests between COS, Esterel Calculus,
            Esterel V5, and Hiphop.js. Are test failures here are
            logged bugs or known differences between the COS
            semantics and Esterel V5 and Hiphop.js.

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

paper: Source for the paper.

`cos-model.rkt` : Implementation of the COS semantics in Redex.

`front-end.rkt`, `front-end-tests.rkt`, `front-end-tester.rkt`:
                  A Racket compiler from a parenthesised version
                  of surface Esterel to the Redex implementation
                  of Kernel Esterel. Used for running the Hiphop.js
                  tests.

`agda-all.rkt: build harness for running all of the Agda code.

`info.rkt: Racket build file.






A diagram of how the various Esterel implementations can be
translated to each other, and where those transformations
are implemented.


Surface Esterel. <-------------------------------------------------------------
   |                                                                          |
   | `front-end.rkt`                                                          |
   |                                                                          |
   |                                                                          | `hiphop/parse.rkt`
   v                                                                          |
Redex Model.----------------------------------------                          |
   |                             |                 |                          |
   | `redex/model/external.rkt`  | `cross-tests/`  | `hiphop/to-hiphop.rkt`   |
   |                             |                 |                          |
   |                             |                 |                          |
   V                             V                 V                          |
Esterel v5.                    Agda.            Hiphop.js.---------------------


Note that `hiphop/parse.rkt` is not a total transformation
because of embedded javascript code. In addition `front-end.rkt`
may embed Racket code into the Redex model. Such programs
cannot be transformed into the other implementations.

How To Use:

Below follows some example changes you might make to this
artifact, and some of what you may need to modify to do so.

Add or modify rules in the calculus:
  Assuming everything is set up and `make` works.
  1. Change `redex/modex/shared.rkt` to update
     the language grammar.
  2. Change `redex/model/calculus.rkt` to
     update the rules.
  3. Change `redex/model/standard.rkt` to make
     corresponding changes to the std reduction.
  4. Update `front-end.rkt` to be able to compile
     to the new forms
  5. Update `redex/test/binding.rkt` to handle
     correct binding of any new forms
  
  --- If you want to test against external implementation
                 (say you are adding Esterel v7 features) ---
  5. Follow below sets of instructions to update
     Esterel v5 and Hiphop.js.
  --- end if

  --- If you want to test against an updated COS model ---
  6. Change `cos-model.rkt` to add the new grammar
     and semantics.
  --- end if

  7. Run `raco test` on  all files in `redex/model` and
     on all files prefixed with `front-end`. this will
     run the basic tests.
  8. Run `raco test` on `redex/test/model-test.rkt`.
     This will run the tests against the COS, Esterel,
     and Hiphop.js pass. If you are not testing against
     Esterel and Hiphop.js, uninstalling either of those
     will skip that check. If you not testing against
     the COS, Esterel, and Hiphop.js, skip this step.
     Any other combination of tests against those three
     will require modifications to `model-test.rkt`.
  9. Run `raco test` on `redex/test/binding.rkt` and
     `redex/test/church-rosser.rkt`. If all of these
     passed, it appears that the Redex model works,
     and has a nonzero probability of being correct.
  10. Update the Agda proofs. See the README there for
      a sense of which files to modify.
  11. Run `make agda` to make sure the proofs work.
  12. Update the files in `cross-test/` to generate
      the new Agda code.
  13. Run `raco test` on all files in `cross-tests/`
      to sanity check Redex model against the Agda model.
  14. Run `make` to sanity check that everything works.
  15. Modify `final-tests/run.rkt` to run the whichever
      tests you want to run (against COS, Agda, Esterel,
      or HipHop.js).
  16. Clear out `final-tests/logs/`
  17. Run `final-tests/run.rkt` in as many processes as
      you want on your favorite multi-core machine.
  18. After you desired Long Amount Of Time has passed,
      check the logs in `final-tests/logs/` for any
      test failures.
  

To update Agda to a new version: 
  Assuming you already have Agda installed, you will need to
  1. update Agda.
  2. update the std library.
  3. update the proofs in `agda/`
  4. change `cross-tests/` Redex to Agda translator
     to generate Agda code consistent with the new
     version of Agda.
  5. run `make` to make sure everything compiles,
     type checks, and passes its tests.
  6. run `make paper` to check that the statements in
     the paper still check out w.r.t the Agda proofs.



Update to a new Esterel version:
  Assuming Esterel is already in the `install-prefix/` directory.
  1. Replace the Esterel with a new Esterel version.
  2. Update `redex/model/concrete.rkt` to compile
     Redex to the new version
  3. Update `redex/test/external.rkt` to handle new
     CLI interface and possible errors.
  4. Run `make` to check new tests.


Update Hiphop.js Version:
  Assuming Hiphop.js, and it dependencies Bigloo Scheme
  and Hop.js are already in `install-prefix/`
  1. Delete `install-prefix/bigloo`
  2. Update `install-bin/install-bigloo.sh` to install
     the new version.
  3. Update `install-bin/install-hop.sh` to install
     the new version.
  4. Update the git submodule in `install-prefix/hiphop/`
     to point to the new version.
  5. Run `install-bin/install-bigloo.sh` and
     `install-bin/install-hop.sh` in that order.
  6. Update `hiphop/parse.rkt` to parse the new Hiphop.js
     format and test cases.
  7. Update `hiphop/pretty-print.rkt` for any changes
     to the Hiphop.js execution harness
  8. Update `hiphop/to-hiphop.rkt` for any changes
     to the Hiphop.js syntax.
  9. Run `make` to test changes
