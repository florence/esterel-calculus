This repository contains the software artifact for the paper "A Calculus for Esterel"

It has the Redex and Agda implementations of the calculus, as well as the testing suites and proofs mentioned in the paper.

External Dependencies:

Agda version 2.5.2, and the Adga standard library version 0.13.
Racket v7.0.
The various dependencies of Bigloo Scheme and Hop.

This directory must be installed as a racket package, and must be
named `esterel-calculus`. Achieve that with the command:
  % raco pkg install esterel-calculus/
run from the parent directory of the repo checkout. The `raco`
command is included with Racket.

Directory Structure:

Makefile: targets are:
          `beforecommit` basic tests to run before any commit.
          `racket-build` compile racket files and paper.
          `front-end`: test the compiler from racket to the redex model
          `redex`: test the redex code (which runs agains the agda code).
          `long`: run the long running tests.
          `agda`: typecheck all agda code, and ensure that there are no `postulate`s or `trustMe`s.
          `paper`: build the paper and check the statements of the proofs against the agda codebase.
          `no-agda-paper`: build the paper but skip checking against agda.
          `all`: run agda and the long running tests.


agda: The agda implementation of the esterel calculus. See `agda/README.txt` for more details.

redex: The redex implementation of the calculus and its tests.
       Some of these tests will be skipped because because Esterel V5 is not included here for licensing reasons.

       `pict.rkt` has a utility function for rendering the calculus as it shows up in the paper.
       `test-short.sh` runs the basic redex tests.

redex/model: The redex model.
             `calculus.rkt` has the calculus proper.
             `reduction.rkt` has the std reduction.
             `eval.rkt` has and eval function used for testing and comparing to agda.
             `shared.rkt` has shared language grammar and helper metafunctions.
             `concrete.rkt` has a translator from redex terms to esterel programs (used for testing).
             `potential-function.rkt` has the implementation of Can.
             `instant.rkt` implements the inter-instant and evaluator used for testing.
             `lset.rkt` has helpers for handling sets in redex.

redex/test: contains the testing harness and redex tests
            `binding.rkt`: redex implementation of correct binding: used to test the property before it was proven in agda.
            `church-rosser.rkt`: redex file to test the church-rosser property. used to test the property before it was proven in agda.
            `sound.rkt`: redex file to test overall soundness of the model.
            `external.rkt`: a bridge between redex and Esterel v5.
            `generator.rkt`: a generator for redex esterel terms, plus a bridge to the COS model.
            `model-test.rkt`: the primary testing harness. runs a fixed set of tests and a small set of random tests.

redex/test/long-test: contains harnesses for long running tests.
                      `external.rkt`: run 100000000000000000 tests between COS, Redex, Esterel v5, and HipHop (if the latter two are available).
                      `internal.rkt`: run 100000000000000000 tests between COS and Redex. These tests run much faster than the external ones.
                      `run-test.rkt`: run 10000 tests between all four implementations. These run when `make` and `make redex` are run.
                      `forever.rkt`: like internal.rkt, but memory limits for the tests are disabled. This means some random tests will
                                       effectively never terminate.


cross-tests: tests that check that the agda and redex models are defining the same calculus. See `cross-tests/README.txt` for more information.

final-tests: test harness and log files for major tests mentioned in the paper.
  logs/agda*.log : logs from the agda/redex cross tests
  logs/internal*.log : logs from the tests between COS and Esterel Calculus only.
  logs/external*.log : logs from the tests between COS, Esterel Calculus,
    Esterel V5, and HipHop. Are test failures here are logged bugs or known differences between the COS semantics and Esterel V5 and HipHop.

hiphop: compiler from the redex implementation of kernel esterel to HipHop.js, used for running hiphops tests.
        `find.rkt`: helpers to locate hiphop and its tests.
        `parse.rkt`: a parser for the hiphop test cases, and the internal hiphop debugging syntax.
        `pretty-print.rkt`: final stage of the redex->hiphop compiler that takes a hiphop program and prints it in a runnable format.
        `run-hiphop.rkt`: a harness to run a hiphop program with some input.
        `run-tests.rkt`: a harness that runs the hiphop tests against redex.
        `skip.txt`: the set of forms in hiphop we cannot compiler to the redex language.
        `to-hiphop.rkt`: the actual redex to hiphop compiler.

install-prefix: install locations for hiphop.js (and its dependencies, bigloo scheme and hop), and Esterel V5 (not included here, as it is not public). install-prefix/bin can be used to install bigloo and hop. hiphop can be installed by initializing the git submodule. See `install-prefix/README.txt` for more information.

paper: Source for the paper.

`cos-model.rkt` : Implementation of the COS semantics in redex.

`front-end.rkt`, `front-end-tests.rkt`, `front-end-tester.rkt`: A racket compiler from a parenthesised version of surface esterel to the redex implementaiton of kernel esterel. Used for running the hiphop tests.

`agda-all.rkt: build harness for running all of the agda code.

`info.rkt: Racket build file.






A diagram of how the various esterel implentations can be translated to eachother, and where those transformations are implemented.


Surface Esterel. <-------------------------------------------------------------
   |                                                                          |
   | `front-end.rkt`                                                          |
   |                                                                          |
   |                                                                          | `hiphop/parse.rkt`
   v                                                                          |
Redex Model.----------------------------------------                          |
   |                             |                 |                          |
   | `redex/model/externa.rkt`   | `cross-tests/`  | `hiphop/to-hiphop.rkt`   |
   |                             |                 |                          |
   |                             |                 |                          |
   V                             V                 V                          |
Esterel v5.                    Agda.            HipHop.js.---------------------


Note that `hiphop/parse.rkt` is not a total transforamtion because of embedded javascript code. In
addition `front-end.rkt` may embed racket code into the redex model. Such programs cannot be
transformed into the other implementations.

How To Use:

Below follows some example changes you might make to this artifact, and some of what you may need to modify to do so.

Add or modify rules in the calculus:
  Assuming everything is set up and `make` works.
  1. change `redex/modex/shared.rkt` to update the language grammar
  2. change `redex/model/calculus.rkt` to update the rules.
  3. change `redex/model/standard.rkt` to make corrisponding changes to the std reduction.
  4. update `front-end.rkt` to be able to compile to the new forms
  5. update `redex/test/binding.rkt` to handle correct binding of any new forms
  
  --- If you want to test against external implementation (say you are adding Esterel v7 features) ---
  5. follow below sets of instructions to update Esterel v5 and HipHop.
  --- end if

  --- If you want to test against an updated COS model ---
  6. change `cos-model.rkt` to add the new grammar and semantics
  --- end if

  7. run `raco test` on  all files in `redex/model` and on all files prefixed with `front-end`. this will run the basic tests.
  8. run `raco test` on `redex/test/model-test.rkt`  This will run 
     the tests against the COS, Esterel, and HipHop pass. If you are not
     testing against Esterel and Hiphop, uninstalling either of those will skip that check. If you
     not testing against the COS, Esterel, and Hiphop, skip this step. Any other combination of
     tests against those three will require modifications to `model-test.rkt`.
  9. run `raco test` on `redex/test/binding.rkt` and `redex/test/church-rosser.rkt`. If all of these
     passed, it appears that the redex model works, and has a nonzero probability of being correct.

  10. Update the Agda proofs. See the README there for a sense of which files to modify.
  11. run `make agda` to make sure the proofs work.
  12. update the files in `cross-test/` to generate the new agda code.
  13. run `raco test` on all files in `cross-tests/` to sanity check redex model
      against the agda model.
  14. run `make` to sanity check that everything works.
  15. modify `final-tests/run.rkt` to run the whichever tests you want to run (against COS, agda, Esterel, or HipHop.js).
  16. clear out `final-tests/logs/`
  17. run `final-tests/run.rkt` in as many processes as you want on your favorite multi-core machine.
  18. After you desired Long Amount Of Time has passed, check the logs in `final-tests/logs/` for any test failures.
  

To update Agda to a new version: 
  Assuming you already have agda installed, you will need to
  1. update agda.
  2. update the std library.
  3. update the proofs in `agda/`
  4. change `cross-tests/` redex to agda translator to generate agda code consistent with the new version of agda.
  5. run `make` to make sure everything compiles, type checks, and passes its tests.
  6. run `make paper` to check that the statements in the paper still check out w.r.t the agda proofs.



Update to a new Esterel version:
  Assuming Esterel is already in the `install-prefix/` directory.
  1. replace the esterel with a new esterel version.
  2. update `redex/model/concrete.rkt` to compile redex to the new version
  3. update `redex/test/external.rkt` to handle new CLI interface and possible errors.
  4. run `make` to check new tests.


Update HipHop Version:
  Assuming hiphop, and it dependencies bigloo scheme and hop are already in `install-prefix/`
  1. delete `install-prefix/bigloo`
  2. update `install-bin/install-bigloo.sh` to install the new version
  3. update `install-bin/install-hop.sh` to install the new version.
  4. update the git submodule in `install-prefix/hiphop/` to point to the new version.
  5. run `install-bin/install-bigloo.sh` and  `install-bin/install-hop.sh` in that order.
  6. update `hiphop/parse.rkt` to parse the new hiphop format and test cases.
  7. update `hiphop/pretty-print.rkt` for any changes to the hiphop execution harness
  8. update `hiphop/to-hiphop.rkt` for any changes to the hiphop syntax.
  9. run `make` to test changes
