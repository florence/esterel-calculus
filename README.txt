Usage:

`make agda` will build and typecheck the agda implementation of the Esterel calculus, and all proofs.

To run Install agda version 2.5.2, and the Adga standard library version 0.13.

`make` will build the redex and agda source, run tests against the COS, this calculus, and HipHop and Esterel v5 if the latter two are installed.

Directory Structure:

agda: The agda implementation of the esterel calculus.

redex: The redex implementation of the calculus. To run must be using Racket version 7.0 or later.
       Some of these tests will be skipped because because Esterel V5 is not included here for licensing reasons.

cos-model.rkt : Implementation of the COS semantics in redex

cross-tests: tests that check that the agda and redex models are defining the same calculus

final-tests: test harness and log files for major tests mentioned in the paper.
  logs/agda*.log : logs from the agda/redex cross tests
  logs/internal*.log : logs from the tests between COS and Esterel Calculus only.
  logs/external*.log : logs from the tests between COS, Esterel Calculus,
    Esterel V5, and HipHop. Are test failures here are logged bugs or known differences between the COS semantics and Esterel V5 and HipHop.

front-end.rkt, front-end-tests.rkt, front-end-tester.rkt, front-end-examples: A racket compiler from surfaces esterel to the redex implementaiton of kernel esterel. Used for testing against hiphop.

hiphop: compiler from the redex implementation of kernel esterel to HipHop.js, used for running hiphops tests.

install-prefix: install locations for hiphop.js (and its dependencies bigloo scheme and hop), and Esterel V5 (not included here, as it is not public). install-prefix/bin can be used to install bigloo and hop. hiphop can be installed by initializing the git submodule.
 The README in this folder describes more.

paper: Source for the paper. Must have Racket 7.0.

agda-all.rkt: build harness for running all of the agda code.

cos-model.rkt: redex implementation of the COS.

info.rkt: Racket build file.

