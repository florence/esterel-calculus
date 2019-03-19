beforecommit: redex agda cross front-end

racket-build: always
	raco setup --check-pkg-deps esterel-calculus
	raco make -v **/*.scrbl

front-end: redex
	raco test front-end*rkt

redex: always racket-build
	raco test cos-model.rkt
	./redex/test-short.sh redex

long: redex cross front-end
	raco test redex/test/long-tests/full-test.rkt
	raco test hiphop/run-tests.rkt

# find -s should work on Mac and BSD-machines
agda: always
	! racket agda-all.rkt | grep -v '^[ ]*\(Skipping \)\|\(Checking \)\|\(Finished \)'
	find . -name "*.agda" -exec grep -H -A 1 postulate {} \;
	find . -name "*.agda" -exec grep -H -A 1 trustMe {} \;

cross: redex agda
	raco test cross-tests/*rkt
	racket cross-tests/redex-model-implies-agda-model.rkt


paper: always
	(cd paper ; raco make -v paper.scrbl && scribble --pdf paper.scrbl)
	raco test paper/*rkt paper/*scrbl

no-agda-paper: always
	(cd paper ; raco make -v paper.scrbl && env SKIPAGDA=1 scribble --pdf paper.scrbl)
	raco test paper/*rkt paper/*scrbl

all: agda long

always:
