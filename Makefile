loglevel = error
beforecommit: circuits redex dissertation front-end

racket-build: always
	raco setup --check-pkg-deps esterel-calculus
	raco make -v **/*.scrbl

front-end: redex
	raco test front-end*rkt

circuits: always racket-build
	raco test circuits

redex: always racket-build circuits 
	raco test redex/cos/model.rkt
	raco test redex/cos/test/main.rkt
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

dissertation: always
	(cd dissertation; raco make -v dissertation.scrbl lib/redex-rewrite-dynamic.rkt && PLTSTDERR="${PLTSTDERR} $(loglevel) warning@diss" scribble --pdf dissertation.scrbl)


dissertation-debug-tex: always
	(cd dissertation; raco make -v dissertation.scrbl lib/redex-rewrite-dynamic.rkt && scribble --latex --dest tex dissertation.scrbl)

 

always:
