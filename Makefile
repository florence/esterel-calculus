LOGLEVEL = error
RACO_PATH =
RACO = $(RACO_PATH)raco


beforecommit: circuits redex dissertation front-end

racket-build: always
	$(RACO) setup --check-pkg-deps esterel-calculus
	$(RACO) make -v **/*.scrbl

front-end: redex
	$(RACO) test front-end*rkt

circuits: always racket-build
	$(RACO) test circuits

redex: always racket-build circuits 
	$(RACO) test redex/cos/model.rkt
	$(RACO) test redex/cos/test/main.rkt
	./redex/test-short.sh redex

long: redex cross front-end
	$(RACO) test redex/test/long-tests/full-test.rkt
	$(RACO) test hiphop/run-tests.rkt

agda: always
	! racket agda-all.rkt | grep -v '^[ ]*\(Skipping \)\|\(Checking \)\|\(Finished \)'
	find . -name "*.agda" -exec grep -H -A 1 postulate {} \;
	find . -name "*.agda" -exec grep -H -A 1 trustMe {} \;

cross: redex agda
	$(RACO) test cross-tests/*rkt
	racket cross-tests/redex-model-implies-agda-model.rkt


paper: always
	(cd paper ; $(RACO) make -v paper.scrbl && SCRIBBLE --pdf paper.scrbl)
	$(RACO) test paper/*rkt paper/*scrbl

no-agda-paper: always
	cd paper ; $(RACO) make -v paper.scrbl && env SKIPAGDA=1 SCRIBBLE --pdf paper.scrbl
	$(RACO) test paper/*rkt paper/*scrbl

all: agda long

dissertation: always
	cd dissertation; $(RACO) make -v dissertation.scrbl lib/redex-rewrite-dynamic.rkt
	cd dissertation; PLTSTDERR="${PLTSTDERR} $(LOGLEVEL) warning@diss" $(RACO) scribble --pdf dissertation.scrbl


dissertation-debug-tex: always
	cd dissertation; $(RACO) make -v dissertation.scrbl lib/redex-rewrite-dynamic.rkt
	cd dissertation; $(RACO) scribble --latex --dest tex dissertation.scrbl

always:
