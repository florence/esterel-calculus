LOGLEVEL = error
RACO_PATH =
RACO = $(RACO_PATH)raco


beforecommit: circuits redex dissertation-tex front-end agda cross

racket-build: always
	$(RACO) setup --check-pkg-deps esterel-calculus
	$(RACO) make -v **/*.scrbl

front-end: redex
	$(RACO) test front-end*rkt

cross: redex agda
	$(RACO) test cross-tests/*rkt
	$(RACO) test cross-tests/redex-model-implies-agda-model.rkt

circuits: always racket-build
	$(RACO) test circuits

redex: always racket-build circuits 
	$(RACO) test redex/cos/model.rkt
	$(RACO) test redex/cos/test/main.rkt
	$(RACO) test redex/model
	$(RACO) test redex/test/*rkt

long: redex cross front-end
	$(RACO) test redex/test/long-tests/full-test.rkt
	$(RACO) test hiphop/run-tests.rkt

agda: always
	! racket agda-all.rkt | grep -v '^[ ]*\(Skipping \)\|\(Checking \)\|\(Finished \)'
	find . -name "*.agda" -exec grep -H -A 1 postulate {} \;
	find . -name "*.agda" -exec grep -H -A 1 trustMe {} \;

all: agda long

dissertation: always
	cd dissertation; $(RACO) make -v lib/redex-rewrite-dynamic.rkt dissertation.scrbl
	cd dissertation; PLTSTDERR="${PLTSTDERR} $(LOGLEVEL) warning@diss" $(RACO) scribble --pdf dissertation.scrbl


dissertation-tex: always
	cd dissertation; $(RACO) make -v lib/redex-rewrite-dynamic.rkt dissertation.scrbl
	cd dissertation; PLTSTDERR="${PLTSTDERR} $(LOGLEVEL) warning@diss" $(RACO) scribble --latex --dest tex dissertation.scrbl

always:
