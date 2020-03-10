#lang info

(define deps '("https://github.com/florence/circuitous.git?path=circuitous-lib"
               "plot-lib"
               "scribble-abbrevs"
               "ppict"
               "rackunit-abbrevs"
               "base"
               "at-exp-lib"
               "parser-tools-lib"
               "https://github.com/florence/pict.git?path=pict-lib#diss"
               "redex-lib"
               "redex-gui-lib"
               ["redex-pict-lib" #:version "1.7"]
               "gui-lib"
               "slideshow-lib"
               "sandbox-lib"
               "unstable-lib"
               "rackunit-lib"
               "draw-lib"
               "scribble-lib"
               "pict-snip-lib"
               "html-parsing"
	       "rosette"
               "https://github.com/florence/diagrama.git?path=diagrama-lib"))

(define collection "esterel-calculus")
(define build-deps '("debug"))
