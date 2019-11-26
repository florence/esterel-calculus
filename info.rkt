#lang info

(define deps '("circuitous-lib"
               "plot-lib"
               "scribble-abbrevs"
               "ppict"
               "rackunit-abbrevs"
               "base"
               "at-exp-lib"
               "parser-tools-lib"
               "pict-lib"
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
               "diagrama-lib"))

(define collection "esterel-calculus")
(define build-deps '("debug"))
