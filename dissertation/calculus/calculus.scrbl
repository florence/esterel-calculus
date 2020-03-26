#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          "../lib/misc-figures.rkt"
          "../lib/rule-figures.rkt"
          "../lib/jf-figures.rkt"
          "../lib/cite.rkt"
          (only-in "../notations.scrbl")
          (only-in "../proofs/proofs.scrbl")
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict
          syntax/parse/define
          esterel-calculus/redex/model/deps
          (for-syntax racket/base)
          pict)

@(define-simple-macro (code+graph {~alt
 {~optional {~seq #:ignore-start? qq}}
 {~once e}} ...)
   (with-bar (es e) (flow/pict 'e #:ignore-start? (~? qq #t))))


@(define (with-bar p1 p2)
   (hc-append
    p1
    (vline 30 (max (pict-height p1) (pict-height p2)))
    p2))

@title[#:style paper-title-style
       #:tag "sec:calculus"]{A Calculus for Esterel}







