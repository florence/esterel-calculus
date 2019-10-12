#lang scribble/acmart @acmsmall

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/test/generator)

@title[#:style paper-title-style]{A Calculus for Esterel}

@include-section["proofs.scrbl"]