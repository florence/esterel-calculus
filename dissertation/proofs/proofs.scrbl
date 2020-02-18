#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Proofs}


@include-section["top.scrbl"]
@include-section["soundness.scrbl"]
@include-section["reduction.scrbl"]
@include-section["adequacy.scrbl"]
@include-section["can.scrbl"]
@include-section["circuit-props.scrbl"]