#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt")

@title[#:style paper-title-style]{Background}

This section provides the background material necessary to
understand this dissertation. @Secref["background:esterel"]
describes the language Esterel. You should read this section
if you are unfamiliar with Esterel.
@Secref["background:calculi"] gives background on language
semantics and calculi. You should read this section if you
have not seen language calculi and using them to define a
languages semantics before, especially the treatment given
in @citet[redex-book]. You should skim this section if you
are familiar with these topics to get a sense of the
notation I will be using. @Secref["background:circuits"]
gives a semantics for circuits. You should read this section
if you are not familiar with the formal treatment of
constructive circuits: that is synchronous circuits with
registers and cycles, such as those described in
@citet[malik-circuit] and
@citet[shiple-constructive-circuit], or @citet[esterel02]
and @citet[compiling-esterel]. If you are familiar a brief
skim of this section may help clarify the exact notation I
am using.

@include-section["esterel.scrbl"]
@include-section["calculi.scrbl"]
@include-section["circuits.scrbl"]
