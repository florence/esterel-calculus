#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt")

@title[#:tag "background" #:style paper-title-style]{Background}

This chapter provides the background material necessary to
understand this dissertation. This chapter is meant as a
refresher on the material, as well as an introduction to the
notation I am going to be using. As such, each section has
recommended reading, which the section is designed as a
refresher for. Readers who are very familiar with the
background work of each area may wish to skim these sections
for the notation I use.

@Secref["background-esterel"] describes the language
Esterel. It is meant as refresher on Chapters 1, 2, 4.1, and
12 of @cite/title[esterel02], as well as chapters 1 and 2 of
@cite/title[compiling-esterel]. Specifically an
understanding of Kernel Esterel and the Constructive
Behavioral Semantics will be helpful. As my dissertation
uses Kernel Esterel, this section only describes that
language. For a description of Full Esterel, please see the
Chapter 1 and 2, and appendix B of
@cite/title[compiling-esterel].


@Secref["background-calculi"] gives background on language
semantics and calculi. It is meant as a refresher to chapters
I.1, I.2, and I.9 of @cite/title[redex-book] and sections
1 and 4 of @cite/title[felleisen-hieb].


@Secref["background-circuits"]
gives a semantics for circuits. It is meant as a refresher
for @cite/title[malik-circuit], @cite/title[shiple-constructive-circuit],
and borrows heavily from chapters 10.1 and 10.3 of @cite/title[esterel02].
The description of circuits here also relies on the theorems
of @cite/title[constructive-boolean-circuits], although that work is in
no way required to understand this dissertation.

@include-section["esterel.scrbl"]
@include-section["calculi.scrbl"]
@include-section["circuits.scrbl"]
