#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          "../proofs/proofs.scrbl")

@title[#:style paper-title-style]{Justifying the Calculus}

@section{The Main Properties}

Syntactic
Local
Sound
Expressive

Consistent

@section{Proving Soundness}

@subsection{the compiler}

@subsection[#:tag "soundness-of-calc"]{proof technique}

@proof-splice["soundness"]
rosette?


@section{Proving Adequacy}

@proof-splice["comp-ad"]

@subsection{proof sketches}

@section{Putting it together}