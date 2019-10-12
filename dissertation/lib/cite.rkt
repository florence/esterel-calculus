#lang racket

(require scriblib/autobib)

(provide (except-out (all-defined-out) |Robert de Simone|))

(define |Robert de Simone| (author-name "Robert" "de Simone"))

(define-cite ~cite citet generate-bibliography)

(define plt-tr1
  (make-bib
   #:title    "Reference: Racket"
   #:author   (authors "Matthew Flatt" "PLT")
   #:date     "2010"
   #:location (techrpt-location #:institution "PLT Inc."
                                #:number "PLT-TR-2010-1")
   #:url      "http://racket-lang.org/tr1/"))


(define hiphop
  (make-bib
   #:title "HipHop: A Synchronous Reactive Extension for Hop"
   #:author (authors "Gérard Berry" "Cyprien Nicolas" "Manuel Serrano")
   #:date 2011
   #:location (proceedings-location "PLASTIC")))

(define bigloo
  (make-bib
   #:title "Bigloo: a portable and optimizing compiler for strict functional languages"
   #:author (authors "Manuel Serrano" "Pierre Weis")
   #:date 1995
   #:location (proceedings-location "Static Analysis Symposium")))

(define optimizations-for-esterel-programs-thesis
  (make-bib
   #:title "Optimizations for Faster Simulation of Esterel Programs"
   #:author (authors "Dumitru Potop-Butucaru")
   #:date 2002
   #:location (dissertation-location #:institution "Ecole des Mines de Paris")))

(define pop-pl
  (make-bib
   #:title "POP-PL: A Patient-Oriented Prescription Programming Language"
   #:author (authors "Spencer P. Florence"
                     "Burke Fetscher"
                     "Matthew Flatt"
                     "William H. Temps"
                     "Tina Kiguradze"
                     "Dennis P. West"
                     "Charlotte Niznik"
                     "Paul R. Yarnold"
                     "Robert Bruce Findler"
                     "Steven M. Belknap")
   #:date 2015
   #:location (proceedings-location "GPCE")))

(define compiling-esterel
  (make-bib
   #:title "Compiling Esterel"
   #:author (authors "Dumitru Potop-Butucaru" "Stephen A. Edwards" "Gérard Berry")
   #:date 2007
   #:location (book-location #:publisher "Springer")))

(define tapl-title "Types and Programming Languages")
(define tapl
  (make-bib
   #:title tapl-title
   #:author "Benjamin Pierce"
   #:date 2002
   #:location (book-location #:publisher "MIT Press")))

(define esterel92
  (make-bib
    #:title "The Esterel Synchronous Programming Language: Design, Semantics, Implementation"
    #:author (authors "Gérard Berry" "Georges Gonthier")
    #:date 1992
    #:location (journal-location "Science of Computer Programming"
                                 #:pages (list 87 152)
                                 #:number 2
                                 #:volume 19)))

(define esterel02
  (make-bib
    #:title "The Constructive Semantics of Pure Esterel (Draft Version 3)"
    #:author "Gérard Berry"
    #:date 2002))

(define tardieu-deterministic
  (make-bib
    #:title "A Deterministic Logical Semantics for Pure Esterel"
    #:author "Olivier Tardieu"
    #:date 2007
    #:location (journal-location "ACM Transactions on Programming Languages and Systems"
                                 #:number 2
                                 #:volume 29)))

(define felleisen-hieb
  (make-bib
    #:title "The revised report on the syntactic theories of sequential control and state."
    #:author (authors "Matthias Felleisen" "Robert Hieb")
    #:date 1992
    #:location (journal-location "Theoretical Computer Science"
                                 #:number 2
                                 #:volume 103
                                 #:pages (list 235 271))))

(define plotkin
  (make-bib
   #:title "Call-by-name, Call-by-value, and the λ-Calculus"
   #:author "Gordon Plotkin"
   #:date 1975
   #:location (journal-location
               "Theoretical Computer Science"
               #:volume 1
               #:number 2
               #:pages (list 125 159))))

(define esterel-v5
  (make-bib
   #:title "The Esterel v5 Language Primer Version v5_91"
   #:author "Gérard Berry"
   #:date 2000
   #:location (book-location
               #:publisher "École des Mines de Paris, CMA and INRIA, Sophia-Antipolis, France")))

(define csmith
  (make-bib
   #:title "Finding and Understanding Bugs in C Compilers"
   #:author (authors "Xuejun Yang" "Yang Chen" "Eric Eide" "John Regehr")
   #:date 2011
   #:location (proceedings-location "Programming Language Design and Implementation (PLDI)")))

(define new-method-schizophrenic
  (make-bib
   #:title "A New Method for Compiling Schizophrenic Synchronous Programs"
   #:author (authors "Klaus Schneider" "Michael Wenz")
   #:location
   (proceedings-location
    "International Conference on Compilers, Architecture, and Synthesis for Embedded Systems (CASES)")
   #:date 2001))

(define synchronous-approach
  (make-bib
   #:title "The Synchronous Approach to Reactive and Real-Time Systems"
   #:author (authors "Albert Benveniste" "Gérard Berry")
   #:date 1991
   #:location (journal-location "Proceedings of the IEEE"
                                #:volume 79 #:number 9)))

(define twelve-years-later
  (make-bib
   #:title "The Synchronous Languages 12 Years Later"
   #:author (authors "Albert Benveniste" "Paul Caspi" "Stephen A. Edwards"
                     "Nicolas Halbwachs" "Paul Le Guernic" |Robert de Simone|)
   #:date 2002
   #:location (journal-location "Proceedings of the IEEE" #:volume 91 #:number 1)))

(define espiau-robotics
  (make-bib
   #:title "A Synchronous Approach for Control Sequencing in Robotics Application"
   #:author (authors "Bernard Espiau" "Eve Coste-Maniére")
   #:date 1990
   #:location (proceedings-location "IEEE International Workshop on Intelligent Motion Control")))

(define redex-book
  (make-bib
   #:title "Semantics Engineering with PLT Redex"
   #:author (authors "Matthias Felleisen" "Robert Bruce Findler" "Matthew Flatt")
   #:date 2009
   #:location (book-location #:publisher "MIT Press")))

(define esterel-avionics
  (make-bib
   #:title "ESTEREL: A Formal Method Applied to Avionic Software Development"
   #:author (authors "Gérard Berry" "Amar Bouali" "Xavier Fornari"
                     "Emmanuel Ledinot" "Eric Nassor" |Robert de Simone|)
   #:date 2000
   #:location (journal-location "Science of Computer Programming"
                                #:volume 36
                                #:number 1
                                #:pages (list 5 25))))

(define constructive-boolean-circuits
  (make-bib
   #:title "Constructive Boolean circuits and the exactness of timed ternary simulation"
   #:author (authors "Michael Mendler" "Thomas R. Shiple" "Gérard Berry")
   #:date 2012
   #:location (journal-location "Formal Methods in System Design"
                                #:volume 40
                                #:pages (list 283 329))))


(define barendregt
  (make-bib
   #:author "H. Barendregt"
   #:title "The Lambda Calculus: its Syntax and Semantics"
   #:date 1984
   #:location (book-location #:publisher "North Holland")))

(define lvars
  (make-bib
   #:title "LVars: lattice-based data structures for deterministic parallelism"
   #:author (authors "Lindsey Kuper" "Ryan R. Newton")
   #:date 2013
   #:location (proceedings-location "Workshop on Functional High-performance Computing (FHPC)")))
