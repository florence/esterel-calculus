#lang racket

(require scriblib/autobib
         rackunit
         (only-in scribble/base italic))

(provide (except-out (all-defined-out) |Robert de Simone|))

(define |Robert de Simone| (author-name "Robert" "de Simone"))
(define gerard "Gérard Berry")

(require/expose
 scriblib/autobib
 [auto-bib-title])

(define-cite ~cite citet generate-bibliography)

(define (cite/title x)
  (list (italic (auto-bib-title x))
        (~cite x)))

(define plt-tr1
  (make-bib
   #:title    "Reference: Racket"
   #:author   (authors "Matthew Flatt" "PLT")
   #:date     "2010"
   #:location (techrpt-location #:institution "PLT Inc."
                                #:number "PLT-TR-2010-1")
   #:url      "http://racket-lang.org/tr1/"))

(define bishop
  (make-bib
   #:title "Schizophrenia in Contemporary Mathmatics"
   #:author "Errett Bishop"
   #:date 1973
   #:location (book-location #:publisher "American Mathematical Society")
   #:url "http://prl.ccs.neu.edu/img/sicm.pdf"))


(define hiphop
  (make-bib
   #:title "HipHop: A Synchronous Reactive Extension for Hop"
   #:author (authors "Gérard Berry" "Cyprien Nicolas" "Manuel Serrano")
   #:date 2011
   #:location (proceedings-location "PLASTIC")))

(define bigloo
  (make-bib
   #:title "Bigloo: A Portable and Optimizing Compiler for Strict Functional Languages"
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

(define esterel84
  (make-bib
    #:title "The ESTEREL Synchronous Programming Language and its Mathematical Semantics"
    #:author (authors "Gérard Berry" "Laurent Cosserat")
    #:date 1992
    #:location (proceedings-location "International Conference on Concurrency")))

(define esterel92
  (make-bib
    #:title "The Esterel Synchronous Programming Language: Design, Semantics, Implementation"
    #:author (authors "Gérard Berry" "Georges Gonthier")
    #:date 1992
    #:location (journal-location "Science of Computer Programming"
                                 #:pages (list 87 152)
                                 #:number 2
                                 #:volume 19)))


(define esterel-state-machine-semantics2
  (make-bib
   #:title "The Semantics of Pure Esterel"
   #:author "Gérard Berry"
   #:date 1993
   #:location (proceedings-location "Program Design Calculi")))

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

(define morris
  (make-bib
   #:title "Lambda-Calculus Models of Programming Languages"
   #:author "James Hiram Morris"
   #:date 1963
   #:location (dissertation-location #:institution "Massachusetts Institute of Technology")))

(define curry-feys
  (make-bib
   #:title "Combinatory Logic I"
   #:author (authors "Haskell B. Curry" "Robert Feys")
   #:date 1958
   #:location (book-location #:publisher "North-Holland Publishing Company, Amsterdam")))

(define felleisen-hieb
  (make-bib
    #:title "The Revised Report on the Syntactic Theories of Sequential Control and State"
    #:author (authors "Matthias Felleisen" "Robert Hieb")
    #:date 1992
    #:location (journal-location "Theoretical Computer Science"
                                 #:number 2
                                 #:volume 103
                                 #:pages (list 235 271))))

(define felleisen-friedman
  (make-bib
   #:title "Control Operators, the SECD-machine, and the λ-calculus"
   #:author (authors "Matthias Felleisen" "Daniel P. Friedman")
   #:date 1986
   #:location (proceedings-location
               "Conference on Formal Descriptions of Programming Concepts Part III")))

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

(define ISWIM
  (make-bib
   #:title "The Mechanical Evaluation of Expressions"
   #:author "Peter J. Landin"
   #:location
   (journal-location "Computer Journal"
                     #:volume 6
                     #:number 4)
   #:date 1964))

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

(define quartz
  (make-bib
   #:title "Embedding Imperative Synchronous Languages in Interactive Theorem Provers"
   #:author "Klaus Schneider"
   #:date 2001
   #:location
   (proceedings-location
               "Second International Conference on Application of Concurrency to System Design (ACSD)")))

(define HOL
  (make-bib
   #:title "Introduction to HOL: A Theorem Proving Environment for Higher Order Logic"
   #:date 1993
   #:author (authors " Michael J C Gordon" " Tom F Melham")
   #:location (book-location #:publisher "Cambridge University Press")))

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
   #:title "Constructive Boolean Circuits and the Exactness of Timed Ternary Simulation"
   #:author (authors "Michael Mendler" "Thomas R. Shiple" "Gérard Berry")
   #:date 2012
   #:location (journal-location "Formal Methods in System Design"
                                #:volume 40
                                #:pages (list 283 329))))

(define mendler-2012 constructive-boolean-circuits)

(define shiple-constructive-circuit
  (make-bib
   #:title "Constructive Analysis of Cycle Circuits"
   #:author (authors "Thomas R. Shiple" gerard "Hervé Touati")
   #:date 1996
   #:location (proceedings-location
               "European design and test conference")))


(define barendregt
  (make-bib
   #:author "H. Barendregt"
   #:title "The Lambda Calculus: its Syntax and Semantics"
   #:date 1984
   #:location (book-location #:publisher "North Holland")))

(define lvars
  (make-bib
   #:title "LVars: Lattice-Based Data Structures for Deterministic Parallelism"
   #:author (authors "Lindsey Kuper" "Ryan R. Newton")
   #:date 2013
   #:location (proceedings-location "Workshop on Functional High-performance Computing (FHPC)")))

(define florence-2019
  (make-bib
   #:title "A Calculus for Esterel"
   #:author (authors "Spencer P. Florence"
                     "Shu-Hung You"
                     "Jesse A. Tov"
                     "Robert Bruce Findler")
   #:date 2019
   #:location (journal-location
               "Proceedings of the ACM on Programming Languages"
               #:volume 3
               #:number "POPL")))


#|
Note about the completeness result here:
Theorem 47. Given constructive Esterel statements E and E′;
 E=E′ if and only if E≈E′.
|#
(define tini-axiomatic
  (make-bib
   #:title "An Axiomatic Semantics for Esterel"
   #:author "Simone Tini"
   #:date 2001
   #:location
   (journal-location
    "Theoretical Computer Science"
    #:volume 296
    #:pages (list 231 282))))


(define pdg
  (make-bib
   #:title "The Program Dependence Graph and Its Use In Optimization"
   #:author (authors "Jeane Ferrante" "Karl J. Ottenstein" "Joe D. Warren")
   #:date 1987
   #:location (journal-location
               "ACM Transactions on Programming Languages and Systems (TOPLAS)"
               #:volume 9
               #:number 6
               #:pages (list 319 349))))

(define zeng-cec
  (make-bib
   #:title "Generating Fast Code from Concurrent Program Dependence Graphs"
   #:author (authors "Jia Zeng" "Cristian Soviani" "Stephan A. Edwards")
   #:date 2004
   #:location (proceedings-location
               "Languages, Compilers, Tools and Theory of Embedded Systems (LCTES)")))


(define optimization-coaching
  (make-bib
   #:title "Optimization Coaching: Optimizers Learn to Communicate with Programmers"
   #:author (authors "Vincent St-Amour" "Same Tobin-Hochstadt" "Matthias Felleisen")
   #:date 2012
   #:location (proceedings-location "ACM international conference on Object oriented programming systems languages and applications (OOPSLA)")))


(define CRP
  (make-bib
   #:title "Communicating Reactive Processes"
   #:author (authors gerard "S. Ramesh" "Rudrapatna K. Shyamasundar")
   #:date 1993
   #:location (proceedings-location "ACM Symposium on Principles of Programming Languages (POPL)")))


(define malik-circuit
  (make-bib
   #:title "Analysis of Cyclic Combinational Circuits"
   #:author "Sharad Malik"
   #:date 1994
   #:location (journal-location "IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems"
                                #:volume 13
                                #:number 7)))

(define bryant-MOS
  (make-bib
   #:title "Boolean Analysis of MOS Circuits"
   #:author "Randal E. Bryant"
   #:date 1987
   #:location
   (journal-location "IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems"
                     #:volume 6
                     #:number 4)))

(define linking-types
  (make-bib
   #:title "Linking Types for Multi-Language Software: Have Your Cake and Eat It Too"
   #:author (authors "Daniel Patterson" "Amal Ahmed")
   #:date 2017
   #:location (proceedings-location "2nd Summit on Advances in Programming Languages (SNAPL)")))

(define rosette
  (make-bib
   #:title "Growing Solver-Aided Languages with ROSETTE"
   #:author (authors "Emina Torlak" "Rastislav Bodik")
   #:date 2013
   #:location (proceedings-location "Onward!")))

(define felleisen-expressive
  (make-bib
   #:title "On the Expressive Power of Programming Languages"
   #:author "Matthias Felleisen"
   #:date 1991
   #:location (proceedings-location
               "European Symposium on Programming")))

(define unit-cite
  (make-bib
   #:title "Units: Cool Modules for HOT Languages"
   #:author (authors "Matthew Flatt" "Matthias Felleisen")
   #:date 1998
   #:location (proceedings-location
               "Programming Language Design and Implementation (PLDI)")))

#|
bohm alcune proprietà delle forme normali nel calcolo
|#