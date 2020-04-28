#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          "lib/misc-figures.rkt"
          "lib/rule-figures.rkt"
          "lib/jf-figures.rkt"
          "lib/cite.rkt"
          (only-in "notations.scrbl")
          (only-in "proofs/proofs.scrbl")
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict
          syntax/parse/define
          esterel-calculus/redex/model/deps
          (for-syntax racket/base)
          pict
          racket/match
          (only-in "lib/circuit-diagrams.rkt" compile-def))


@title[#:style paper-title-style
       #:tag "sec:the-rest"]{Adding in the rest of Esterel}

The tripod of evidence that the calculus stands on includes
prior work and testing, along side the proofs. So far I have
only given one of those legs, the proofs, and only for the
pure, loop free, single instant, fragment of Esterel. This
chapter fills in the parts of the calculus which handle
loops, host language expressions, and multi-instant
execution. It will also give the other two legs of the
tripod: testing and prior work. While the parts of the
calculus given so far stand on all three legs, these new
parts are only supported by testing and prior work.


@section{Loops}

The calculus handles loops with two new administrative rules. However to handle loops
we must add a new form to Kernel Esterel:
@centered[lang/loop]
This new form, @es[loop^stop] represents a loop which has been unrolled once.
To understand its usage, the loop rules are:@(linebreak)
@[render-specific-rules '(loop loop^stop-exit)]@(linebreak)
The first rule, @rule["loop"] expands a
@es[loop] into a @es[loop^stop]. This @es[(loop^stop p q)]
is essentially equivalent to @es[(seq p (loop p))]---that
is, it represent one unrolling of a loop---however, unlike
@es[seq], the second part is inaccessible: if @es[p] reduces
to @es[nothing], the loop cannot restart, instead the
program gets stuck. This handles instantaneous loops,
which are an error in Esterel. The second loop rule,
@rule["loop^stop-exit"], is analogous to @rule["seq-exit"],
aborting the loop if it @es[exit]s.

@subsection{Loops and Can}

@figure["fig:cl" "Can and Loops" Can-loop-pict]

To handle loops we must add two clauses to @es[Can](@figure-ref["fig:cl"]). which just behave as their bodies.
In the case of @es[loop^stop] the right hand side, which is the loops original body,
is not analyzed as it @italic{cannot} be reached in this instant.

@subsection{Loops and Blocked}

As adding loops adds a new evaluation context, the blocked
relation must be extended to handle it, seen in
@figure-ref["fig:lblock"]. This extension treats
@es[loop^stop] the same as @es[seq].

@figure["fig:lblock" "Extending Blocked for Loops" loop-blocked-pict]

@subsection[#:tag "sec:calc:loop:cb"]{Loops and Correct Binding}

We can now turn to the issue of Schizophrenia in the
calculus. Correct binding prevents schizophrenia, because at
their heart schizophrenic variables are variables which have
two instances, and one captures the other! Thus, the loop
clause in @es[CB] (@figure-ref["fig:bl"]) forbids the bound
and free variables of the loop body from overlapping at all.
This way then the loop expands into @es[loop^stop], the
constraint given the corresponding clause (which is the same
as the constraint given for @es[seq]) is preserved,
preventing any variable capture.

@figure["fig:bl" "Correct Binding and Loops" CB-loop-pict]

@subsection[#:tag "sec:calc:loop:eval"]{Loops and the evaluator}

Loops give us another scenario that the evaluator is: instantaneous loops. Instantaneous
loops will always reach a state where they contain a program
fragment which matches @es[(loop^stop nothing q)]. Such a
program has had the loop body terminate in the current
instant, and there is no rule which can reduce this term.
This term is not @es[done], however, because it is not a
complete program state. In addition This program is not
counted as @es[blocked]. This is because if such a program
were to be counted as non-constructive then the definitions
of non-constructive in Esterel would not cleanly match the
definition of non-constructive in circuits, because the
Esterel compiler, as given in chapter 11 of
@citet[esterel02], requires that instantaneous loops be
eliminated statically before compilation, and therefore is
not defined on such programs. Therefore I have chosen to
make @es[eval^esterel] also not defined on such programs.


@subsection{Leaving loops out of the proofs}

There are two reasons I have left loops out of my proofs, and
they all relate to difficulties in stating the theorems correctly.

Firstly there is a subtle difference in how the compiler
and the evaluator handle instantaneous loops. The compiler
requires that all loops be checked statically to ensure
that they can never be instantaneous.
The evaluator, however, is undefined only on programs
that trigger instantaneous loops dynamically. This means that
the evaluator is defined on more programs than the compiler.

The next issue is the issue of schizophrenia. The correct binding
judgment ensures that the calculus never suffers from schizophrenia.
However the compiler requires that programs be transformed to
eliminate possibly schizophrenic variables. The simplest
of these (which is what the random tests do) is to fully
duplicate every loop body. This is not what is done
in practice: in general parts of the program
are selectively duplicated, using methods such as those given by
@citet[new-method-schizophrenic] or chapter 12 of
@citet[esterel02] selectively duplicate only parts of the
program. This however means in practice that the loops
that the compiler operates on look different to those that
the evaluator operates on, in a way that is difficult to formalize.


The handling of in the calculus loops is adapted from the COS, which lends
evidence to its correctness.

Loops are handled by the compiler by duplicating the loop body, in a manner described
by @citet[esterel02]. To see how this works, it is easiest to look at the compilation of
@es[loop^stop], seen in @figure-ref["comp:loop^stop"]. This is essentially the compilation of
@es[seq], except that the output @es[K0] wire is removed (and is therefore @es[0]),
and the @es[K0] wire of @es[q-pure] is or'ed with the @es[GO] wire, restarting the
whole loop when it terminates. From here we can define
@es[(= (compile (loop p-pure)) (compile (loop^stop p-pure p-pure)))]. Note that this
loop compilation assumes that the loop is never instantaneous.

@[begin
   (define (circ-fig n)
     (match-define (list _ _ pict circ) (assoc n compile-def))
     (figure (~a "comp:" n)
             @list{The compilation of @pict}
             circ))
 ]
@circ-fig['loop^stop]
@section[#:tag "sec:full:host"]{Host language rules}

To handle host language forms, @es[θ] and @es[θr] must be extended
to accept shared and host language variables. Thus @es[θ] will
also map @es[x]s to their values, and @es[s]s to a pair
of a value and their current status:
@[centered [with-paper-rewriters [render-language esterel-eval #:nts '(shared-status)]]]

To understand these @es[shared-status]es, observe the rules
for shared variables:@(linebreak)
@[render-specific-rules '(shared set-old set-new)]@(linebreak)
The first rule is analogous to the @rule["signal"] rule,
converting a shared variable binder into a local environment
with the control variable @es[WAIT]. However the rule
@rule["shared"] must evaluate a host language expression to
determine the default value for the shared variable. To do
this it check if every single shared and host language
variable in the host language expression is bound in the
local environment, and that all of the referenced shared
variables cannot be written to, according to
@es/unchecked[(->sh Can-θ)]. Only if this is true can the expression
@es[e] be given to the host language evaluator @es[δ], which
accepts the host language expression and the binding
environment. The new environment initializes
the shared variable's status to @es[old], because the default
value of the shared value acts as if it came from the previous instant
and should only be used if the shared variable is not written to.

The @rule["set-old"] and @rule["set-new"] rules both update the value of a shared variable,
using the same rules as @rule["shared"] to decide if the host language expression
can be evaluated. The difference is in the actual updating. If the status
is @es[old], then the new value replaces the old value, and the status is
set to @es[new]. If the status is already @es[new], then the value
gotten from evaluating @es[e] is combined by the associative and commutative operator
for that variable. In this model the only operator is @es[+], however in a real
program the operator is given by the program itself. Like @rule["emit"], these rules
may only fire when the control variable is @es[GO], for a similar reason as
to @rule["emit"].


Initializing and updating host language variables is
simpler:@(linebreak)
@[render-specific-rules '(var set-var)]@(linebreak)
The initialization of the host language variable via
@rule["var"] is nearly identical to the initialization of
shared variables, the only difference being the type of
variable, and the lack of a status. Updating a host language
variable is also akin to @rule["set-old"], except that
because Esterel doesn't directly provide guarantees about
concurrency with host language variables, the new value just
replaces the old one in the environment.

We can condition on host language variables using the @es[if!0] form:@(linebreak)
@[render-specific-rules '(if-true if-false)]@(linebreak)
Which, for this model, behaves like C's @es[if], treating @es[0] as false
and everything else as true.

Note that these rules assume that host language expressions
@es[e] cannot have side effects which modify the environment
@es[θr]. This is not, in general, true however---for example
in HipHop.js@~cite[hiphop], which is an Esterel
implementation which uses Javascript at its Host Language,
these host language expressions can (and in practice do)
have side effects. In order to handle this the calculus
would need additional reasoning, for example having @es[δ]
return a value and a new environment.

@subsection[#:tag "sec:full:host:can"]{Host language and Can}


@[begin
 (define S (with-paper-rewriters (text "S" (default-style))))
 (define K (with-paper-rewriters (text "K" (default-style))))
 (define sh (with-paper-rewriters (text "sh" (default-style))))]

We must add several clauses to @es[Can] to handle shared variables and host language
expressions(@figure-ref["sec:cs"]). The analysis of the @es[shared] from is like that of
the @es[signal] form, except that there is no special case
for when the shared variable cannot be written to. Because
Esterel does not make control flow decisions based on the
writability of shared variable, there is not need for the
extra step. Writing to a shared variable behaves akin to
emitting a signal: the return code is @es[0] and the variable
is added to the @sh set.

The last three clauses handle host language variables. No special
analysis is done for these forms as Esterel does not link
them into its concurrency mechanism.

@figure["sec:cs" "Can and the Host Language" Can-host-pict]

@subsection{Host language and Blocked}

The @es[blocked] relation must be extended to forms that refer to the host
language in @figure-ref["calc:eval:blocked:host"]. They are
all base cases, and are either blocked because a write to a
shared variable may not be performed due to the control
variable (@rule["set-shared-wait"]), or because a host
language expression is blocked. The blocked judgment for a
host language expression
(@figure-ref["calc:eval:blocked:e"]) says that the
expression may not be evaluated if at least one of the
shared variables that the expression references might still
be written to by the full program.

@figure["calc:eval:blocked:host" "The blocked judgment on terms using the host language" 
         blocked-pict]
@figure["calc:eval:blocked:e" "The blocked judgment host language expressions" 
         blocked-e-pict]

@subsection{Host language and Correct Binding}

The extensions to correct binding for the host language, seen in @figure-ref["fix:bh"], forms are trivial.
They simply require that all subforms have correct binding.

@[figure "fix:bh" "Correct Binding and the host language" CB-host-pict]

@subsection{Leaving the host language out of the proofs}

There are two reasons I have left the host language out of the proofs.
The primary one is that the ground truth semantics I am using
does not include these forms, thus writing proofs
about them would involve extending that semantics in a non-trivial way.
The second reason is that the host language forms
reuse many of the mechanisms from the pure language. Therefore the
proofs about the pure section of the language give some confidence for
the correctness of the host language part.

The handling of shared variables is adapted from the COS, which lends
evidence to its correctness.

@section[#:tag "sec:calc:future"]{Future Instants}

While both the calculus and the evaluator only handle single
instants, we can still describe multiple instants. This is
done via the inter-instant transition metafunction
@es[next-instant]. This relies on the notion of a complete
term:
@centered[[with-paper-rewriters (render-language esterel-eval #:nts '(complete*))]]
which is a term which is either constructive or @es[done].
Such a term is either a program or a fragment of a program
which has finished evaluating for the current instant. The
@es[next-instant] metafunction turns such a term into a term
which will begin execution at the start of the next instant.
The function is defined in @figure-ref["calc:eval:next"].

@figure["calc:eval:next" "The inter-instant transition function" @extract-definition["next-instant"]]

This function walks down the structure of the program
updating it so that it will unpause, if possible. The first
clause uses the metafunction @es[reset-θ], which takes an
environment and sets the status of every signal to
@es[unknown], and the status of every shared variable to
@es[old]. The second clause replaces a @es[pause] with a
@es[nothing], causing execution to resume from that point.

All but two of the remaining clauses simply recur down the
structure of evaluation contexts. The exceptions are
@es[loop^stop] and @es[suspend]. @es[loop^stop] is replaced
by the traditional unfolding of a loop, because in the next
instant the body of the loop that was executing is allowed
to terming, restarting the loop.

The @es[suspend] transformation is more complex. We want a
term which entered a @es[suspend] to pause in that suspend
if the given signal is @es[present] in the next instant.
Therefore we transform an @es[suspend] to do exactly that:
if the signal is @es[present] then @es[pause], otherwise do
nothing and resume executing the loop body.

@subsection{Leaving instants out of the proofs}

I have left instants out of the proofs because of how
@es[Can] is defined in the calculus. The version of @es[Can]
I give here assumes that the top of the program is where
execution will occur, rather than execution starting from
some @es[pause]. However I postulate that the calculus
should still be correct for multi-instant execution. In
addition to the tests, the inter-instant translation
function @es[next-instant] is nearly identical to the same
function from @citet[esterel02]@note{Section 8.3, page 89 of
 the current draft} which as been proven correct@note{
 Specifically, it is proven that, up to bisimilarity, a
 program passed through @es[next-instant] under the
 Constructive Semantics remains the same program with respect
 to the State Semantics.} by Lionel Rieg in Coq.@note{
 Unfortunately, as of the writing of this dissertation this
 work is unpublished.}, but with extensions to handle
@es[loop^stop] and @es[ρ].

@section[#:tag "just:sound:testing"]{Evidence via Testing}

@(require racket/runtime-path racket/system racket/port racket/string racket/format)
@(define-runtime-path loc "../final-tests/logs/")
@(unless (directory-exists? loc)
   (error "could not find final tests logs directory"))
       
            
   
@(define impure-test-count*
   (parameterize ([current-directory loc])
     (define numbers
       (with-output-to-string
         (lambda ()
           (system* (find-executable-path  "bash")
                    "-c"
                    @~a{for x in *ternal*; do grep "running test" $x | tail -1; done | awk '{ print $3 }'}))))
     (apply + (port->list read (open-input-string numbers)))))

@(define circuit-test-count*
   (parameterize ([current-directory loc])
     (define numbers
       (with-output-to-string
         (lambda ()
           (system* (find-executable-path  "bash")
                    "-c"
                    @~a{for x in *circuit*; do grep "running test" $x | tail -1; done | awk '{ print $3 }'}))))
     (apply + (port->list read (open-input-string numbers)))))


@;{@(unless (number? impure-test-count*)
      (error 'arg "expected a test count, got ~a" test-count))}
@;{@(unless (number? circuit-test-count*)
      (error 'arg "expected a test count, got ~a" test-count))}

@(define impure-test-count
   (if impure-test-count*
       (max impure-test-count*
            (* 100000 (floor (/ impure-test-count* 100000))))
       "TODO"))

@(define circuit-test-count
   (if circuit-test-count*
       (max
        circuit-test-count*
        (* 100000 (floor (/ circuit-test-count* 100000))))
       "TODO"))
@(define |Esterel v5| @nonbreaking{Esterel v5})

@(define itemlistheader bold)
   
I have evidence the theorems I have proven hold for the pure language,
and that they should hold for the extensions in this chapter.
This evidence comes in the form of random tests.
To do this, I provide the following:

@itemlist[@item{@itemlistheader{Redex COS model} I built a
           Redex@~cite[redex-book] model of the COS semantics. The semantics is a
           rule-for-rule translation of the COS semantics from @citet[compiling-esterel],
           aside from some minor syntax differences. This provides an executable model
           of the COS semantics.}
          @item{@itemlistheader{Redex calculus model} I have also build
           a Redex model of the calculus. This defines two relations:
           the core relation of the calculus @es[⇀], and a new
           relation @es[⇁] which gives an evaluation strategy for @es[⇀].
           The @es[⇁] relation and the @es[next-instant] function is used to define a
           multi-instant evaluator for Esterel. This evaluator checks at
           every reduction step that the step taken by @es[⇁] is also
           in @es[⇀]. The relation @es[⇁] is given in the appendix A.}

          @item{@itemlistheader{Racket Frontend} The actual
           execution of this Redex model of the calculus is embedded
           into Racket, and therefore may use Racket expression as its
           host language expressions, in addition to the numeric
           language the calculus comes equipped with. There is also a
           Racket frontend compiler which compiles Full Esterel into
           the Kernel used by the Redex model with the extensions to
           use Racket as its host language.}
           
          @item{@itemlistheader{Redex/Hiphop.js bridge} 
           HipHop.js is an Esterel implementation embedded into Javascript. We
           built a library that can translate Redex expressions into
           Hiphop.js@~cite[hiphop] programs and then evaluate them.@note{Special thanks to Jesse Tov
           for helping out with this.}
           There is also a
           compiler form a subset of Hiphop.js to the Redex model of the calculus,
           allowing many of the Hiphop.js tests be run directly against the calculus. This translator does not accept
           all Hiphop.js programs, because Hiphop.js programs embed
           JavaScript code as the Redex model cannot evaluate the
           JavaScript.}
          @item{@itemlistheader{Redex/@|Esterel\ v5| bridge}
           There is also built a translator that produces @|Esterel\ v5| programs
           from Redex terms.}
          @item{@itemlistheader{Redex circuit compiler}
           Finally I have built a compiler from pure Esterel (with loops)
           to circuits, which runs on top of the circuit library Circuitous.}]


I have run @(~a impure-test-count) random tests which on Full
Esterel programs with loops which test that the Hiphop.js,
@|Esterel\ v5|, the COS, the calculus, and the circuit
compiler agree on the result of running programs for
multiple instants.@note{Each test runs for a random number
 of instants.} These tests are to provide evidence for consistency and
adequacy, not just against the circuit semantics but against
real implementations as well. The real implementations are
important because they accept Esterel terms that use host
language expressions, which the circuit compiler does not.
Therefore these tests in particular give evidence that
adequacy holds in the presence of Full Esterel. Whenever the generate
program contains host language variables or is not guaranteed to
be loop safe the direct circuit compiler is skipped.

In addition I have run @(~a circuit-test-count) random tests
which generate a random pure program (with loops), and apply
all rules from the calculus (specifically from @es[⟶], the
compatible closure of @es[⇀]), and then check that the
circuits are equal using the Circuitous library. These
tests provide evidence for soundness, and especially for the
soundness with loops.