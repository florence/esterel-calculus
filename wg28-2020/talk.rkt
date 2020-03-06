#lang racket
(require slideshow "examples.rkt" "aterm.rkt")

(example+label example1-syntax-intro-aterm "Esterel Syntax, i")
(example+label example2-syntax-intro-aterm "Esterel Syntax, ii")
(example+label example3-deterministic-parallelism-aterm "Deterministic Parallelism")
(example+label example4-circularity-non-recative-aterm "Nonreactive")
(example+label example5-circularity-non-deterministic-aterm "Nondeterministic")
(example+label example6-circularity-non-constructive-aterm "Nonconstructive")

(add-title (vl-append 20
                      (aterm->pict (aterm (seq p q)))
                      (aterm->pict (aterm (present S p q))))
           "Happens Before")

(example1-fingers)
(example3-fingers)
(constructive-cycle-example)
(nonconstructive-cycle-example)
(constructive/nonconstructive-cycle-with-cycle-shown)
