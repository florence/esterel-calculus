#lang racket

(require esterel-calculus/front-end-tester)

(test-case "basic awaits"
  (define-esterel-machine m1
    #:inputs ()
    #:outputs ()
    (signal&
     S
     (par&
      (loop& pause& (emit& S))
      (await& 5 S))))
  (test-seq m1
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())))

(test-case "await"
  (define-esterel-machine m1
    #:inputs (A)
    #:outputs (O)
    (loop&
     (await& A)
     (emit& O)
     pause&))
  (test-seq m1
            ((A) => ())
            ((A) => (O))
            ((A) => ())
            ((A) => (O))))

(test-case "await-immediate"
  (define-esterel-machine m1
    #:inputs (A)
    #:outputs (O)
    (loop&
     (await-immediate& A)
     (emit& O)
     pause&))
  (test-seq m1
            ((A) => (O))
            ((A) => (O))
            ((A) => (O))
            ((A) => (O))))

(test-case "awaits+trap"
  (define-esterel-machine m1
    #:inputs (S)
    #:outputs ()
    (signal&
     S
     (trap& T
            (par&
             (loop& pause& (emit& S))
             (seq& (await& 5 S) (exit& T))))))
  (test-seq m1
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())))

(test-case "loop+par+trap+await"
  (define-esterel-machine m1
    #:inputs ()
    #:outputs ()
    (signal&
     (theraputic hour 4-hour check-aptt)
     (par&
      (loop& pause& (emit& hour))
      (loop& pause& pause& pause& pause& (emit& 4-hour))
      (loop&
       (trap& checking
              (par& (seq& (await& check-aptt) (exit& checking))
                    (every& hour
                            (present& theraputic nothing& (emit& check-aptt)))
                    (every& 4-hour
                            (present& theraputic (emit& check-aptt)))))))))
  (test-seq m1
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())
            (() => ())))

(test-case "every"
  (define-esterel-machine m1
    #:inputs (A)
    #:outputs (O)
    (every& A (emit& O)))
  (test-seq m1
            ((A) => ())
            ((A) => (O))
            (()  => ())
            ((A) => (O))
            (()  => ())))

(test-case "repeat-exp"
  (define-esterel-machine MODULE0 #:inputs () #:outputs (O)
    (seq& (var& x := 2 (trap& T (loop& (if& (> (get-var x) 0) (seq& (:=& x (- (get-var x) 1)) pause&) (exit& T)))))
          (emit& O)))
  (test-seq
   MODULE0
   (() => ())
   (() => ())
   (() => (O))))

(test-case
  "repeat-count0"
  (define-esterel-machine MODULE0 #:inputs () #:outputs (O) (seq& (repeat& 2 pause&) (emit& O)))
  ;(pretty-print (machine-prog MODULE0))
  (test-seq
   MODULE0
   (() => ())
   (() => ())
   (() => (O))))

(test-case
  "await-count0"
  (define-esterel-machine MODULE0 #:inputs (I) #:outputs (O) (seq& (await& 3 I) (emit& O)))
  ;(pretty-print (machine-prog MODULE0))
  (test-seq
   MODULE0
   (() => ())
   ((I) => ())
   (() => ())
   ((I) => ())
   ((I) => (O))))

(test-case
  "await-count"
  (define-esterel-machine MODULE0 #:inputs (I) #:outputs (O) (seq& (loop& (await& 3 I) (emit& O))))
  ;(pretty-print (machine-prog MODULE0))
  (test-seq
   MODULE0
   (() => ())
   ((I) => ())
   (() => ())
   ((I) => ())
   ((I) => (O))
   (() => ())
   (() => ())
   (() => ())
   ((I) => ())
   ((I) => ())
   ((I) => (O))
   (() => ())
   (() => ())
   ((I) => ())
   ((I) => ())
   ((I) => (O))
   ((I) => ())
   (() => ())
   (() => ())
   (() => ())
   ((I) => ())
   ((I) => (O))))

(test-case "every"
  (define-esterel-machine m1
    #:inputs (A)
    #:outputs (O)
    (every& A (emit& O)))
  (test-seq m1
            ((A) => ())
            ((A) => (O))
            (()  => ())
            ((A) => (O))
            (()  => ())))

(test-case "every-immediate"
  (define-esterel-machine m1
    #:inputs (A)
    #:outputs (O)
    (every-immediate& A (emit& O)))
  (test-seq m1
            ((A) => (O))
            (() => ())
            (() => ())
            ((A) => (O))
            (() => ())))

(test-case "weak-abort"
  (define-esterel-machine m1
    #:inputs (S)
    #:outputs (O F W)
    (seq&
     (weak-abort& S (loop& (emit& O) pause& (emit& W)))
     (emit& F)))
  (test-seq m1
            (() => (O))
            (() => (O W))
            ((S) => (O F W))
            (() => ())))


(test-case "weak-abort-immediate"
  (define-esterel-machine m1
    #:inputs (S)
    #:outputs (O F W)
    (seq&
     (weak-abort-immediate& S (loop& (emit& O) pause& (emit& W)))
     (emit& F)))
  (test-seq m1
            ((S) => (O F))
            (() => ())))

(test-case "weak-abort-immediate 2"
  (define-esterel-machine m1
    #:inputs (S)
    #:outputs (O F W)
    (seq&
     (weak-abort-immediate& S (loop& (emit& O) pause& (emit& W)))
     (emit& F)))
  (test-seq m1
            (() => (O))
            (() => (O W))
            ((S) => (O F W))
            (() => ())))

(test-case "run2 tests"
  (define-esterel-machine m1
    #:inputs ()
    #:outputs ()
    #:input/outputs (s u w z)
    (par&
     (present& s (seq& (emit& w)) nothing&)
     (present& u (seq& (emit& z)) nothing&)))
  (define-esterel-machine run2
    #:inputs (s u)
    #:outputs ()
    #:input/outputs (a b)
    (loop&
       (run& m1 [s -> s] [u -> u] [a -> w] [b -> z])
     pause&))
  (test-seq
   run2
   [() => ()]
   [(s) => (a)]
   [(a) => (a)]))

(test-case "basic causality error"
  (define-esterel-machine broke
    #:inputs ()
    #:outputs ()
    (signal& S
      pause&
      pause&
      (present& S (emit& S))))
  (test-seq
   broke
   [() => ()]
   [() => ()]
   [() => #:causality-error]))
