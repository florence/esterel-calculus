#lang racket
(require redex/reduction-semantics
         rackunit
         esterel-calculus/redex/cos/model
         esterel-calculus/redex/cos/test/harness)

(test-equal
 `(nat= two one)
 #f)
(test-equal
 `(nat= one two)
 #f)

(test-case "grammar"
  (check-true
   (redex-match? esterel (exit k) `(exit zero)))
  (check-true
   (redex-match? esterel (exit k) `(exit one)))
  (check-true
   (redex-match? esterel (exit k) `(exit two)))
  (check-true
   (redex-match? esterel (exit k) `(exit (Succ (Succ zero)))))
  (check-true
   (redex-match? esterel (exit k) `(exit three))))

(test-case "eval grammar"
  (check-true
   (redex-match? esterel-eval l `one))
  (check-true
   (redex-match? esterel-eval sstat `one))
  (check-true
   (redex-match? esterel-eval E `((S one))))
  (check-true
   (redex-match? esterel-eval (E K V) `(((S one)) (zero) ()))))

(test-case "basic eval"
  (test-case "1"
    (parameterize ([current-traced-metafunctions '(→)])
      (test-equal (do `(· nothing))
                  `((nothing ⊥ zero ())))))
  (test-case "2"
    (test-equal (do `(· pause))
                `(((hat pause) ⊥ one ()))))
  (test-case "3"
    (test-equal (do `(· (hat pause)))
                `((pause ⊥ zero ()))))
  (test-case "4"
    (test-equal
     (do `(· (seq pause pause)))
     `(((seq (· pause) pause) ⊥ ⊥ ())))
    (test-equal
     (do `(· (seq (hat pause) pause)))
     `(((seq (· (hat pause)) pause) ⊥ ⊥ ()))))
  (test-case "5"
    (test-equal
     (do `(seq (· (hat pause)) pause))
     `(( (seq pause (· pause)) ⊥ ⊥ ())))
    (test-equal
     (do `(seq (· pause) pause))
     `(( (seq (hat pause) pause) ⊥ one ()))))
  (test-case "6"
    (test-equal
     (do `(seq (· (hat pause)) pause))
     `(( (seq pause (· pause)) ⊥ ⊥ () )))

    (test-equal
     (do `(seq (· nothing) pause))
     `(( (seq nothing (· pause)) ⊥ ⊥ () ))))

  (test-case "7"
    (test-not-false "pbar"
                    (redex-match esterel pbar `(seq pause (hat pause))))
    (test-equal
     (do `(· (seq pause (hat pause))))
     `(( (seq pause (· (hat pause))) ⊥ ⊥ ())))
    (test-equal
     (do `(· (seq pause (seq pause (hat pause)))))
     `(( (seq pause (· (seq pause (hat pause)))) ⊥ ⊥ () ))))

  (test-case "8"
    (check-not-false
     "8"
     (redex-match esterel pbardot `(seq pause (seq (· (hat pause)) pause))))
    (check-not-false
     "8"
     (redex-match esterel pbardot `(seq (· (hat pause)) pause)))
    (check-not-false
     "8"
     (redex-match esterel (seq p qbardot) `(seq pause (seq (· (hat pause)) pause))))
    (test-equal
     (do ` (seq pause (· (hat pause))))
     `(( (seq pause pause) ⊥ zero ())))
    (test-equal
     (do `(seq pause (seq pause (· (hat pause)))))
     `(( (seq pause  (seq pause pause)) ⊥ zero () )))
    (test-equal
     (do `(seq pause (seq pause (· pause))) )
     `(( (seq pause (seq pause (hat pause))) ⊥ one () )))
    (test-equal
     (do `(seq pause (seq (· (hat pause)) pause)))
     `(( (seq pause (seq pause (· pause))) ⊥ ⊥ () ))))

  (test-case "9"
    (test-equal
     (do `(· (par pause pause)))
     `(( (par (· pause) ⊥ (· pause) ⊥) ⊥ ⊥ ()))))

  (test-case "10"
    (test-equal
     (do `(· (par (hat pause) (hat pause))))
     `(( (par (· (hat pause)) ⊥ (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "11"
    (test-equal
     (do `(· (par (hat pause)  pause)))
     `(( (par (· (hat pause)) ⊥ pause zero) ⊥ ⊥ ()))))

  (test-case "12"
    (test-equal
     (do `(· (par  pause (hat pause))))
     `(( (par pause zero (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "13"
    (test-equal
     (do `(par pause zero (hat pause) one))
     `(( (par pause (hat pause)) ⊥ one ()))))
  (test-case "14"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ pause zero))
     `(( (par (seq (· pause) pause) ⊥ pause zero) ⊥ ⊥ ()))))
  (test-case "15"
    (test-equal
     (do `(par pause zero (· (seq pause pause)) ⊥))
     `(( (par pause zero (seq (· pause) pause) ⊥) ⊥ ⊥ ()))))
  (test-case "14/15"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ (· (seq pause pause)) ⊥))
     `(( (par (seq (· pause) pause) ⊥ (· (seq pause pause)) ⊥) ⊥ ⊥ ())
       ( (par (· (seq pause pause)) ⊥ (seq (· pause) pause) ⊥) ⊥ ⊥ ())))
    (test-equal
     (do/det `(par (· (seq pause pause)) ⊥ (· (seq pause pause)) ⊥))
     `(( (par (seq (· pause) pause) ⊥ (· (seq pause pause)) ⊥) ⊥ ⊥ ()) ))
    (test-equal
     (do/det `(· (par (signal pQ (emit x)) (emit C))))
     `((  (par (· (signal pQ (emit x))) ⊥ (· (emit C)) ⊥)
          ⊥ ⊥ ()) ))
    (test-equal
     (do/det `(par (· (signal pQ (emit x))) ⊥ (· (emit C)) ⊥))
     `((  (par  (signal pQ ⊥ (·(emit x))) ⊥ (· (emit C)) ⊥)
          ⊥ ⊥ ()) ))
    (test-equal
     (do/det `(par (signal pQ (emit x)) zero (· (emit C)) ⊥))
     `((  (par  (signal pQ (emit x)) zero (emit C) zero)
          C ⊥ ()) )))
  (test-case "16"
    (test-equal
     (do `(· (loop (seq pause nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "17"
    (test-equal
     (do `(· (loop (seq (hat pause) nothing))))
     `(( (loop go (· (seq (hat pause) nothing))) ⊥ ⊥ ())))
    (test-equal
     (do `(· (loop (hat pause) )))
     `(( (loop go (· (hat pause))) ⊥ ⊥ ()))))
  (test-case "18"
    (test-equal
     (do `(loop go (seq pause (· nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "19"
    (test-equal
     (do `(loop go (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ one ())))
    (test-equal
     (do `(loop stop (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ one ()))))
  (test-case "20"
    (test-equal
     (do `(loop go (seq (· (hat pause)) nothing)))
     `(( (loop go (seq pause (· nothing))) ⊥ ⊥ ())))
    (test-equal
     (do `(loop stop (seq (· (hat pause)) nothing)))
     `(( (loop stop (seq pause (· nothing))) ⊥ ⊥ ()))))
  (test-case "21"
    (test-equal
     (do `(· (trap (par pause pause))))
     `(( (trap (· (par pause pause))) ⊥ ⊥ ()))))
  (test-case  "22"
    (test-equal
     (do `(trap (seq (· nothing) pause)))
     `(( (trap (seq  nothing (· pause))) ⊥ ⊥ ()))))
  (test-case "23"
    (test-equal
     (do `(trap (seq (· (exit two)) pause)))
     `(( (trap (seq (exit two) pause)) ⊥ zero ()))))
  (test-case "24"
    (test-equal
     (do `(trap (seq pause (· (hat pause)))))
     `(( (trap (seq pause pause)) ⊥ zero ()))))
  (test-case "25"
    (test-equal
     (do `(trap (seq pause (· pause))))
     `(( (trap (seq pause (hat pause))) ⊥ one ()))))
  (test-case "26"
    (test-equal
     (do `(trap (· (exit three))))
     `(( (trap (exit three)) ⊥ (natnorm two) () ))))
  (test-case "27"
    (test-equal
     (do `(· (exit three)))
     `(( (exit three) ⊥ three ()))))
  (test-case "28"
    (test-equal
     (do `(· (signal S (emit S))))
     `(( (signal S ⊥ (· (emit S))) ⊥ ⊥ ()))))
  (test-case "29"
    (test-true "29-pdotdot"
               (redex-match? esterel-eval pdotdot `(seq (· (emit S«156»)) pause)))
    (test-true "29-E"
               (redex-match? esterel-eval E `((S«156» ⊥))))
    (test-equal
     (do `(seq (· (emit S)) pause))
     `(( (seq (emit S) (· pause)) S ⊥ ())))
    (test-equal
     (do `(signal S ⊥ (seq (· (emit S)) pause)))
     `(( (signal S one (seq (emit S) (· pause))) ⊥ ⊥ ()))))
  (test-case "30"
    (test-equal
     `(Can_S (signal S zero (seq (emit S) (seq pause (· pause)))) ((S ⊥)))
     `())
    (test-equal
     (do `(signal S ⊥ (seq (emit S) (seq pause (· pause)))))
     `(
       ((signal
            S
          zero
          (seq (emit S) (seq pause (· pause))))
        ⊥
        ⊥
        ())
       )))
  (test-case "31"
    (test-equal
     (do `(signal S zero (seq (· (emit R)) pause)))
     `(( (signal S zero (seq (emit R) (· pause)))
         R
         ⊥
         ())))
    (test-equal
     `(Can_S (seq (· (hat pause)) (emit S)) ())
     `((S one)))
    (test-equal
     (do `(signal S ⊥ (seq (· (hat pause)) (emit S))))
     `(( (signal S ⊥ (seq pause (· (emit S))))
         ⊥
         ⊥
         ()))))

  (test-case "32"
    (test-equal
     (do `(signal S zero (· (emit R))))
     `(( (signal S (emit R))
         R
         zero
         ())))
    (test-equal
     (do `(· pause))
     `(( (hat pause) ⊥ one ())))
    (test-equal
     (do `(signal S zero (· pause)))
     `(( (signal S (hat pause))
         ⊥
         one
         ()))))

  (test-case "33"
    (test-equal
     (do `(signal S one (· (emit S)) ))
     `(( (signal S (emit S))
         ⊥
         zero
         ()))))

  (test-case "34"
    (test-equal
     (do `(· (emit S)))
     `(( (emit S) S zero ()))))

  (test-case "35"
    (test-equal
     (do `(· (suspend (hat pause) S))
       `((S (Succ zero))))
     `(( (suspend (hat pause) S) ⊥ (Succ zero) () ))))

  (test-case "36"
    (test-equal
     (do `(· (suspend (hat pause) S))
       `((S zero)))
     `(( (suspend (· (hat pause)) S) ⊥ ⊥ () ))))

  (test-case "37"
    (test-equal
     (do `(· (suspend pause S)))
     `(( (suspend (· pause) S) ⊥ ⊥ () ))))

  (test-case "38"
    (test-equal
     (do `(suspend (· pause) S))
     `(( (suspend (hat pause) S) ⊥ one () ))))

  (test-case "39"
    (test-equal
     (do `(· (present t pause pause)) `((t one)))
     `(( (present t (· pause) pause) ⊥ ⊥ ()))))
  (test-case "40"
    (test-equal
     (do `(· (present t pause pause)) `((t zero)))
     `(( (present t pause (· pause)) ⊥ ⊥ ()))))

  (test-case "41"
    (test-equal
     (do `(· (present t (hat pause) pause)) `((t zero)))
     `(( (present t (· (hat pause)) pause) ⊥ ⊥ ()))))
  (test-case "42"
    (test-equal
     (do `(· (present t  pause (hat pause))) `((t one)))
     `(( (present t pause (· (hat pause))) ⊥ ⊥ ()))))
  (test-case "43"
    (test-equal
     (do `(present t (· (hat pause)) pause))
     `(( (present t pause pause) ⊥ zero ()))))
  (test-case "44"
    (test-equal
     (do `(present t pause (· (hat pause))))
     `(( (present t pause pause) ⊥ zero ()))))
  (test-case "45"
    (test-equal
     (do* (· (shared s := 5 nothing)) ())
     `(( (shared s := 5 (· nothing)) ((dshared s 5 old))
                                     ⊥ ⊥ )))
    (test-equal
     (do* (· (shared s := 5 nothing)) ((dshared s 5 old)))
     `(( (shared s := 5 (· nothing)) ((dshared s 5 old))
                                     ⊥ ⊥ ))))
  (test-case "46"
    (test-equal
     (do* (· (shared s := 5 (hat pause))) ((dshared s 12 ready)))
     `(( (shared s := 5 (· (hat pause))) ((dshared s 12 old))
                                         ⊥ ⊥
                                         ))))
  (test-case "47"
    (test-equal
     (do* (shared s := 1 (· nothing)) ((dshared s 0 old)))
     `(( (shared s := 1 (· nothing)) ((dshared s 0 ready))
                                     ⊥ ⊥ ))))
  (test-case "48"
    (test-equal
     (do* (shared s := 1 (· nothing)) ((dshared s 0 ready)))
     `(( (shared s := 1 nothing) ((dshared s 0 ready))
                                 ⊥ zero ))))
  (test-case "49"
    (test-equal
     (do* (shared s := 1
            (· (<= s (+ 1 y))))
          ((dshared s 1 old)
           (dshared y 1 ready)))
     `((
        (shared s := 1 (<= s (+ 1 y)))
        ((dshared s 2 new)
         (dshared y 1 ready))
        ⊥
        zero
        ))))
  (test-case "50"
    (test-equal
     (do* (shared s := 1
            (· (<= s (+ 1 y))))
          ((dshared s 1 new )
           (dshared y 1 ready)))
     `((
        (shared s := 1 (<= s (+ 1 y)))
        ((dshared s 3 new)
         (dshared y 1 ready))
        ⊥
        zero
        ))))

  (test-case "51"
    (test-equal `(shared-of (+ 2 1) ()) `())
    (check-true
     (redex-match? esterel-eval (· (var v := call p)) `(· (var v := (+ 2 1) nothing))))
    (test-equal
     (do*
      (· (var v := (+ 2 1) nothing))
      ())
     `((
        (var v := (+ 2 1) (· nothing))
        ((dvar v 3))
        ⊥ ⊥
        ))))

  (test-case "52"
    (test-equal
     (do*
      (· (var v := 3 (hat pause)))
      ((dvar v 2)))
     `((
        (var v := 3 (· (hat pause)))
        ((dvar v 2))
        ⊥
        ⊥
        ))))
  (test-case "53"
    (test-equal
     (do*
      (var v := 3 (· (hat pause)))
      ((dvar v 2)))
     `((
        (var v := 3 pause)
        ((dvar v 2))
        ⊥
        zero)))
    (test-equal
     (do*
      (var v := 3 (· (:= v 4)))
      ((dvar v 2)))
     `((
        (var v := 3 (:= v 4))
        ((dvar v 4))
        ⊥
        zero))))
  (test-case "54"
    (test-equal
     (do*
      (· (if v nothing pause))
      ((dvar v 1)))
     `((
        (if v (· nothing) pause)
        ((dvar v 1))
        ⊥ ⊥))))
  (test-case "55"
    (test-equal
     (do*
      (· (if v nothing pause))
      ((dvar v 0)))
     `((
        (if v nothing (· pause))
        ((dvar v 0))
        ⊥ ⊥))))
  (test-case "56"
    (test-equal
     (do*
      (· (if v (hat pause) nothing))
      ((dvar v 12)))
     `(( (if v (· (hat pause)) nothing)
         ((dvar v 12))
         ⊥ ⊥))))
  (test-case "57"
    (test-equal
     (do*
      (· (if v nothing (hat pause)))
      ((dvar v 12)))
     `((
        (if v nothing (· (hat pause)))
        ((dvar v 12))
        ⊥ ⊥
        ))))
  (test-case "58"
    (test-equal
     (do*
      (if v (· pause) nothing)
      ((dvar v 12)))
     `((
        (if v (hat pause) nothing)
        ((dvar v 12))
        ⊥ (Succ zero)
        ))))
  (test-case "59"
    (test-equal
     (do*
      (if v nothing (· pause))
      ((dvar v 12)))
     `((
        (if v nothing (hat pause))
        ((dvar v 12))
        ⊥ (Succ zero)
        ))))
  (test-case "60"
    (test-equal
     (do*
      (· (:= v 4))
      ((dvar v 2)))
     `((
        (:= v 4)
        ((dvar v 4))
        ⊥
        zero))))
  (test-case "bugs"
    (test-equal
     (do `(loop go (present t (· (hat pause)) nothing)))
     `(( (loop stop (· (present t pause nothing))) ⊥ ⊥ () )))
    (test-equal
     (do `(trap (· (signal T (hat pause)))))
     `(( (trap (signal T ⊥ (· (hat pause))))
         ⊥
         ⊥
         ())))
    (test-equal
     (do `(· (signal T (hat pause))))
     `(( (signal T ⊥ (· (hat pause)))
         ⊥
         ⊥
         ()  )))
    (test-equal (do `(· (par nothing nothing)))
                `(( (par (· nothing) ⊥ (· nothing) ⊥) ⊥ ⊥ () )))

    (test-equal (do `(par (· nothing) ⊥ nothing zero))
                `(( (par nothing zero nothing zero) ⊥ ⊥ () )))

    (test-equal (do `(par nothing zero nothing zero))
                `(( (par nothing nothing) ⊥ zero () )))

    (test-equal
     (do* (· (seq (shared c := 1 nothing) (suspend pause plU)))
          ((dshared c 1 old)))
     `((
        (seq (·(shared c := 1 nothing)) (suspend pause plU))
        ((dshared c 1 old))
        ⊥
        ⊥
        )))
    (test-equal
     (do*  (seq (· (shared c := 1 nothing)) (suspend pause plU))
           ((dshared c 1 old)))
     `((
        (seq (shared c := 1 (· nothing)) (suspend pause plU))
        ((dshared c 1 old))
        ⊥
        ⊥
        )))))

(test-case "eval bugs"
  (test-judgment-holds
   (c->>
    (machine (par (signal f (emit S)) (shared v := 1 pause)) ()) ()
    (machine (par (signal S_f (emit S_S)) (shared v := 1 (hat pause))) ((dshared v 1 ready)))
    (S_S)
    (Succ zero)))
  (test-judgment-holds
   (cc->>
    (machine (par (signal f (emit S)) (shared v := 1 pause)) ()) ()
    (machine (par (signal S_f (emit S_S)) (shared v := 1 (hat pause))) ((dshared v 1 ready)))
    (S_S)
    (Succ zero)))

  #|
    (test-judgment-holds
     (c->>
      (seq (loop (present h nothing (hat pause))) (trap (exit (Succ (Succ zero)))))
      ))
    |#
  (test-judgment-holds
   (c->>
    (machine
     (present Q (par pause nothing) (signal z nothing))
     ())
    ((Q one))

    (machine
     (present S_Q (par (hat pause) nothing) (signal S_z nothing))
     ())
    ()
    (Succ zero)))
  (test-judgment-holds
   (c->>
    (machine
     (seq (trap (signal X (emit p))) (suspend (signal g pause) UU))
     ())
    ((g one) (X zero))
    (machine (seq (trap (signal S_X (emit S_p)))
                  (suspend (signal S_g (hat pause)) S_U))
             ())
    (S_p)
    (Succ zero)))
  (test-judgment-holds
   (c->>
    (machine
     (seq (suspend (loop (seq (hat pause) (emit QY))) t) (signal f (trap nothing)))
     ())
    ((t zero))
    (machine
     (seq (suspend (loop (seq (hat pause) (emit S_QY))) S_t) (signal f (trap nothing)))
     ())
    (S_QY)
    (Succ zero)))
  (test-judgment-holds
   (c->>
    (machine
     (seq (suspend (hat pause) N) (signal k (emit Z)))
     ())
    ((N zero))
    (machine
     (seq (suspend pause S_N) (signal S_k (emit S_Z)))
     ())
    (S_Z)
    zero))
  (test-judgment-holds
   (c->>
    (machine
     (seq (trap (hat pause)) (signal n (emit h)))
     ())
    ()
    (machine
     (seq (trap pause) (signal S_n (emit S_h)))
     ())
    (S_h)
    zero))
  (test-judgment-holds
   (cc->>
    (machine
     (seq (trap (hat pause)) (signal n (emit h)))
     ())
    ()
    (machine
     (seq (trap pause) (signal S_n (emit S_h)))
     ())
    (S_h)
    zero))
  (test-judgment-holds
   (cc->>
    (machine
     (seq (loop (hat pause)) (trap nothing))
     ())
    ()
    (machine
     (seq (loop (hat pause)) (trap nothing))
     ())
    ()
    one))
  (test-judgment-holds
   (cc->>
    (machine
     (signal A (signal Gz (emit H)))
     ())
    ()
    (machine
     (signal S_A (signal S_Gz (emit S_H)))
     ())
    (S_H)
    zero))
  (test-judgment-holds
   (cc->>
    (machine
     (trap (trap (exit (Succ two))))
     ())
    ()
    (machine
     (trap (trap (exit (Succ two))))
     ())
    ()
    zero))

  (test-judgment-holds
   (cc->>
    (machine
     (seq (trap (trap (exit (Succ two)))) (signal A (signal Gz (emit H))))
     ())
    ()
    (machine
     (seq (trap (trap (exit (Succ two)))) (signal S_A (signal S_Gz (emit S_H))))
     ())
    (S_H)
    zero))

  (test-judgment-holds (cc->>
                        (machine
                         (loop (hat pause))
                         ())
                        ()
                        (machine
                         (loop (hat pause))
                         ())
                        ()
                        one))
  (test-judgment-holds (cc->>
                        (machine
                         (seq (emit z) (loop pause))
                         ())
                        ()
                        (machine
                         (seq (emit S_z) (loop (hat pause)))
                         ())
                        (z)
                        one))
  (test-judgment-holds (cc->>
                        (machine
                         (seq (emit z) (loop (hat pause)))
                         ())
                        ()
                        (machine
                         (seq (emit S_z) (loop (hat pause)))
                         ())
                        ()
                        one))
  (test-judgment-holds (cc->>
                        (machine
                         (trap (trap (exit (Succ two))))
                         ())
                        ()
                        any_1
                        any_2
                        any_3))
  (test-judgment-holds
   (cc->>
    (machine
     (seq (trap (trap (exit (Succ two)))) (signal IH nothing))
     ())
    ()
    (machine
     (seq (trap (trap (exit (Succ two)))) (signal S_IH nothing))
     ())
    ()
    zero))

  (test-judgment-holds
   (cc->>
    (machine
     (par (seq (emit Q) (emit Q)) (signal S pause))
     ())
    ()
    (machine
     (par (seq (emit S_Q) (emit S_Q)) (signal S_v (hat pause)))
     ())
    (Q)
    one)))

(test-case "slow tests"
  (time ;; failing
   (test-judgment-holds
    (cc->>
     (machine
      (par (signal TY (signal a nothing))
           (signal S (par (par (emit R) pause)
                          pause)))
      ())
     ()
     (machine (par (signal S_TY (signal S_a nothing))
                   (signal S_S (par (par (emit S_R) (hat pause))
                                    (hat pause))))
              ())
     (R)
     one)))
  (time ;; failing
   (test-judgment-holds
    (cc->>
     (machine
      (par (signal K (signal Z (par nothing pause))) (signal R nothing))
      ())
     ()
     (machine
      (par (signal S_K (signal S_Z (par nothing (hat pause)))) (signal S_R nothing))
      ())
     ()
     one))))

(module+ random
  (define-syntax-rule (tjh e)
    (begin
      (test-judgment-holds e)
      (judgment-holds e)))
  (test-case "random tests"
    ;(current-traced-metafunctions 'all)
    (redex-check
     esterel-check
     #:satisfying (okay p-check)
     (begin
       ;(displayln `p-check)
       (term-let ([p `(uniquify p-check)])
                 (tjh (cc->> (fix-env (machine p ()))
                             (random-E (free-signal-vars p))
                             (machine pbar data_*) (S ...) k))))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay phat-check)
     (begin
       ;(displayln `phat-check)
       (term-let ([p `(uniquify phat-check)])
                 (tjh (cc->> (fix-env (machine p ()))
                             (random-E (free-signal-vars p))
                             (machine pbar data_*) (S ...) k))))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay pbar-check)
     (begin
       ;(displayln `pbar-check)
       (term-let ([p `(uniquify pbar-check)])
                 (tjh (cc->> (fix-env (machine p ()))
                             (random-E (free-signal-vars p))
                             (machine pbar data_*) (S ...) k))))
     #:attempts 333
     )))

(test-case "eval part 2"
  (test-judgment-holds
   (c->>
    (machine (par (signal pQ (emit x)) (emit C)) ())
    ()
    (machine (par (signal S_pQ (emit S_x)) (emit S_C)) ())
    any
    zero))
  (test-judgment-holds
   (cc->>
    (machine (par (signal pQ (emit x)) (emit C)) ())
    ()
    (machine (par (signal S_pQ (emit S_x)) (emit S_C)) ())
    any
    zero))
  (test-judgment-holds
   (c->>
    (fix-env
     (machine
      (seq (shared c := Q nothing) (suspend pause plU))
      ()))
    ()
    (machine (seq (shared s_c := 1 nothing)
                  (suspend (hat pause) S_p))
             ((dshared s_c 1 ready)))
    ()
    (Succ zero)))
  (test-judgment-holds
   (cc->>
    (fix-env
     (machine
      (seq (shared c := Q nothing) (suspend pause plU))
      ()))
    ()
    (machine (seq (shared s_c := 1 nothing)
                  (suspend (hat pause) S_p))
             ((dshared s_c 1 ready)))
    ()
    (Succ zero))))

(test-case "Can bugs"
  ;(current-traced-metafunctions '(Can Can_V))
  (test-equal
   `(Can (present S pause (trap (emit A))) ())
   `( ((A (Succ zero)))
      ((Succ zero) zero)
      () ))
  (test-equal
   `(Can (suspend (loop (seq (hat pause) (emit QY))) tt) ())
   `( ((QY (Succ zero)))
      ((Succ zero))
      () ))
  (test-equal
   `(Can (suspend (hat pause) xJux) ())
   `( () ((Succ zero) zero) () ))
  (test-equal
   `(Can_S (seq (· (emit S)) pause) ((S ⊥)))
   `((S one)))
  (test-equal
   `(Can_S (seq (· (hat pause)) (emit S)) ())
   `((S one)))
  (test-equal
   `(Can_K (· (hat pause)) ())
   `(zero))
  (test-equal
   `(∉ zero (Can_K (· (hat pause)) ()))
   #f))

(test-case "without"
  (check-equal?
   (term (without (zero zero) zero))
   (term ()))
  (check-equal?
   (term (Can (seq (trap (· (present S5 nothing (exit (Succ (Succ zero)))))) pause) ((S5 ⊥))))
   (term (() ((Succ zero)) ()))))

(test-case "regression tests"
  (check-true
   (redex-match?
    esterel-eval
    p
    `(signal
         O4
       (par
        (signal
            A1
          (par
           (signal
               B2
             (par
              (signal
                  R3
                (par
                 (loop
                  (trap
                   (par
                    (seq
                     (suspend
                      (seq
                       (seq
                        (par
                         (trap
                          (loop
                           (seq pause (present A1 (exit (Succ (Succ zero))) nothing))))
                         (trap
                          (loop
                           (seq
                            pause
                            (present B2 (exit (Succ (Succ zero))) nothing)))))
                        (emit O4))
                       (loop pause))
                      R3)
                     (exit (Succ (Succ zero))))
                    (seq
                     (trap
                      (loop
                       (seq pause (present R3 (exit (Succ (Succ zero))) nothing))))
                     (exit (Succ (Succ zero)))))))
                 (loop (seq (present R3 (emit R3) nothing) pause))))
              (loop (seq (present B2 (emit B2) nothing) pause))))
           (loop (seq (present A1 (emit A1) nothing) pause))))
        (loop (seq (present O4 (emit O4) nothing) pause))))
    ))


  (test-case "abro"
    (judgment-holds
     (cc->>
      (machine
       (loop
        (trap
         (par
          (seq
           (suspend
            (seq
             (seq
              (par
               (trap
                (loop
                 (seq
                  pause
                  (present A (exit (Succ (Succ zero))) nothing))))
               (trap
                (loop
                 (seq
                  pause
                  (present B (exit (Succ (Succ zero))) nothing)))))
              (emit O))
             (loop pause))
            R3)
           (exit (Succ (Succ zero))))
          (seq
           (trap
            (loop
             (seq pause (present R (exit (Succ (Succ zero))) nothing))))
           (exit (Succ (Succ zero)))))))
       ())
      ((A (Succ zero)) (B zero) (R zero))
      any_1 any_2 any_3))))