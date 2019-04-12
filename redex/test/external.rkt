#lang racket

#|

This module provides the function `run-with-signals`, which takes a s-expression
representation of an Esterel program and a sequence of input signals to send
it, runs it using the Esterel-to-C compiler, and returns the produced sequence
of output signals.

It depends on two parameters:

 - `esterel-root` should be the path to the root of the Esterel distribution.
   We expect to find two files relative to that: bin/esterel.exe and
   lib/libcoresim.a. It defaults to directory relative to the current module:
   ../../install-prefix/esterel

 - `c-compiler` should be the path to the C compiler. It defaults to the value
   of the CC environment variable, or /usr/bin/cc if that isn't set.

|#

(require esterel-calculus/redex/model/concrete
         racket/runtime-path)
(provide run-with-signals
         esterel-root
         c-compiler
         signals->input-string
         output-string->signals
         warn-about-uninstalled-esterel)

(define-logger esterelv5)

(module+ test (require rackunit))

(define-runtime-path esterel-root-path "../../install-prefix/esterel")

; Parameter controlling where to look for Esterel:
(define esterel-root
  (make-parameter esterel-root-path path-string?))

; Parameter containing the location of the C compiler:
(define c-compiler
  (make-parameter (or (getenv "CC") "/usr/bin/cc")
                  path-string?))

; An Esterel-error is one of:
; - 'instantaneous-loop
; - 'non-constructive
; - 'c-compiler-error
; - 'other-esterel-error

; A Signal-sequence is [listof [listof symbol?]]

; Some example Esterel modules:
(define BAD-LOOP-EXAMPLE
  '(BadLoop () () (loop nothing)))
(define GOOD-LOOP-EXAMPLE
  '(GoodLoop () () (loop pause)))
(define NON-CONSTRUCTIVE-EXAMPLE
  '(NonConstructive () () (signal S (present S (emit S) nothing))))
(define UNKNOWN-SIGNAL-EXAMPLE
  '(UnknownSignal () () (emit Q)))
(define AOP-EXAMPLE
  '(AOP (A) (O P)
        (loop
              (seq (present A (emit O) (emit P))
                   pause))))

; run-with-signals : Esterel-module Signal-sequence
;                      -> [or Signal-sequence Esterel-error]
; Runs an s-exp Esterel module using the native Esterel implementation,
; sending it the specified sequence of signals, and returning the sequence
; of output signals.
(define (run-with-signals program signals #:debug? [debug? #f])
  (cond
    [(not (directory-exists? (esterel-root)))
     'not-installed]
    [else
     (define exe-or-error (compile/redex program #:debug? debug?))
     (cond
       [(symbol? exe-or-error) exe-or-error]
       [else
        (define error (open-output-string))
        (define success? #f)
        (define output
          (parameterize ([current-error-port error])
            (with-input-from-string
                (signals->input-string signals)
              (λ ()
                (with-output-to-string
                  (λ () (set! success? (system* exe-or-error))))))))
        (delete-file exe-or-error)
        (match* (success? (get-output-string error))
          [(#t "") (output-string->signals output)]
          [(_ (regexp #rx"Causality error"))
           'non-constructive]
          [(_ t)
           (displayln t)
           'other-esterel-error])])]))

(module+ test
  (cond
    [(directory-exists? (esterel-root))
     (check-equal? (run-with-signals AOP-EXAMPLE '((A) () (A) ()))
                   '((O) (P) (O) (P)))
     (check-equal? (run-with-signals NON-CONSTRUCTIVE-EXAMPLE '(()))
                   'non-constructive)
     (check-equal? (run-with-signals BAD-LOOP-EXAMPLE '())
                   'instantaneous-loop)]
    [else (warn-about-uninstalled-esterel)]))

; output-string->signals : string? -> Signal-sequence
; Turns the output of running an Esterel program into a list of lists of
; emitted output signals.
(define (output-string->signals output)
  (map (λ (each)
         (map concrete->id (call-with-input-string (format "(~a)" each) read)))
       (rest (regexp-split #rx"\n?[^\n]*--- Output: " output))))

(module+ test
  (check-equal? (output-string->signals
                 "garbage--- Output: V_A V_B\n--- Output: \n--- Output: V_R")
                '((A B) () (R))))


; signals->input-string : Signal-sequence -> string?
; Turns a sequence of input signals into a string in the right format to
; send to an Esterel program.
(define (signals->input-string signals)
  (apply string-append
         (map (λ (symbol-list)
                (format "~a;"
                        (apply string-append
                               (map (λ (symbol) (format "~a " (id->concrete symbol)))
                                    symbol-list))))
              signals)))

(module+ test
  (check-equal? (signals->input-string '((A) () (A B)))
                "V_A ;;V_A V_B ;")
  (check-equal? (signals->input-string '((S1)))
                "V_S_49 ;"))


; compile/redex : Esterel-module -> [or path? Esterel-error]
; Compiles an s-expression representation of an Esterel module to into an
; executable, returning the name of the executable.
(define (compile/redex program #:debug? [debug? #f])
  (define prog (redex->concrete program))
  (log-esterelv5-debug prog)
  (compile/concrete prog))

(module+ test
  (cond
    [(directory-exists? (esterel-root))
         (check-equal? (compile/redex BAD-LOOP-EXAMPLE) 'instantaneous-loop)
         (check-not-false
          (let ([result (compile/redex NON-CONSTRUCTIVE-EXAMPLE)])
            (and path? (delete-file result))))
         (check-equal?
          (parameterize ([current-output-port (open-output-nowhere)])
            (compile/redex UNKNOWN-SIGNAL-EXAMPLE))
          'other-esterel-error)
         (check-not-false
          (let ([result (compile/redex GOOD-LOOP-EXAMPLE)])
            (and (path? result) (delete-file result))))]
    [else (warn-about-uninstalled-esterel)]))


; compile/concrete : string? -> [or path? Esterel-error]
; Given concrete Esterel syntax, compiles it into an executable and returns
; either the name of the executable or an error.
(define (compile/concrete program)
  (define src-file-name    (make-temporary-file "esterel-~a.strl"))
  (define c-file-name      (path-replace-extension src-file-name ".c"))
  (define exe-file-name    (path-replace-extension src-file-name ".exe"))
    
  (define esterel-compiler (build-path (esterel-root) "bin" "esterel"))
  (define esterel-lib      (build-path (esterel-root) "lib" "libcoresim.a"))


  ; To compile the file, we write the Esterel concrete syntax to a temporary
  ; .strl file, and then use the Esterel compiler to translate it to C. We
  ; capture stderr of the Esterel compiler, so that we can look at the error
  ; message if it fails.
  ;
  ; We need to run the Esterel compiler in the temp directory, because it puts
  ; its C output in its current working directory.
  (with-output-to-file src-file-name
    (λ () (display program))
    #:exists 'truncate)
  (define error-out (open-output-string))
  (define esterel-success?
    (parameterize ([current-directory (find-system-path 'temp-dir)]
                   [current-error-port error-out])
      ; The ESTEREL environment variable needs to be set to the esterel root
      (putenv "ESTEREL" (path->string (setup-symlink-dance (esterel-root))))
      (system* esterel-compiler "-simul" "-I" src-file-name)))
  (delete-file src-file-name)
  (define esterel-error-output (get-output-string error-out))
  (log-esterelv5-debug esterel-error-output)

  ; Now we check for errors. If (system* esterel-compiler ...) returned #true,
  ; then the translation to C succeeded, and it's time to run the C compiler.
  ; Otherwise we match against the Esterel compiler's error output to determine
  ; which error symbol to return.
  (cond
    [esterel-success?
     (define cc-success?
       (system* (c-compiler) "-o" exe-file-name c-file-name esterel-lib))
     (delete-file c-file-name)
     (if cc-success? exe-file-name 'c-compiler-error)]
    [(regexp-match #rx"instantaneous loop" esterel-error-output)
     'instantaneous-loop]
    [(or (regexp-match #rx"cyclic program" esterel-error-output)
         (regexp-match #rx"Causality error" esterel-error-output))
     'non-constructive]
    [else
     (displayln esterel-error-output)
     (displayln program)
     'other-esterel-error]))

(define (setup-symlink-dance path)
  (cond
    [(eq? (system-path-convention-type) 'unix)
     (define loc (make-temporary-file "esterel-shim~a" 'directory))
     (define result-path (build-path loc "esterel"))
     (unless (system* (find-executable-path "ln")
                      "-s"
                      path
                      result-path)
       (error "error while creating temporary symlink to esterel root"))
     result-path]
    [else path]))
  

(define (warn-about-uninstalled-esterel)
  (printf "\n\nWARNING: Esterel is not installed; skipping some tests\n\n\n")
  (set! warn-about-uninstalled-esterel void))
