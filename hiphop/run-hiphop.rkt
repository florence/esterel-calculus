#lang racket

(require esterel-calculus/hiphop/find
         esterel-calculus/hiphop/to-hiphop
         esterel-calculus/hiphop/parse
         esterel-calculus/redex/test/external)
(provide run-hiphop-with-signals)
(define-logger hiphop)

; run-hiphop : Esterel-module Signal-sequence -> Signal-sequence or #f or 'not-installed
; Runs the given hiphop program, sending it the given sequence of
; input signals and producing the sequence of output signals.
(define (run-hiphop-with-signals program insigs
                                 #:debug? [debug? #f])
  (cond
    [(file-exists? (hop-binary-path))
     (define batch-file (make-temporary-file "run-~a.js"))
     (define input-file (path-replace-extension batch-file ".in"))
     (call-with-output-file batch-file
       (λ (port)
         (redex->hiphop/port port program)
         (displayln "try {" port)
         (displayln "  hh.batch(machine);" port)
         (displayln "} catch (e) {" port)
         (displayln "  console.log(e.message);" port)
         (displayln "  process.exit(1);" port)
         (displayln "}" port))
       #:exists 'truncate)
     (call-with-output-file input-file
       (λ (port) (display (signals->input-string insigs) port)))
     (define out (open-output-string))
     (define err (open-output-string))
     (with-input-from-file input-file
       (lambda ()
         (parameterize ([current-output-port out]
                        [current-error-port err])
           (system*
            (hop-binary-path)
            "--no-server" "--no-sofile" "-q" "-I"
            (hiphop-lib-directory)
            batch-file))))
     (delete-file batch-file)
     (delete-file input-file)
     (define outs (get-output-string out))
     (define errs (get-output-string err))
     (log-hiphop-debug (format "output: ~a" outs))
     (log-hiphop-debug (format "error: ~a" errs))
     (cond
       [(or (regexp-match? #rx".*RUNTIME ERROR" outs)
            (regexp-match? #rx".*CAUSALITY ERROR" outs)
            (regexp-match? #rx".*SIGNAL ERROR" outs))
        #f]
       [(not (equal? errs "")) #f]
       [else
        (map (λ (iteration)
               (map hiphop->id (third iteration)))
             (parse-hiphop-output/string outs))])]
    [else 'not-installed]))

(module+ test
  (require rackunit)

  (check-equal?
    (run-hiphop-with-signals
      '(AO (A) (O) (loop (seq (present A (emit O) nothing) pause)))
      '(() (A) () (A)))
    '(() (O) () (O)))
  (check-equal?
   (run-hiphop-with-signals '(TEST () () (loop nothing)) '(()))
   #f))
