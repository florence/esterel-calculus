#lang racket
(require racket/runtime-path)

(define-runtime-path log-dir "logs")
(define-runtime-path external "../redex/test/long-tests/external.rkt")
(define-runtime-path internal "../redex/test/long-tests/internal.rkt")
(define-runtime-path agda "../cross-tests/redex-model-implies-agda-model.rkt")

(define (make-file-name name iter)
  (~a name "-" iter ".log"))

(define (determine-next-number dir)
  (add1
   (apply
    max
    0
    (for/list ([f (in-list (directory-list dir))])
      (string->number
       (second
        (regexp-match "[a-z]+-([0-9]+).log" (path->string f))))))))

(define (run-with-output-file cmd args name n)
  (define o (open-output-file (build-path log-dir (make-file-name name n))))
  (thread
   (lambda ()
     (let loop () (sleep 1) (flush-output o) (loop))))
  (match-define (list #f i _ #f f)
    (apply process*/ports o #f o cmd args))
  f)

(define racket (find-executable-path "racket"))

(module+ main
  (make-directory* log-dir)
  (define n (determine-next-number log-dir))
  (define fs
    (list
     (run-with-output-file racket (list external) "external" n)
     (run-with-output-file racket (list internal) "internal" n)
     (run-with-output-file racket (list agda "-r" "-c" "10000000") "agda" n)))
  (for-each (lambda (f) (f 'wait)) fs))
