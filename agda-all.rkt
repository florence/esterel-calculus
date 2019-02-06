#lang racket/base
(require racket/runtime-path racket/path racket/system)

(define-runtime-path agda "agda")
(define all.agda (build-path agda "all.agda"))
(define agda-files
  (for/list ([f (in-directory agda)]
             #:when (regexp-match #rx"[.]agda$" (path->string f)))
    (path->bytes (find-relative-path agda f))))

(call-with-output-file all.agda
  (λ (port)
    (fprintf port "module all where\n")
    (for ([agda-file (in-list agda-files)]
          #:unless (equal? agda-file #"all.agda"))
      (fprintf port " open import ~a using ()\n"
               (regexp-replace*
                #rx"/"
                (regexp-replace* #rx"[.]agda$" agda-file "")
                "."))))
  #:exists 'truncate)

(define success?
  (parameterize ([current-directory agda])
    (system "agda --safe all.agda")))
(unless success?
  (raise-user-error 'agda-all.rkt "agda did not complete successfully"))
