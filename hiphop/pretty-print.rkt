#lang racket

(require esterel-calculus/hiphop/find)
(provide pretty-print)

; path-string? -> string?
; Pretty-prints the given test using the hiphop.js pretty printer.
(define (pretty-print file-or-test)
  (define batch-file (make-temporary-file "pretty-print-~a.js"))
  (define file (path-replace-extension file-or-test ".js"))
  (with-output-to-file batch-file
    (λ ()
      (displayln "\"use hopscript\"")
      (displayln "\"use strict\"")
      (displayln (format "let test = require(\"~a\");" file))
      (displayln "console.log(test.prg.pretty_print());"))
    #:exists 'truncate)
  (define out (open-output-string))
  (define err (open-output-string))
  (parameterize ([current-output-port out]
                 [current-error-port err])
    (system* (hop-binary-path)
             "--no-server" "--no-sofile" "-q"
             "-I" (hiphop-lib-directory) "-I" (hiphop-test-directory)
             batch-file))
  (delete-file batch-file)
  (get-output-string out))
