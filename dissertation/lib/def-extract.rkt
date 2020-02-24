#lang racket
(provide render-def render-file)

(require
  (for-syntax syntax/parse)
  syntax/parse
  racket/runtime-path
  (only-in scribble/manual typeset-code))


(module extract racket
  (provide get-path extract-definition)
  (require
    (for-syntax syntax/parse)
    syntax/parse
    racket/runtime-path
    syntax/modread)
  (define-runtime-module-path circuitous circuitous)
  (define (get-path x)
    (cleanse-path
     (simplify-path (build-path (resolved-module-path-name circuitous) ".." (~a x ".rkt")))))
  (define (extract-definition path name)
    (define mod
      (with-module-reading-parameterization
        (lambda ()
          (parameterize ([port-count-lines-enabled #t])
            (with-input-from-file path read-syntax)))))
    (define x 
      (let loop ([exp mod])
        (syntax-parse exp
          #:datum-literals (define define-unit define-syntax)
          [((~or define-unit define define-syntax) (~or name1:id (name1:id args ...)) body ...)
           #:when (eq? name (syntax-e #'name1))
           exp]
          [(a ...) (ormap loop (syntax->list exp))]
          [_ #f])))
    (unless x
      (error 'extract-definition "could not find definition for ~a in ~a" name path))
    x))

(require (submod "." extract)
         (for-syntax (submod "." extract)))


(define-syntax render-def
  (syntax-parser
    [(_ subpath:id name:id)
     #:do [(define path1 (get-path (syntax-e #'subpath)))]
     #:with path (path->string path1)
     #:with def (extract-definition path1 (syntax-e #'name))
     #:with start (sub1 (syntax-position #'def))
     #:with end (+ (syntax-e #'start) (syntax-span #'def))
     
     #'(typeset-code
        (substring (file->string 'path)
                   'start
                   'end))]))

(define-syntax render-file
  (syntax-parser
    [(_ subpath:id)
     #`(render-filef (get-path 'subpath))]))
(define (render-filef path)
  (typeset-code (file->string path)))


