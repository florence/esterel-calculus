#lang racket
(provide
 arrow/tag
 strike-for
 (contract-out
  [app
   (-> pict?
       (-> pict? pict?) ...
       pict?)]))
  
(require pict ppict ppict/tag racket/draw)

(define arrow/tag
  (procedure-rename
   (make-keyword-procedure
    (lambda (kws kw-args size src find-src dest find-dest . rest)
      (lambda (pict)
        (keyword-apply
         pin-arrow-line
         kws
         kw-args
         size
         pict
         (if (pict? src) src (find-tag pict src)) find-src
         (if (pict? dest) dest (find-tag pict dest)) find-dest
         rest))))
   'arrow/tag))

(define (app p . f)
  (for/fold ([p p])
            ([f (in-list f)])
    (f p)))

(define strike-for
  (case-lambda
    [(p) (strike-for (pict-width p) (pict-height p))]
    [(w h)
     (strike-for w h 3)]
    [(w h t)
     (strike-for w h t 'tr)]
    [(w h t start)
     (dc
      (lambda (dc dx dy)
        (define old-brush (send dc get-brush))
        (define old-pen (send dc get-pen))
        (send dc set-brush
              (new brush% [style 'fdiagonal-hatch]
                   [color "red"]))
        (send dc set-pen
              (new pen% [width t] [color "red"]))
        (define path (new dc-path%))
        (if (eq? start 'tr)
            (begin
              (send path move-to 0 h)
              (send path line-to w 0))
            (begin
              (send path move-to w h)
              (send path line-to 0 0)))
        (send path close)
        (send dc draw-path path dx dy)
        (send dc set-brush old-brush)
        (send dc set-pen old-pen))
      w h)]))