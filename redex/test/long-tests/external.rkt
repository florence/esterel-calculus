#lang racket
(require "../model-test.rkt")
(define iterations 100000000000000000)
(do-test #:limits? #f #:count iterations #:debug #f #:external #t #:continue-on-fail? #t #:memory-limits? #t)
