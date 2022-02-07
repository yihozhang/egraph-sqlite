#lang racket

(require "./egraph.rkt")

(define E (init-egraph))
; (show-egraph E)
(add-symbol! E '+ 2)
(define N 10)
(for ([i (range 0 N)])
  (add-symbol! E i 0))

(add-s-expr! E '(+ (+ (+ (+ (+ (+ 1 2) 3) 4) 5) 6) 7))
(define r1 (rw-rule ((+ a b)) => ((+ b a))))
(define r2 (rw-rule ((+ a b @ x)) => ((+ b a @ x))))
(displayln (pat->sql E r1))
(displayln (pat->sql E r2))
; get the id of (g 1) and (g 2)
; (define id3 (add-s-expr! E '(g 1)))
; (define id4 (add-s-expr! E '(g 2)))
; relation f should have two rows
; (show-egraph E)
; (define res (merge E id3 id4))
; after merging (g 1) and (g 2), relation f should
; have only one row thanks to congruence
; (show-egraph E)

