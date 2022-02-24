#lang racket

(require "./egraph.rkt")

(define E (init-egraph))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (datatype expr                                          ;;
;;   (Num int)                                             ;;
;;   (Var int)                                             ;;
;;   (Neg expr)                                            ;;
(add-symbol! E 'neg 1)
;;   (Abs expr)                                            ;;
(add-symbol! E 'abs 1)
;;   (Add expr expr)                                       ;;
(add-symbol! E 'add 2)
;;   (Sub expr expr)                                       ;;
(add-symbol! E 'sub 2)
;;   (Mul expr expr)                                       ;;
(add-symbol! E 'mul 2)
;;   (Div expr expr))                                      ;;
(add-symbol! E 'div 2)

;; # evaluation rules                                      ;;
;; (eq                                                     ;;
;;   (Neg (Num ?i))                                        ;;
;;   (Num [~ ?i]))                                         ;;
(rw-rule ((neg (num i) @ a)) =>
         ((num ,(- i) @ a)))
;; (eq                                                     ;;
;;   (Abs (Num ?i))                                        ;;
;;   (Num [abs ?i]))                                       ;;
(rw-rule ((abs (num i) @ a)) =>
         ((num ,(abs i) @ a)))
;; (eq                                                     ;;
;;   (Add (Num ?i1) (Num ?i2))                             ;;
;;   (Num [+ ?i1 ?i2]))                                    ;;
(rw-rule ((add (num i1) (num i2) @ a)) =>
         ((num ,(+ i1 i2) @ a)))
;; (eq                                                     ;;
;;   (Sub (Num ?i1) (Num ?i2))                             ;;
;;   (Num [- ?i1 ?i2]))                                    ;;
(rw-rule ((sub (num i1) (num i2) @ a)) =>
         ((num ,(- i1 i2) @ a)))
;; (eq                                                     ;;
;;   (Mul (Num ?i1) (Num ?i2))                             ;;
;;   (Num [* ?i1 ?i2]))                                    ;;
(rw-rule ((mul (num i1) (num i2) @ a)) =>
         ((num ,(* i1 i2) @ a)))
;; (rule (                                                 ;;
;;   (eq ?a (Div (Num ?i1) (Num ?i2)))                     ;;
;;   (<> ?i2 0) # guard Div eval                           ;;
;; )(                                                      ;;
;;   (eq ?a (Num [/ ?i1 ?i2])))                            ;;
;; ))                                                      ;;
(rw-rule ((div (num i1) (num i2) @ a)
          ,(not (equal? i2 0))) =>
         ((num ,(- i1 i2) @ a)))

;; # syntactic rewrites                                    ;;
;; (eq                                                     ;;
;;   (Neg (Neg ?x))                                        ;;
;;   ?x)                                                   ;;
(rw-rule ((neg (neg x) @ a)) =>
         ((neg (neg x) @ x)))
;; (eq                                                     ;;
;;   (Abs (Abs ?x))                                        ;;
;;   (Abs ?x))                                             ;;
(rw-rule ((abs (abs x) @ a)) =>
         ((abs x @ a)))
;; (eq                                                     ;;
;;   (Abs (Neg ?x))                                        ;;
;;   (Abs ?x))                                             ;;
(rw-rule ((abs (neg x) @ a)) =>
         ((abs x @ a)))
;; (eq                                                     ;;
;;   (Add ?x (Num 0))                                      ;;
;;   ?x)                                                   ;;
;; (eq                                                     ;;
;;   (Add ?x ?y)                                           ;;
;;   (Add ?y ?x))                                          ;;
;; (eq                                                     ;;
;;   (Add (Add ?x ?y) ?z)                                  ;;
;;   (Add ?x (Add ?y ?z)))                                 ;;
;; (eq                                                     ;;
;;   (Sub ?x (Num 0))                                      ;;
;;   ?x)                                                   ;;
;; (eq                                                     ;;
;;   (Sub ?x ?x)                                           ;;
;;   (Num 0))                                              ;;
;; (eq                                                     ;;
;;   (Sub ?x ?y)                                           ;;
;;   (Add ?x (Neg ?y)))                                    ;;
;; (eq                                                     ;;
;;   (Mul ?x (Num 0))                                      ;;
;;   (Num 0))                                              ;;
;; (eq                                                     ;;
;;   (Mul ?x (Num 1))                                      ;;
;;   ?x)                                                   ;;
;; (eq                                                     ;;
;;   (Mul ?x ?y)                                           ;;
;;   (Mul ?y ?x))                                          ;;
;; (eq                                                     ;;
;;   (Mul (Mul ?x ?y) ?z)                                  ;;
;;   (Mul ?x (Mul ?y ?z)))                                 ;;
;; (eq                                                     ;;
;;   (Mul ?x (Add ?y ?z))                                  ;;
;;   (Add (Mul ?x ?y) (Mul ?x ?z)))                        ;;
;; (eq                                                     ;;
;;   (Div ?x (Num 1))                                      ;;
;;   ?x)                                                   ;;
;;                                                         ;;
;;                                                         ;;

;; (symmetric-relation not_eq                              ;;
;;   (type (Expr Expr)))                                   ;;
(add-symbol E 'not-eq 2)
(add-symbol E 'PANIC 1)
;; # following rule implicit b/c symrel                    ;;
;; # (rule (                                               ;;
;; #   (not_eq ?a ?b)                                      ;;
;; # )(                                                    ;;
;; #   (not_eq ?b ?a)                                      ;;
;; # ))                                                    ;;
(rw-rule ((not-eq a b)) =>
         ((not-eq b a)))

;; # check expected invariant                              ;;
;; (rule (                                                 ;;
;;   (not_eq ?a ?a)                                        ;;
;; )(                                                      ;;
;;   (PANIC ?a)                                            ;;
;; ))                                                      ;;
(rw-rule ((not-eq a a)) =>
         ((PANIC a)))

;; # "Int+" is "extended integers", i.e., Z U {-inf, inf}  ;;
;; (functions                                              ;;
;;   (lo                                                   ;;
;;     (type (Expr) Int+)                                  ;;
;;     (merge (a b)                                        ;;
;;       (max (lo a) (lo b)))                              ;;
;;     (lo (e)                                             ;;
;;       (case e                                           ;;
;;         ((Num ?i)                                       ;;
;;           ?i)                                           ;;
;;         ((Var _)                                        ;;
;;           -inf)                                         ;;
;;         ((Neg ?x)                                       ;;
;;           (~ (hi ?x)))                                  ;;
;;         ((Abs ?x)                                       ;;
;;           (if (<= 0 (lo ?x))                            ;;
;;             (lo ?x)                                     ;;
;;             (if (<= 0 (hi ?x))                          ;;
;;               0                                         ;;
;;               (~ (hi ?x)))))                            ;;
;;         ((Add ?x ?y)                                    ;;
;;           (+ (lo ?x) (lo ?y)))                          ;;
;;         ((Sub ?x ?y)                                    ;;
;;           (- (lo ?x) (hi ?y)))                          ;;
;;         ((Mul ?x ?y)                                    ;;
;;           (min                                          ;;
;;             (* (lo ?x) (lo ?y))                         ;;
;;             (* (lo ?x) (hi ?y))                         ;;
;;             (* (hi ?x) (lo ?y))                         ;;
;;             (* (hi ?x) (hi ?y))))                       ;;
;;         ((Div ?x ?y)                                    ;;
;;           ...))))                                       ;;
;;   (hi                                                   ;;
;;     (type (Expr) Int+)                                  ;;
;;     (merge (a b)                                        ;;
;;       (min (hi a) (hi b)))                              ;;
;;     (hi (e)                                             ;;
;;       (case e                                           ;;
;;         ((Num ?i)                                       ;;
;;           ?i)                                           ;;
;;         ((Var _)                                        ;;
;;           inf)                                          ;;
;;         ((Neg ?x)                                       ;;
;;           (~ (lo ?x)))                                  ;;
;;         ((Abs ?x)                                       ;;
;;           (max (Abs (lo ?x)) (Abs (hi ?x))))            ;;
;;         ((Add ?x ?y)                                    ;;
;;           (+ (hi ?x) (hi ?y)))                          ;;
;;         ((Sub ?x ?y)                                    ;;
;;           (- (hi ?x) (lo ?y)))                          ;;
;;         ((Mul ?x ?y)                                    ;;
;;           (max                                          ;;
;;             (* (lo ?x) (lo ?y))                         ;;
;;             (* (lo ?x) (hi ?y))                         ;;
;;             (* (hi ?x) (lo ?y))                         ;;
;;             (* (hi ?x) (hi ?y))))                       ;;
;;         ((Div ?x ?y)                                    ;;
;;           ...)))))                                      ;;
;;                                                         ;;
;; # check expected invariant                              ;;
;; (rule (                                                 ;;
;;   (< (hi ?a) (lo ?a))                                   ;;
;; )(                                                      ;;
;;   (PANIC ?a)                                            ;;
;; ))                                                      ;;
;;                                                         ;;
;;                                                         ;;
;; # if intervals do not overlap, expressions cannot be eq ;;
;; (rule (                                                 ;;
;;   (< (hi ?a) (lo ?b))                                   ;;
;; )(                                                      ;;
;;   (not_eq ?a ?b)                                        ;;
;; ))                                                      ;;
;;                                                         ;;
;;                                                         ;;
;; # conditional rules                                     ;;
;; (rule (                                                 ;;
;;   (eq ?a (Div ?x ?x))                                   ;;
;;   (not_eq ?x (Num 0))                                   ;;
;; )(                                                      ;;
;;   (eq ?a (Num 1))                                       ;;
;; ))                                                      ;;
;;                                                         ;;
;;                                                         ;;
;; # injectivity rules                                     ;;
;; (rule (                                                 ;;
;;   (eq (Add ?x ?y) (Add ?x ?z))                          ;;
;; )(                                                      ;;
;;   (eq ?y ?z)                                            ;;
;; ))                                                      ;;
;;                                                         ;;
;; (rule (                                                 ;;
;;   # "merge only"                                        ;;
;;   (eq ?a (Add ?x ?y))                                   ;;
;;   (eq ?b (Add ?x ?z))                                   ;;
;;   (not_eq ?y ?z)                                        ;;
;; )(                                                      ;;
;;   (not_eq ?a ?b)                                        ;;
;; ))                                                      ;;
;;                                                         ;;
;; (rule (                                                 ;;
;;   (eq (Mul ?x ?y) (Mul ?x ?z))                          ;;
;;   (not_eq ?x (Num 0))                                   ;;
;; )(                                                      ;;
;;   (eq ?y ?z)                                            ;;
;; ))                                                      ;;
;;                                                         ;;
;; (rule (                                                 ;;
;;   # "merge only"                                        ;;
;;   (eq ?a (Mul ?x ?y))                                   ;;
;;   (eq ?b (Mul ?x ?z))                                   ;;
;;   (not_eq ?y ?z)                                        ;;
;;   (not_eq ?x (Num 0))                                   ;;
;; )(                                                      ;;
;;   (not_eq ?a ?b)                                        ;;
;; ))                                                      ;;
;;                                                         ;;
;;                                                         ;;
;; # add something and run eqsat                           ;;
;; (define root (ADD                                       ;;
;;   # like quadratic, but not sqrt                        ;;
;;   (Div (Add (Neg b) (Sub (Mul b b) (Mul 4 (Mul a c))))  ;;
;;        (Mul 2 a))))                                     ;;
;; (run (iters 5))                                         ;;
;;                                                         ;;
;;                                                         ;;
;; # extract                                               ;;
;; (function cost                                          ;;
;;   (type (Expr) Int)                                     ;;
;;   (merge (a b)                                          ;;
;;     (min (cost a) (cost b)))                            ;;
;;   (cost (e)                                             ;;
;;     (case e                                             ;;
;;       ((Num _) 1)                                       ;;
;;       ((Var _) 2)                                       ;;
;;       ((Neg ?x)                                         ;;
;;         (+ 3 (cost ?x)))                                ;;
;;       ((Abs ?x)                                         ;;
;;         (+ 4 (cost ?x)))                                ;;
;;       ((Add ?x ?y)                                      ;;
;;         (+ 5 (cost ?x) (cost ?y)))                      ;;
;;       ((Sub ?x ?y)                                      ;;
;;         (+ 6 (cost ?x) (cost ?y)))                      ;;
;;       ((Mul ?x ?y)                                      ;;
;;         (+ 7 (cost ?x) (cost ?y)))                      ;;
;;       ((Div ?x ?y)                                      ;;
;;         (+ 8 (cost ?x) (cost ?y))))))                   ;;
;;                                                         ;;
;; (extract cost root)                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
