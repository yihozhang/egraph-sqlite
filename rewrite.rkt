#lang racket
; to run this, put the update-to-date libsqlite3.0.dylib in the corresponding libraries
(require racket/hash)
(require db)
(require "egraph.rkt")

(struct pattern (rel vars id) #:transparent)
(struct rewrite (matcher applier) #:transparent)

(define (rw-pat pat)
  (match pat
    [(list (? symbol? R) pats ... '@ (? (or/c false? symbol?) id))
     (let* ([pats (map rw-pat pats)]
            [vars (map (λ (pat) (cond [(symbol? pat) pat]
                                      [((listof pattern?) pat) (pattern-id (first pat))]))
                       pats)])
       (cons (pattern R vars id) (flatten (filter (listof pattern?) pats))))]
    [(list R pats ...) (rw-pat `(,R ,@pats @ ,(gensym 'x)))]
    [(? symbol? x) x]))

(define-syntax rw-rule
  (syntax-rules (=>)
    [(rw-rule (mat ...) => (app ...))
     (rewrite (flatten (list (rw-pat (quote mat)) ...))
              (flatten (list (rw-pat (quote app)) ...)))]))

(define (build-var-set pats)
  (define var-set (make-hash))
  (define (update-var-set! var f) (hash-update! var-set var f '()))
  (for ([pat (in-list pats)]
        [i (in-naturals)])
    (let ([id (pattern-id pat)]
          [vars (pattern-vars pat)])
      (update-var-set! id (λ (vars) (cons (cons i #f) vars)))
      (for ([var (in-list vars)]
            [j (in-naturals)])
        (update-var-set! var (λ (vars) (cons (cons i j) vars))))))
  var-set)

; map each var to a set of (rel-loc, field-loc or #f, which stands for e-class)
(define (get-loc-string E pats loc)
  (let* ([i (car loc)]
         [j (cdr loc)]
         ; [pat (list-ref pats i)]
         ; [func (pattern-rel pat)]
         ; [arity (length (pattern-vars (list-ref pats i)))]
         ; [table-name (hash-ref (egraph-symbols E) (cons func arity))]
         [table-name (format "f~a" i)]
         [field-name (if j (format "child~a" j) "eclass")])
    (string-append table-name "." field-name)))

(define (create-temp-table E var-set)
  (define conn (egraph-conn E))
  (define vars (hash-keys var-set))
  (define temp-rel-name (symbol->string (gensym "rel")))
  (define fields (string-join
                  (map (λ (var) (string-append (symbol->string var) " INTEGER")) vars)
                  ", "))
  
  (define create-temp-rel (format "CREATE TEMP TABLE ~a (~a);" temp-rel-name fields))
  ; (query-exec conn create-temp-rel)
  (query-exec conn create-temp-rel)
  (displayln create-temp-rel)
  temp-rel-name)

(define (populate-rw-rel-with-mat E rw-rel-name mat mat-var-set var-set)
  (define conn (egraph-conn E))
  (define from-clause
    (let ([lst (for/list ([pat (in-list mat)]
                         [i (in-naturals)])
                (define rel (get-rel-from-pattern E pat))
                (format "~a f~a" rel i))])
      (string-join lst ", ")))
    
  (define where-clause
    (let* ([work (λ (var locs)
                   (define loc (car locs))
                   (define loc-string (get-loc-string E mat loc))
                   (define locs+ (cdr locs))
                   (define wheres (for/list ([loc+ (in-list locs+)])
                                    (define loc+-string (get-loc-string E mat loc+))
                                    (format "~a = ~a" loc-string loc+-string)))
                   wheres)]
           [lst (flatten (hash-map mat-var-set work))])
      [string-join lst " AND "  #:before-first "AND "]))
  (define schema-select-clause
    (hash-map mat-var-set
              (λ (var locs) (cons (symbol->string var) (get-loc-string E mat (first locs))))))
  (define schema (string-join (map car schema-select-clause) ", "))
  (define select-clause (string-join (map cdr schema-select-clause) ", "))
  (define query (format "INSERT INTO ~a (~a) SELECT DISTINCT ~a FROM ~a WHERE TRUE ~a;"
                          rw-rel-name
                          schema select-clause
                          from-clause where-clause))
  (displayln query)
  (query-exec conn query))
;  (for ([pat app])
;    (let* ([rel (pattern-rel pat)]
;           [vars (pattern-vars pat)]
;           [id (pattern-id pat)]
;           [var->field (λ (var) (get-loc-string (first (hash-ref mat-var-set var))))]
;           [eclass (var->field id)]
;           [fields (map var->field vars)]
;           [select-clause (string-join (cons eclass fields) ", ")]
;           )
;      (displayln query)))

(define (get-rel-from-pattern E pat)
  (hash-ref (egraph-symbols E)
            (cons (pattern-rel pat) (length (pattern-vars pat)))))

(define (chase-rw-rel E rw-rel-name app mat-var-set)
  (define conn (egraph-conn E))
  (define computed (list->mutable-set (hash-keys mat-var-set)))
  
  (define (can-extend? pat)
    (and (andmap (λ (var) (set-member? computed var)) (pattern-vars pat))
         (not (set-member? computed (pattern-id pat)))))

  (define (get-extendable pats)
    (if (empty? pats) #f
        (if (can-extend? (car pats))
            (car pats)
            (get-extendable (cdr pats)))))

  (define (compute-with-pat pat)
    (define dominated (pattern-id pat))
    (define rel (get-rel-from-pattern E pat))
    ; rw.{var} = f.child{i}
    (define where-constraints 
       (for/list ([var (in-list (pattern-vars pat))]
                  [i (in-naturals)])
         (format "rw.~a = f.child~a" (symbol->string var) i)))
    (define where-clause (string-join where-constraints " AND " #:before-first "AND "))
    (define query (format "UPDATE ~a AS rw SET ~a = f.eclass FROM ~a f WHERE TRUE ~a"
            rw-rel-name dominated rel where-clause))
    (displayln query)
    (query-exec conn query))

  (displayln computed)
  (displayln app)
  (let loop ([pat (get-extendable app)])
    (when pat
      (compute-with-pat pat)
      (set-add! computed (pattern-id pat))
      (loop (get-extendable app)))))
  
(define (drop-table E rel-name)
  (define conn (egraph-conn E))
  (define drop-rel (format "DROP TABLE ~a;" drop-rel))
  (query-exec conn drop-rel))

(define (pat->sql E rw)
  (define mat (rewrite-matcher rw))
  (define app (rewrite-applier rw))
  
  (define mat-var-set (build-var-set mat))
  (define app-var-set (build-var-set app))
  (define rw-var-set (make-hash))
  (hash-union! rw-var-set mat-var-set app-var-set #:combine append)

  (define rw-rel-name (create-temp-table E rw-var-set))
  (populate-rw-rel-with-mat E rw-rel-name mat mat-var-set rw-var-set)
  (chase-rw-rel E rw-rel-name app mat-var-set)
  )

(define E (init-egraph))
; (show-egraph E)
(add-symbol! E '+ 2)
(define N 10)
(for ([i (in-range 0 N)])
  (add-symbol! E i 0))

(define r (rw-rule ((+ a (+ b c) @ x)) => ((+ (+ a b) c @ x))))
(displayln (pat->sql E r))

(define conn (egraph-conn E))
; (query-rows conn "select sqlite_version();")