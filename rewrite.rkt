#lang racket

(require racket/hash)
(require data/union-find)
(require db)
(require "egraph.rkt")

; to run this, put the update-to-date libsqlite3.0.dylib in the corresponding libraries

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

(define (populate-rw-rel-with-mat E rw-rel-name mat mat-var-set)
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
                                    (format "AND ~a = ~a" loc-string loc+-string)))
                   wheres)]
           [lst (flatten (hash-map mat-var-set work))])
      [string-join lst]))
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
        (format "AND rw.~a = f.child~a" (symbol->string var) i)))
    (define where-clause (string-join where-constraints))
    (define query (format "UPDATE ~a AS rw SET ~a = f.eclass FROM ~a f WHERE TRUE ~a;"
                          rw-rel-name dominated rel where-clause))
    (displayln query)
    (query-exec conn query))

  (let loop ([pat (get-extendable app)])
    (when pat
      (compute-with-pat pat)
      (set-add! computed (pattern-id pat))
      (loop (get-extendable app)))))

(define (fill-nulls E rw-rel-name rw-var-set)
  (define conn (egraph-conn E))
  (define rw-vars (hash-keys rw-var-set))
  (for ([var (in-list rw-vars)])
    (define field (symbol->string var))
    (define query (format "UPDATE ~a SET ~a = next_id(total_changes()) WHERE ~a IS NULL;" rw-rel-name field field))
    (displayln query)
    (query-exec conn query)))

(define (drop-table E rel-name)
  (define conn (egraph-conn E))
  (define drop-rel (format "DROP TABLE ~a;" rel-name))
  (query-exec conn drop-rel))

(define (apply-rw-rel E rw-rel-name app)
  (define conn (egraph-conn E))
  (for ([pat app])
    (define rel (get-rel-from-pattern E pat))
    (define id (pattern-id pat))
    (define vars (pattern-vars pat))
    (define select-clause (string-join (map symbol->string (cons id vars)) ", "))
    (define query
      (format "INSERT OR IGNORE INTO ~a SELECT DISTINCT ~a FROM ~a" rel select-clause rw-rel-name))
    (displayln query)
    (query-exec conn query)))

(define (view-table E rel)
  (define conn (egraph-conn E))
  (query-rows conn (format "SELECT * FROM ~a;" rel)))

(define (view-tables E)
  (for/list ([rel-name (hash-values (egraph-symbols E))])
    (view-table E rel-name)))

(define (build-rw-rel E mat app)
  (define mat-var-set (build-var-set mat))
  (define app-var-set (build-var-set app))
  (define rw-var-set (make-hash))
  (hash-union! rw-var-set mat-var-set app-var-set #:combine append)

  (define rw-rel-name (create-temp-table E rw-var-set))
  (populate-rw-rel-with-mat E rw-rel-name mat mat-var-set)
  (chase-rw-rel E rw-rel-name app mat-var-set)
  (fill-nulls E rw-rel-name rw-var-set)
  rw-rel-name)

(define (rebuild E)
  (define conn (egraph-conn E))
  (define ids (make-hash))
  (for ([(symbol rel-name) (egraph-symbols E)])
    (let* ([func (car symbol)]
           [arity (cdr symbol)]
           [where-clause
            (string-join
             (for/list ([i (in-range arity)])
               (format "AND f1.child~a = f2.child~a" i i)))]
           [stmt (format
                  (string-append
                   "SELECT DISTINCT f1.eclass, f2.eclass "
                   "FROM ~a f1, ~a f2 "
                   "WHERE f1.eclass != f2.eclass ~a;")
                  rel-name rel-name where-clause)]
           [_ (displayln stmt)]
           [todos (query-rows conn stmt)])
      
      (for ([todo todos])
        (let* ([a (vector-ref todo 0)]
               [b (vector-ref todo 1)]
               [a+ (hash-ref! ids a (λ () (uf-new a)))]
               [b+ (hash-ref! ids b (λ () (uf-new b)))])
          (uf-union! a+ b+)))))
  (when (not (hash-empty? ids))
    ; TODO we can eliminate the outer loop by store (id, canon-id) to a relation
    (for ([(id id-canon) ids]
          #:when (not (equal? id (uf-find id-canon)))
          [(symbol rel-name) (egraph-symbols E)])
      (query-exec conn (format "UPDATE OR REPLACE ~a SET eclass = ~a WHERE eclass = ~a" rel-name id (uf-find id-canon)))
      (for* ([i (in-range (cdr symbol))])
        (let ([stmt (format ; REPLACE here is important because we use unique constraint to delete duplicate lines
                     "UPDATE OR REPLACE ~a SET child~a = ~a WHERE child~a = ~a"
                     rel-name i (uf-find id-canon) i id)])
          (query-exec conn stmt))))
    (rebuild E)))

(define (run-rw E rws)
  
  (define rw-rel-names
    (for/list ([rw rws])
      (let* ([mat (rewrite-matcher rw)]
             [app (rewrite-applier rw)])
        (build-rw-rel E mat app))))
  (for ([rw-rel-name rw-rel-names]
        [rw rws])
    (define app (rewrite-applier rw))
    (apply-rw-rel E rw-rel-name app)
    (drop-table E rw-rel-name))
  
  (rebuild E))

(define E (init-egraph))
(add-symbol! E '+ 2)
(define N 10)
(for ([i (in-range 0 N)])
  (add-symbol! E i 0))

(add-s-expr! E '(+ (+ (+ (+ (+ (+ (1) (2)) (3)) (4)) (5)) (6)) (7)))
(define r1 (rw-rule ((+ (+ a b) c @ x)) => ((+ a (+ b c) @ x))))
(define r2 (rw-rule ((+ a b @ x)) => ((+ b a @ x))))
(for ([i (in-range 7)])
  (run-rw E (list r1 r2)))
(get-s-expr-id E '(+ (+ (+ (+ (+ (7) (6)) (5)) (4)) (3)) (2)))

; (view-tables E)

; (define conn (egraph-conn E))

;(define rule (rw-rule ((* x y @ c1)
;                       (* z y @ c2))
;                      =>
;                      ((* (concat x z) y @ p)
;                       (fst p @ c1)
;                       (snd p @ c2))))
; (query-rows conn "select sqlite_version();")