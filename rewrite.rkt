#lang racket

(require racket/hash)
(require data/union-find)
(require "conn.rkt")
(require "egraph.rkt")

; to run this, put the update-to-date libsqlite3.0.dylib in the corresponding libraries

(struct pattern (rel vars id) #:transparent)
(struct rewrite (matcher applier) #:transparent)

(define (rw-pat pat)
  (match pat
    [(list (? symbol? R) pats ... '@ (? (or/c false? symbol?) id))
     (let* ([pats (map rw-pat pats)]
            [vars (map (λ (pat)
                         (cond [(symbol? pat) pat]
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
  (query-exec conn create-temp-rel)
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
              (λ (var locs)
                (cons (symbol->string var)
                      (get-loc-string E mat (first locs))))))
  (define schema (string-join (map car schema-select-clause) ", "))
  (define select-clause (string-join (map cdr schema-select-clause) ", "))
  (define query (format
                 "INSERT INTO ~a (~a) SELECT DISTINCT ~a FROM ~a WHERE TRUE ~a;"
                 rw-rel-name
                 schema select-clause
                 from-clause where-clause))
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
    (query-exec conn query))

  (let loop ([pat (get-extendable app)])
    (when pat
      (compute-with-pat pat)
      (set-add! computed (pattern-id pat))
      (loop (get-extendable app)))))

(define (fill-nulls E rw-rel-name rw-var-set)
  (define conn (egraph-conn E))
  (define rw-vars (hash-keys rw-var-set))
  (define num-nulls 0)
  (for ([var (in-list rw-vars)])
    (define field (symbol->string var))
    (define count-query
      (format "SELECT COUNT(*) FROM ~a WHERE ~a IS NULL;" rw-rel-name field))
    (set! num-nulls (+ num-nulls (query-value conn count-query)))
    (define query
      (format "UPDATE ~a SET ~a = next_id(total_changes()) WHERE ~a IS NULL;"
              rw-rel-name field field))
    (query-exec conn query)
    )
  num-nulls)

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
      (format "INSERT OR IGNORE INTO ~a SELECT DISTINCT ~a FROM ~a"
              rel select-clause rw-rel-name))
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
  (define num-nulls (fill-nulls E rw-rel-name rw-var-set))

  (values rw-rel-name num-nulls))

(define (create-parent-table E)
  (define conn (egraph-conn E))
  (define symbols (egraph-symbols E))

  (for* ([(symbol rel-name) symbols]
         ;; [field (cons "eclass" (build-list (cdr symbol) (λ (i) (format "child~a" i))))]
         [field (build-list (cdr symbol) (λ (i) (format "child~a" i)))])
    (query-exec conn
                (string-append "INSERT INTO parent "
                               "SELECT f." field ", COUNT(*) "
                               "FROM " rel-name " f "
                               "GROUP BY f." field)))
  "parent")

(define (delete-from-parent E)
  (define conn (egraph-conn E))
  (query-exec conn "DELETE FROM parent;"))


(define (rebuild E)
  (define conn (egraph-conn E))
  (define ids (make-hash))
  (define id->leader (make-hash))

  ;; (for ([(symbol rel-name) (egraph-symbols E)])
  ;;   (let* ([func (car symbol)]
  ;;          [arity (cdr symbol)
  ;;          [where-clause
  ;;           (string-join
  ;;            (for/list ([i (in-range arity)])
  ;;              (format "AND f1.child~a = f2.child~a" i i)))]
  ;;          [stmt (format
  ;;                 (string-append
  ;;                  "SELECT DISTINCT f1.eclass, f2.eclass "
  ;;                  "FROM ~a f1, ~a f2 "
  ;;                  "WHERE f1.eclass != f2.eclass ~a;")
  ;;                 rel-name rel-name where-clause)]
  ;;          [todos (query-rows conn stmt)])

  ;;     (for ([todo todos])
  ;;       (let* ([a (vector-ref todo 0)]
  ;;              [b (vector-ref todo 1)]
  ;;              [a+ (hash-ref! ids a (thunk (uf-new a)))]
  ;;              [b+ (hash-ref! ids b (thunk (uf-new b)))])
  ;;         (uf-union! a+ b+)))))
  ;; (define num-applied-cong (hash-count ids))

  ;; (let* ([parent-table-name (create-parent-table E)]
  ;;        [select-stmt
  ;;         (string-append "SELECT todo.a, todo.b, TOTAL(p1.t), TOTAL(p2.t) "
  ;;                        "FROM todo "
  ;;                        "LEFT JOIN parent p1 ON todo.a=p1.t "
  ;;                        "LEFT JOIN parent p2 ON todo.b=p2.t "
  ;;                        "GROUP BY todo.a, todo.b")]
  ;;        [delete-stmt "DELETE FROM todo;"])

  ;;   (define max-combo
  ;;     (λ lst (foldr (lambda (a b) (if (> (cdr a)
  ;;                                        (cdr b))
  ;;                                     a b))
  ;;                   (car lst)
  ;;                   (cdr lst))))
  ;;   (for ([(a b pa pb) (in-query conn select-stmt #:fetch 1000)])
  ;;     (let* ([a+ (hash-ref! ids a (thunk (uf-new a)))]
  ;;            [b+ (hash-ref! ids b (thunk (uf-new b)))])
  ;;       (define combo (max-combo (hash-ref id->leader (uf-find a+) (cons a pa))
  ;;                                (hash-ref id->leader (uf-find b+) (cons b pb))
  ;;                                (cons a pa)
  ;;                                (cons b pa)))
  ;;       (uf-union! a+ b+)
  ;;       (hash-set! id->leader (uf-find a+) combo)
  ;;       ))

  ;;   (query-exec conn delete-stmt)
  ;;   (delete-from-parent E))

  (let* ([select-stmt (string-append "SELECT * FROM todo;")]
         [delete-stmt "DELETE FROM todo;"])
    (for ([(a b) (in-query conn select-stmt #:fetch 1000)])
      (let* ([a+ (hash-ref! ids a (thunk (uf-new a)))]
             [b+ (hash-ref! ids b (thunk (uf-new b)))])
        (uf-union! a+ b+)
        (hash-set! id->leader (uf-find a+) (cons (uf-find a+) 0))))

    (query-exec conn delete-stmt))

  ;; (displayln id->leader)
  (define num-applied-cong (hash-count ids))
  (when (not (hash-empty? ids))
    (define cong-rel-name (symbol->string 'ids))
    (define create-stmt
      (format "CREATE TABLE ~a (a INTEGER, b INTEGER);"
              cong-rel-name))
    (query-exec conn create-stmt)

    (define cong-values
      (for/list ([(id id-canon) ids]
                 #:when (not (equal? id
                                     (car (hash-ref id->leader (uf-find id-canon)))))
                 ;; #:when (not (equal? id (uf-find id-canon)))
                 )
        (format "(~a, ~a)" id (car (hash-ref id->leader (uf-find id-canon))))
        ;; (format "(~a, ~a)" id (uf-find id-canon))
        ))
    (when (not (empty? cong-values))
      (define insert-stmt
        (format "INSERT INTO ~a VALUES ~a;" cong-rel-name
                (string-join cong-values ", ")))
      (query-exec conn insert-stmt))

    (for ([(symbol rel-name) (egraph-symbols E)])
      (define (stmt field)
        ;; REPLACE makes sense here because there are
        ;; only two scenarios:
        ;; if this is updating a child, then since we have
        ;; already insert into the todo table correctly, it
        ;; does not matter whether the NEW one or the OLD one persist
        ;; if this is updating an eclass, then we should use
        ;; the replaced one as the eclass, and before that the
        ;; trigger should also have inserted the correct tuples to todo.
        (format (string-append
                 "UPDATE OR REPLACE ~a "
                 "SET ~a = t.b "
                 "FROM ~a t "
                 "WHERE ~a = t.a;")
                rel-name field cong-rel-name field))
      (query-exec conn (stmt "eclass"))
      (for* ([i (in-range (cdr symbol))])
          (query-exec conn (stmt (format "child~a" i)))))

    (drop-table E cong-rel-name)

    (set! num-applied-cong (+ num-applied-cong (rebuild E))))

  num-applied-cong)

(define (run-rw E rws)
  (begin-egraph-transaction E)
  (define num-new-id 0)
  (define rw-rel-names
    (for/list ([rw rws])
      (let* ([mat (rewrite-matcher rw)]
             [app (rewrite-applier rw)])
        (define-values
          (rw-rel-name num-nulls)
          (build-rw-rel E mat app))
        (set! num-new-id (+ num-new-id num-nulls))
        rw-rel-name)))

  (for ([rw-rel-name rw-rel-names]
        [rw rws])
    (define app (rewrite-applier rw))
    (apply-rw-rel E rw-rel-name app)
    (drop-table E rw-rel-name))

  (define num-applied-cong (rebuild E))
  (commit-egraph-transaction E)

  (displayln num-new-id)
  (displayln num-applied-cong)
  (displayln "")
  (not (and (= num-applied-cong 0)
            (= num-new-id 0))))

(define (run-until-fixpoint E rws [iter 0])
  (if (run-rw E rws)
      (run-until-fixpoint E rws (add1 iter))
      iter))

(define (gen-expr n)
  (if (= n 2)
      '(+ (1) (2))
      (list '+ (gen-expr (sub1 n)) (list n))))

(define result
  (for/list ([N (in-range 9 10)])
    (define E (init-egraph))
    (add-symbol! E '+ 2)
    (for ([i (in-range 1 (add1 N))])
      (add-symbol! E i 0))

    (add-s-expr! E (gen-expr N))
    (define r1 (rw-rule ((+ (+ a b) c @ x)) => ((+ a (+ b c) @ x))))
    (define r2 (rw-rule ((+ a b @ x)) => ((+ b a @ x))))
    (time (displayln (run-until-fixpoint E (list r1 r2))))
    (displayln (format "↑ TIME FOR N=~a" N))
    E))
