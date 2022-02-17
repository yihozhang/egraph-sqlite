#lang racket

(require racket/match)
(require data/queue)
(require data/union-find)
(require data/gvector)
(require "conn.rkt")

(provide init-egraph add-symbol!
         add-node! add-s-expr!
         get-node-id get-s-expr-id
         show-egraph
         egraph-num-nodes
         egraph-symbols
         egraph-conn
         begin-egraph-transaction
         commit-egraph-transaction)

(struct egraph (conn symbols [count #:mutable]))

(define (init-egraph)
  (define conn (sqlite3-connect #:database 'memory))
  (define symbols (make-hash))
  (define E (egraph conn symbols 0))
  (sqlite3-create-function conn "next_id" 1
                           (λ (unused) (let ([count (egraph-count E)])
                                         (set-egraph-count! E (add1 count))
                                         count)))
  E)

(define (add-symbol! E f arity)
  (define (next-rel-name)
    (format "rel_~a" (hash-count (egraph-symbols E))))

  (define (create-rel-stmt rel-name arity)
    (define fields (cons "eclass INTEGER"
                         (build-list arity (λ (i)
                                             (format "child~a INTEGER" i)))))
    (define stmt (string-append
                  "CREATE TABLE " rel-name "("
                  (string-join fields ", ") ");"))
    stmt)

  (define (create-uniq-stmt rel-name arity)
    (define fields (build-list arity (λ (i) (format "child~a" i))))
    (define stmt
      (string-append
       "CREATE UNIQUE INDEX " rel-name "_uniq_idx "
       " ON " rel-name "(" (string-join (cons "eclass" fields) ", ") ");"))
    stmt)

  (define (create-idx-stmts rel-name arity)
    (define (stmt field [field-name field])
      (format "CREATE INDEX ~a_~a_idx ON ~a (~a);"
              rel-name field-name rel-name field))
    (define child-idxs
      (for/list ([i arity])
        (stmt (format "child~a" i))))
    (define class-idx (stmt "eclass"))
    (define all-child-idx
      (stmt (string-join
             (build-list arity (λ (i) (format "child~a" i)))
             ", ")
            "all_child"))
    (define stmts
      (if (= arity 0)
          (cons class-idx child-idxs)
          (cons all-child-idx (cons class-idx child-idxs))))
    stmts)

  (define rel-name (next-rel-name))
  (define symbols (egraph-symbols E))
  (if (hash-has-key? symbols (cons f arity))
      #f
      (begin
        (hash-set! symbols (cons f arity) rel-name)
        (let ([conn (egraph-conn E)]
              [create-stmt (create-rel-stmt rel-name arity)]
              [uniq-stmt (create-uniq-stmt rel-name arity)]
              [idx-stmts (create-idx-stmts rel-name arity)])
          (displayln idx-stmts)
          (query-exec conn create-stmt)
          (query-exec conn uniq-stmt)
          ; (for ([idx-stmt idx-stmts]) (query-exec conn idx-stmt))
          #t))))

(define (show-egraph E)
  (hash-for-each
   (egraph-symbols E)
   (λ (symbol rel-name)
     (define select-stmt
       (string-append "SELECT * FROM " rel-name " LIMIT 10;"))
     (define count-stmt
       (string-append "SELECT count(*) FROM " rel-name ";"))
     (define content (query-rows (egraph-conn E) select-stmt))
     (define total (query-value (egraph-conn E) count-stmt))
     (displayln
      (format
       "relation ~a has ~a rows in total\nfirst 10 lines: ~a\n"
       symbol total content))))
  (displayln (format "~a symbols in total\n" (hash-count (egraph-symbols E)))))

(define (egraph-num-nodes E)
  ; TODO: this is inaccurate (due to congruence)
  (egraph-count E))

(define (get-node-id E node)
  (let* ([f (car node)]
         [arg-ids (cdr node)]
         [arity (length arg-ids)]
         [conn (egraph-conn E)]
         [symbols (egraph-symbols E)]
         [rel-name (hash-ref symbols (cons f arity))]
         [query-stmt (format "SELECT eclass FROM ~a WHERE true ~a;" rel-name
                             (string-join
                              (for/list ([id (in-list arg-ids)]
                                         [i (in-naturals)])
                                (format "AND child~a = ~a" i id))))])
    (query-maybe-value conn query-stmt)))

(define (get-s-expr-id E expr)
  (match expr
    [`(,f ,args ...)
     (define arg-ids
       (foldr (λ (arg lst)
                (and lst ; return lst if lst is #f
                     (let ([id (get-s-expr-id E arg)])
                       (and id (cons id lst))))) ; return id if id is #f
              '() args))
     (and arg-ids (get-node-id E `(,f ,@arg-ids)))]))

(define (add-node! E node)
  (or (get-node-id E node) ; return if get-node-id return non-#f value
      (let* ([f (car node)]
             [arg-ids (cdr node)]
             [arity (length arg-ids)]
             [conn (egraph-conn E)]
             [symbols (egraph-symbols E)]
             [rel-name (hash-ref symbols (cons f arity))]
             [num-nodes (egraph-num-nodes E)]
             [args (map number->string (cons num-nodes arg-ids))]
             [insert-stmt (format "INSERT INTO ~a VALUES (~a);" rel-name
                                  (string-join args ", "))])
        (query-exec conn insert-stmt)
        (set-egraph-count! E (add1 num-nodes))
        num-nodes)))

(define (add-s-expr! E expr)
  (match expr
    [`(,f ,args ...)
     (let ([arg-ids (map (λ (arg) (add-s-expr! E arg)) args)])
       (add-node! E `(,f ,@arg-ids)))]))

(define (begin-egraph-transaction E)
  (define conn (egraph-conn E))
  (start-transaction conn))

(define (commit-egraph-transaction E)
  (define conn (egraph-conn E))
  (commit-transaction conn))
