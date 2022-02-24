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
         commit-egraph-transaction
         get-parent-view-name)

(struct egraph (conn symbols [count #:mutable]))

(define (init-egraph)
  (define conn (sqlite3-connect #:database 'memory))
  (define symbols (make-hash))
  (define E (egraph conn symbols 0))
  (define create-todo-stmt "CREATE TABLE todo (a INTEGER, b INTEGER);")
  (define create-parent-stmt "CREATE TABLE parent (c INTEGER, t INTEGER)")
  (query-exec conn create-todo-stmt)
  (query-exec conn create-parent-stmt)
  (sqlite3-create-function conn "next_id" 1
                           (λ (unused) (let ([count (egraph-count E)])
                                         (set-egraph-count! E (add1 count))
                                         count)))
  E)

(define (get-parent-view-name rel-name)
  (string-append rel-name "_parent "))

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
    (if (= arity 0)
        "SELECT 1;"
        (let* ([fields (build-list arity (λ (i) (format "child~a" i)))]
               [stmt (string-append
                      "CREATE UNIQUE INDEX " rel-name "_uniq_idx "
                      " ON " rel-name "("
                      ; (string-join (cons "eclass" fields) ", ")
                      (string-join fields ", ")
                      ");")])
          stmt)))

  (define (create-idx-stmts rel-name arity)
    (define (stmt field [field-name field])
      (format "CREATE INDEX ~a_~a_idx ON ~a (~a);"
              rel-name field-name rel-name field))
    (define child-idxs
      (for/list ([i arity])
        (stmt (format "child~a" i))))
    (define eclass-idx (stmt "eclass"))
    (cons eclass-idx child-idxs))

  (define (create-trigger-stmt rel-name arity insert?)
    (define op (if insert? "INSERT" "UPDATE"))
    (define select-clause
      (string-join
       (build-list arity (λ (i) (format "AND f.child~a = NEW.child~a" i i)))))
    (define stmt
      (string-append "CREATE TRIGGER trig_" op "_" rel-name " "
                     "BEFORE " op " ON " rel-name " "
                     "BEGIN "
                     "INSERT INTO todo SELECT NEW.eclass, f.eclass "
                     "FROM " rel-name " f "
                     "WHERE NEW.eclass != f.eclass " select-clause " "
                     "LIMIT 1; "
                     "END"))
    stmt)

  (define (create-view-stmt rel-name arity)
    (define (build-stmt field)
      (string-append "SELECT f." field ", count(*) "
                     "FROM " rel-name " f "
                     "GROUP BY f." field))

    (define select-clause
      (string-join
       (cons (build-stmt "eclass")
             (build-list arity
                         (λ (i) (build-stmt (format "child~a" i)))))
       " UNION ALL "))
    (string-append "CREATE VIEW " (get-parent-view-name rel-name)
                     "(c, t) AS " select-clause))

  ;; (define (create-update-parent-stmts rel-name arity)
  ;;   (define (stmt field)
  ;;     (string-append "CREATE TRIGGER trig_update_" rel-name "_" field "_parent "
  ;;                    "BEFORE UPDATE OF " field " ON " rel-name " "
  ;;                    "BEGIN "
  ;;                    "INSERT INTO parent SELECT NEW." field ", 0 "
  ;;                    "WHERE NOT EXISTS "
  ;;                    "(SELECT 1 FROM parent WHERE c = NEW." field "); "
  ;;                    "UPDATE parent SET t = t + 1 WHERE c = NEW." field "; "
  ;;                    "UPDATE parent SET t = t - 1 WHERE c = OLD." field "; "
  ;;                    "END"))
  ;;   (cons (stmt "eclass")
  ;;         (build-list arity (λ (i) (stmt (format "child~a" i))))))

  ;; (define (create-insert-parent-stmt rel-name arity)
  ;;   (define (build-stmt field)
  ;;     (string-append "INSERT INTO parent SELECT NEW." field ", 0 "
  ;;                    "WHERE NOT EXISTS "
  ;;                    "(SELECT 1 FROM parent WHERE c = NEW." field "); "
  ;;                    "UPDATE parent SET t = t + 1 WHERE c = NEW." field "; "))
  ;;   (define insert-stmts
  ;;     (string-join (cons (build-stmt "eclass")
  ;;                        (build-list arity
  ;;                                    (λ (i) (build-stmt (format "child~a" i)))))))
  ;;   (string-append "CREATE TRIGGER trig_insert_" rel-name "_parent "
  ;;                  "BEFORE INSERT ON " rel-name " "
  ;;                  "BEGIN "
  ;;                  insert-stmts
  ;;                  "END "))

  (define rel-name (next-rel-name))
  (define symbols (egraph-symbols E))
  (if (hash-has-key? symbols (cons f arity))
      #f
      (begin
        (hash-set! symbols (cons f arity) rel-name)
        (let ([conn (egraph-conn E)]
              [create-stmt (create-rel-stmt rel-name arity)]
              [uniq-stmt (create-uniq-stmt rel-name arity)]
              [idx-stmts (create-idx-stmts rel-name arity)]
              [insert-trigger-stmt (create-trigger-stmt rel-name arity #t)]
              [update-trigger-stmt (create-trigger-stmt rel-name arity #f)]
              ;; [insert-parent-stmt (create-insert-parent-stmt rel-name arity)]
              ;; [update-parent-stmts (create-update-parent-stmts rel-name arity)]
              ;; [view-stmt (create-view-stmt rel-name arity)]
              )
          (query-exec conn create-stmt)
          (query-exec conn uniq-stmt)
          (for ([stmt idx-stmts]) (query-exec conn stmt))

          (query-exec conn insert-trigger-stmt)
          (query-exec conn update-trigger-stmt)

          ;; (query-exec conn insert-parent-stmt)
          ;; (for ([stmt update-parent-stmts]) (query-exec conn stmt))

          ;; (query-exec conn view-stmt)
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
