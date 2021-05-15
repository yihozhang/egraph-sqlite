#lang racket

(require racket/match)
(require db)
(require data/queue)

(struct egraph
  (conn
   symbols
   [num-nodes #:mutable]))

(define literal? (or symbol? number?))

(define (init-egraph)
  (define conn (sqlite3-connect #:database 'memory))
  (define symbols (make-hash))
  (egraph conn symbols 0))

(define (add-symbol! E f arity)
  (define (symbol->rel-name f arity)
    (format "rel_~a_~a" f arity))

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
    (define stmt (if (> arity 0)
                     (string-append
                      "CREATE UNIQUE INDEX " rel-name "_uniq_idx "
                      " ON " rel-name "(" (string-join fields ", ") ");")
                     (string-append
                      "CREATE UNIQUE INDEX " rel-name "_uniq_idx "
                      " ON " rel-name "(eclass);")))
    stmt)

  (define rel-name (symbol->rel-name f arity))
  (define symbols (egraph-symbols E))
  (if (hash-has-key? symbols (cons f arity))
      #f
      (begin
        (hash-set! symbols (cons f arity) rel-name)
        (let ([conn (egraph-conn E)]
              [create-stmt (create-rel-stmt rel-name arity)]
              [uniq-stmt (create-uniq-stmt rel-name arity)])
          (query-exec conn create-stmt)
          (query-exec conn uniq-stmt)
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
     (displayln (format "relation ~a has ~a rows in total\nfirst 10 lines: ~a\n" symbol total content))))
  (displayln (format "~a symbols in total\n" (hash-count (egraph-symbols E)))))

(define (add-node! E node)
  (define num-nodes (egraph-num-nodes E))
  (match node
    [`(,f ,arg-ids ...)
     (let* ([arity (length arg-ids)]
            [conn (egraph-conn E)]
            [symbols (egraph-symbols E)]
            [rel-name (hash-ref symbols (cons f arity))]
            ; TODO: merge them into one query
            [query-stmt (format "SELECT eclass FROM ~a WHERE true ~a;" rel-name
                                (string-join (for/list ([id arg-ids]
                                                        [i (in-naturals)])
                                               (format "AND child~a = ~a" i id))))]
            ; [_ (displayln query-stmt)]
            [id (query-maybe-value conn query-stmt)])
       (or id (let ([insert-stmt (format "INSERT INTO ~a VALUES (~a);" rel-name
                                         (string-join (map number->string (cons num-nodes arg-ids)) ", "))])
                (query-exec conn insert-stmt)
                (set-egraph-num-nodes! E (add1 num-nodes))
                num-nodes)))]
    [c (add-node! E (list c))]))

(define (add-s-expr! E expr)
  (match expr
    [`(,f ,args ...)
     (let ([arg-ids (map (λ (arg) (add-s-expr! E arg)) args)])
       (add-node! E `(,f ,@arg-ids))
       )]
    [c (add-node! E c)]))

(define (merge E class1 class2)
  (define conn (egraph-conn E))
  (define todos (mutable-set (cons class1 class2)))
  (define (do)
    (if (set-empty? todos) #f
        (let* ([todo (set-first todos)]
               [_ (set-remove! todos todo)]
               [class1 (car todo)]
               [class2 (cdr todo)])
          (for ([(symbol rel-name) (egraph-symbols E)])
            (let* ([f (car symbol)]
                   [arity (cdr symbol)]
                   [build-ands (λ (i j)
                                 (if (= i j)
                                     (format "f1.child~a = ~a AND f2.child~a = ~a" j class1 j class2)
                                     (format "f1.child~a = f2.child~a" j j)))]
                   [build-ors (λ (i)
                                (let ([ands (build-list arity (λ (j) (build-ands i j)))])
                                  (string-join ands " AND " #:before-first " OR (" #:after-last ")")))]
                   [ors (build-list arity build-ors)]
                   [pred (string-join ors #:before-first "(FALSE" #:after-last ")")]
                   
                   ; 1. identify new todos
                   [stmt (format "SELECT DISTINCT f1.eclass, f2.eclass FROM ~a f1, ~a f2 WHERE f1.eclass != f2.eclass AND ~a" rel-name rel-name pred)]
                   ; [_ (displayln stmt)]
                   [new-todos (query-rows conn stmt)]
                   [_ (for ([todo new-todos])
                        (define todo+ (cons (vector-ref todo 0) (vector-ref todo 1)))
                        (set-add! todos todo+))]

                   ; 2. delete duplicate rows
                   [stmt (format "DELETE FROM ~a AS f1 WHERE EXISTS (SELECT 1 FROM ~a f2 WHERE ~a)" rel-name rel-name pred)]
                   ; [_ (displayln stmt)]
                   [_ (query-exec conn stmt)]

                   ; 3. change all class1 to class2
                   [_ (for ([col (stream-cons "eclass" (stream-map (λ (i) (format "child~a" i)) (in-range arity)))])
                        (define stmt (format "UPDATE ~a SET ~a = ~a WHERE ~a = ~a" rel-name col class1 col class2))
                        (query-exec conn stmt))]
                   )
              (void))))))
  (do))

(define E (init-egraph))
(show-egraph E)
(add-symbol! E 'f 2)
(add-symbol! E 'g 1)
(add-symbol! E 1 0)
(add-symbol! E 2 0)
(define id1 (add-s-expr! E '(f 1 (g 1))))
(define id2 (add-s-expr! E '(f 1 (g 2))))
(define id3 (add-s-expr! E '(g 1)))
(define id4 (add-s-expr! E '(g 2)))
; relation f should have two rows
(show-egraph E)
(define res (merge E id3 id4))
; after merging (g 1) and (g 2), relation f should
; have only one row thanks to congruence
(show-egraph E)