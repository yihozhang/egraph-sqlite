#lang racket
(require (rename-in db (query-exec old-query-exec)))
(require db/unsafe/sqlite3)

(provide
    (except-out (all-from-out db) old-query-exec)
    (all-from-out db/unsafe/sqlite3)
    query-exec)

(define (query-exec conn stmt)
  ;; (displayln stmt)
  (old-query-exec conn stmt))
