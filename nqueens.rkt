#lang racket

(require "solver.rkt")

(define (nqueens n)
  (define (row i) (symbol-append 'row (string->symbol (number->string i))))

  (for ([i (in-range n)])
    (let ([r (row i)])
      (solver-declare-const r 'Int)
      (solver-assert `(and (<= 0 ,r) (< ,r ,n)))))

  (solver-assert
   `(distinct ,@(for/list ([i (in-range n)]) (row i))))

  (for* ([i (in-range n)]
         [j (in-range i)])
    (solver-assert `(not (= (- ,(row i) ,(row j)) ,(- i j))))
    (solver-assert `(not (= (- ,(row i) ,(row j)) ,(- j i)))))

  (define ans (solver-check-sat))
  (match ans
    ['sat
     (define board
       (for/list ([i (in-range n)])
         (solver-eval (row i))))
     (print-board board)]))

(define (print-board board )
  (define n (length board))
  (for ([row board])
    (for ([col (in-range row)])
      (display "."))
    (display "*")
    (for ([col (in-range (+ 1 row) n)])
      (display "."))
    (display "\n")))

(define (main)
  (solver-init)
  (nqueens 4)
  (pretty-print (solver-get-stack)))
