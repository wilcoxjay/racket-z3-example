#lang racket

(require "solver.rkt")

(define (main)
  (solver-init)


  (define a (gensym))

  (printf "a is named ~a\n" a)

  (solver-declare-const a 'Int)
  (solver-declare-const 'b 'Int)

  (solver-assert `(= (+ (* ,a 1) b) 1))
  (solver-assert `(= (+ (* ,a 2) b) 2))
  

  (define res (solver-check-sat))

  (printf "check-sat returned: ~a\n" res)

  (define model (solver-get-model))
  
  (printf "the model is: ~a\n" model))
