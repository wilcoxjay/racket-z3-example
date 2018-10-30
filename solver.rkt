#lang racket

;; A simple Racket interface to Z3, adapted from the labs of Emina Torlak's
;; 2014 graduate offerring of "Computer-Aided Reasoning for Software".
;; Additional modifications by Konstantin Weitz, Doug Woos, and James Wilcox

;; The basic premise of this interface is that Z3's SMTLIB-2 format is based on
;; S-expressions, and Racket is really good at S-expressions. So, for the most part
;; the interface is very thin and just lets you send S-expressions to Z3.
;;
;; It provides some wrapper functions for the main operations, but at the end of the day
;; you can call solver-write-raw with an S-expression, which will be sent directly to Z3.

(require racket/runtime-path racket/path)

(provide z3 z3-log?
         symbol-append
         solver-init
         solver-write-raw
         solver-write-success
         solver-write-with-result
         solver-flush
         solver-read
         solver-set-option
         solver-check-sat solver-get-model
         solver-declare-sort solver-declare-fun solver-declare-const
         solver-push solver-pop solver-dont-pop!
         solver-label
         solver-and solver-and*
         solver-or solver-or*
         solver-not
         solver-assert
         solver-assert-skolemize
         solver-eval
         solver-get-assertions
         solver-get-unsat-core
         solver-get-stack
         )

(define z3 (make-parameter (find-executable-path "z3")))

(define-values (solver-process solver-out solver-in solver-err)
  (values (void) (void) (void) (void)))

; A racket-side log of the current commands on Z3's assertion stack.
; Useful for debugging when turning on logging would be too much.
(define solver-stack (void))

(define actually-pop? (void))

; Start the Z3 process. This function must be called before any other in this library.
; Clients should set further options immediately after calling solver-init by
; using solver-set-option (see below).
(define (solver-init)
  (set!-values (solver-process solver-out solver-in solver-err)
               (subprocess #f #f #f (z3) "-smt2" "-in"))
  (set! solver-stack '(()))
  (set! actually-pop? #t)
  (solver-set-option ':print-success 'true))

(define symbol-append
  (λ l (string->symbol (apply string-append (map symbol->string l)))))

; If true, log everything sent to Z3. Useful with parametrize to only log parts of the session.
(define z3-log? (make-parameter false))

; Write the given S-expression to Z3, logging if desired. Everything else in the library uses this.
(define (solver-write-raw expr)
  (when (void? solver-in)
    (error "initialize the solver by calling (solver-init) first"))
  (when (z3-log?)
    (printf "~a\n" expr))
  (fprintf solver-in "~a\n" expr))

; Read one S-expression from Z3.
(define (solver-read)
  (read solver-out))

(define (solver-flush)
  (flush-output solver-in))

; Write an S-expression to Z3 representing a command that returns success-or-error. Expect success and return nothing.
(define (solver-write-success expr)
  (solver-write-raw expr)
  (solver-flush)
  (match (solver-read)
    ('success (void))))

; Several commands that return success-or-error have a side effect on the assertion stack.
; We record these effects on solver-stack for debugging

; Push an S-expression onto the top frame of the solver-stack
(define (solver-stack-push expr)
  (set! solver-stack
        (cons (cons expr (car solver-stack))
              (cdr solver-stack))))

(define (solver-get-stack)
  (reverse (map reverse solver-stack)))

; Log a command that pushes an assertion or declaration onto Z3's stack.
(define (solver-log-success expr)
  (solver-stack-push expr)
  (solver-write-success expr))

; Thin wrapper around Z3's (push). Record a fresh frame on the debug stack.
(define (solver-push [n 1])
  (set! solver-stack (cons '() solver-stack))
  (solver-write-success `(push ,@(if (= n 1) null (list n)))))

; Occasionally it is useful for debugging to drop into a REPL in a Z3 context deep inside of the tool.
; We can facilitate this by setting a flag to disable all pops.
(define (solver-dont-pop!)
  (set! actually-pop? #f))

; Thin wrapper around Z3's (pop). If actually-pop? is false, don't do anying.
; In any case, record the effect on the debug stack.
(define (solver-pop [n 1])
  (when actually-pop?
    (for ([_ (in-range n)])
      (set! solver-stack (cdr solver-stack)))
    (solver-write-success `(pop ,@(if (= n 1) null (list n))))))


;;; Thin wrappers around Z3 commands that return success-or-error

(define solver-set-option
  (λ args (solver-write-success `(set-option ,@args))))


(define (solver-declare-sort S)
  (solver-log-success `(declare-sort ,S)))

(define (solver-declare-fun f arg-sorts ret-sort)
  (solver-log-success `(declare-fun ,f ,arg-sorts ,ret-sort)))

(define (solver-declare-const C sort)
  (solver-log-success `(declare-const ,C ,sort)))

(define (solver-label expr #:label [label null])
  (if (null? label)
      expr
      `(! ,expr :named ,label)))

(define (solver-assert expr #:label [label null])
  (solver-log-success `(assert ,(solver-label expr #:label label))))

; Write an S-expression to Z3 representing a command that returns some nontrivial result. Return that result.
(define (solver-write-with-result expr)
  (solver-write-raw expr)
  (solver-flush)
  (solver-read))

;;; Thin wrappers around Z3 commands with results

(define z3-check-epr? (make-parameter true))

(define (solver-check-sat)
  (solver-write-with-result '(check-sat)))

(define (solver-eval expr)
  (solver-write-with-result `(eval ,expr)))

(define (solver-get-model)
  (solver-write-with-result '(get-model)))

(define (solver-get-assertions)
  (solver-write-with-result '(get-assertions)))

(define (solver-get-unsat-core)
  (solver-write-with-result '(get-unsat-core)))

; Compute an S-expression equivalent to (not expr) by doing a little bit of NNF-style simplification.
(define (solver-not expr)
  (match expr
    ['true 'false]
    ['false 'true]
    [`(forall ,vars ,body)
     `(exists ,vars ,(solver-not body))]
    [`(exists ,vars ,body)
     `(forall ,vars ,(solver-not body))]
    [`(and ,conjs ...)
     (solver-or* (map solver-not conjs))]
    [`(or ,conjs ...)
     (solver-and* (map solver-not conjs))]
    [`(=> ,e1 ,e2)
     (solver-not `(or (not ,e1) ,e2))]
    [`(not ,expr) expr]
    [_ `(not ,expr)]))

(define (flatten-ands arg)
  (match arg
    [`(and ,args ...) args]
    [_ (list arg)]))

; Compute an S-expression equivalent to (and args) by doing some basic simplifications.
(define (solver-and . args)
  (match (append* (map flatten-ands (filter (λ (x) (not (equal? 'true x))) args)))
    ['() 'true]
    [(list x) x]
    [l `(and ,@l)]))

(define (solver-and* l)
  (apply solver-and l))

; Like solver-and, but for or.
(define (solver-or . args)
  (match (filter (λ (x) (not (equal? 'false x))) args)
    ['() 'false]
    [(list x) x]
    [l `(or ,@l)]))

(define (solver-or* l)
  (apply solver-or l))

; Semantically equivalent to (assert formula), but introduces skolem constants for existential variables.
; Also descends under (and ...) to find more existential quantifiers.
(define (solver-assert-skolemize #:label [name 'anonymous] formula)
  (match formula
    [`(exists ,vars ,body)
     (for ([bv vars])
       (match bv
         [(list x sort)
          (solver-declare-const x sort)]))
     (solver-assert-skolemize #:label name body)]
    [`(and ,body ...)
     (for ([c body])
       (solver-assert-skolemize #:label name c))]
    [`(! ,formula ':named ,other-name)
     (solver-assert-skolemize #:label (symbol-append name '- other-name) formula)]
    [_ (solver-assert #:label (symbol-append name '- (gensym)) formula)]))

(define (quantifier-free e)
  (match e
    [`(forall ,vars ,body) #f]
    [`(exists ,vars ,body) #f]
    [`(and ,args ...) (andmap quantifier-free args)]
    [`(or ,args ...) (andmap quantifier-free args)]
    [`(=> ,e1 ,e2) (and (quantifier-free e1) (quantifier-free e2))]
    [`(not ,e) (quantifier-free e)]
    [_ #t]))

(define (quantifier-alternations expr)
  (define (go env e)
    (match e
      [`(forall ,vars ,body)
       (go (append env vars) body)]
      [`(exists ,vars ,body)
       (stream-append
        (for*/stream ([x env]
                      [y vars])
          (match (list x y)
            [(list (list x xsort) (list y ysort))
             (list xsort ysort (list x y))]))
        (go env body))]
      [`(and ,args ...)
       (apply stream-append (map (λ (e) (go env e)) args))]
      [`(or ,args ...)
       (apply stream-append (map (λ (e) (go env e)) args))]
      [`(=> ,e1 ,e2)
       (go env (solver-or (solver-not e1) e2))]
      [e
       (unless (quantifier-free e)
         (error (format "unexpected expression while analyzing quantifier alternations: ~a" e)))
       empty-stream]))

  (go '() expr))

