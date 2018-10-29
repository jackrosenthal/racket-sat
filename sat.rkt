#lang racket/base
;; SAT Solver in Racket
;; Author: Jack Rosenthal (jrosenth@mines.edu)
;;
;; Example: (solve '(and a b))
;;    ==>   '((b . #t) (a . #t))
;; Example: (solve '(or (and a b) (and c d) (and e f)))
;;    ==>   '((d . #t) (f . #t) (c . #t))
;; Example: (solve '(and a (not a)))
;;    ==>   #f
;; Example: (solve '(and (or (not a) b) (or a (not b))))
;;    ==>   '((b . #t) (a . #t))

(require racket/function)
(require racket/match)

;; Check if an expression is currently in CNF. The level argument
;; specifies what we have already seen (what we are checking inside)
;;
;; - level 'root: root level, we haven't seen anything
;; - level 'and: we are inside of a conjunction
;; - level 'or: we are inside of a disjunction
(define/match (in-cnf? expr [level 'root])
  [((? symbol?) _) #t]
  [(`(not ,(? symbol?)) _) #t]
  [((list-rest 'or args) (or 'root 'and))
   (andmap (λ (x) (in-cnf? x 'or)) args)]
  [((list-rest 'and args) 'root)
   (andmap (λ (x) (in-cnf? x 'and)) args)]
  [(_ _) #f])

;; Convert a boolean expression to conjunctive normal form.
;; https://en.wikipedia.org/wiki/Conjunctive_normal_form
;;
;; Example: (boolean->cnf '(or (and a b) (and (not c) d) (and (not e) f)))
;;    ==>   '(and (or (not c) a (not e))
;;                (or (not c) b (not e))
;;                (or d a (not e))
;;                (or d b (not e))
;;                (or (not c) a f)
;;                (or (not c) b f)
;;                (or d a f)
;;                (or d b f))
(define (boolean->cnf expr)
  (if (in-cnf? expr)
    expr
    (boolean->cnf
      (match expr
        ;; ¬¬A ≡ A
        [`(not (not ,e)) e]

        ;; DeMorgan's Law
        [`(not (and ,@(list-rest args)))
          `(or ,@(map (curry list 'not) args))]
        [`(not (or ,@(list-rest args)))
          `(and ,@(map (curry list 'not) args))]

        ;; Explosion of and/or with single argument
        [`(or ,e) e]
        [`(and ,e) e]

        ;; Explosion of and/or with nested expression of same operator
        [`(and ,@(list-no-order (list-rest 'and inside) outside ...))
          `(and ,@inside ,@outside)]
        [`(or ,@(list-no-order (list-rest 'or inside) outside ...))
          `(or ,@inside ,@outside)]

        ;; Distributive Law
        [`(or ,@(list-no-order (list-rest 'and and-args) args ...))
          `(or ,@(cdr args)
               (and ,@(map
                        (λ (x) (list 'or (car args) x))
                        and-args)))]

        ;; Otherwise, map boolean->cnf onto arguments
        [(list-rest sym args)
         (cons sym (map boolean->cnf args))]))))

;; Assume a variable holds the value (either #t or #f) in the specified
;; equation. If you are looking at the steps for DPLL, this is the
;; "unit-propagate" step.
(define (assume var value expr)
  (define (reduce-junction)
    (let* ([sym (car expr)]
           [args (cdr expr)]
           [look-for (case sym
                      [(and) #f]
                      [(or) #t])])
      (define (reduction-function item acc)
        (if (eq? acc look-for)
          acc
          (let ([result (assume var value item)])
            (cond
              [(eq? result look-for) result]
              [(eq? result (not look-for)) acc]
              [else (cons result acc)]))))
      (let ([result (foldl reduction-function '() args)])
       (cond
        [(null? result) (not look-for)]
        [(eq? result look-for) result]
        [else (cons sym result)]))))
  (cond
    [(eq? var expr) value]
    [(equal? `(not ,var) expr) (not value)]
    [(symbol? expr) expr]
    [else (case (car expr)
            [(and or) (reduce-junction)]
            [else expr])]))

;; DPLL Algorithm. Returns a set of bindings (list of conses) or #f.
(define (solve-cnf expr)
  (define (solve-rec expr bindings)
    (define (choose-symbol expr)
      (if (symbol? expr)
        expr
        (choose-symbol (cadr expr))))
    (case expr
      [(#t) bindings]
      [(#f) #f]
      [else
        (let ([sym (choose-symbol expr)])
          (define (solve-assume value)
            (solve-rec (assume sym value expr)
                       (cons (cons sym value) bindings)))
          (let ([sym-true (solve-assume #t)])
            (if sym-true
              sym-true
              (solve-assume #f))))]))
  (solve-rec expr '()))

;; Helper to convert to CNF first.
(define (solve expr)
  (solve-cnf (boolean->cnf expr)))
