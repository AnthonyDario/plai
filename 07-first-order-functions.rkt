#lang plai-typed

;; ----------------
;; Types
;; ----------------
(define-type ExprC
  [numC  (n : number)            ]
  [idC   (x : symbol)            ]
  [appC  (f : ExprC) (a : ExprC)]
  [plusC (l : ExprC)  (r : ExprC)]
  [multC (l : ExprC)  (r : ExprC)]
  [lamC  (arg : symbol) (body : ExprC)])

(define-type Value
  [numV (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)])

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

;; ---------------------
;; Interpreting
;; ---------------------
(define (interp [e : ExprC] [env : Env]) : Value
  (type-case ExprC e
    [numC (n) (numV n)]
    [idC (i) (lookup i env)]
    [appC (f p) (local ([define fd (interp f env)])
                  (interp (closV-body fd)
                          (extend-env (bind (closV-arg fd)
                                            (interp p env))
                                      (closV-env fd))))]
    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [lamC (a b) (closV a b env)]))

(define (lookup [i : symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup (string-append "undefined symbol: " (symbol->string i)))]
    [(cons? env) (cond
                    [(equal? i (bind-name (first env))) (bind-val (first env))]
                    [else (lookup i (rest env))])]))

;; ---------------------
;; Helpers
;; ---------------------
(define (num+ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (+ (numV-n l) (numV-n r)))]
    [else (error 'num+ "adding a non-number")]))

(define (num* [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (* (numV-n l) (numV-n r)))]
    [else (error 'num* "subtracting a non-number")]))

;; ---------------------
;; Tests
;; ---------------------

(test (interp (plusC (numC 10) 
                     (appC (lamC '_ (numC 5))
                           (numC 10)))
              mt-env)
      (numV 15))
            
(test (interp (plusC (numC 10) 
                     (appC (lamC 'x 
                                 (plusC (idC 'x) (idC 'x)))
                           (plusC (numC 1) (numC 2))))
              mt-env)
      (numV 16))

(test (interp (appC (appC (lamC 'x 
                               (lamC 'y
                                    (plusC (idC 'x) (idC 'y))))
                          (numC 4))
                    (numC 5))
              mt-env)
      (numV 9))

(test (interp (appC (lamC 'f
                          (lamC 'x
                                (appC (idC 'f) (numC 10))))
                    (lamC 'y
                          (plusC (idC 'x) (idC 'y))))
              mt-env)
      (numV 10))
