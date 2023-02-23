#lang plai-typed

;; ----------------
;; Types
;; ----------------
(define-type ExprC
  [numC  (n : number)            ]
  [idC   (x : symbol)            ]
  [appC  (f : symbol) (a : ExprC)]
  [plusC (l : ExprC)  (r : ExprC)]
  [multC (l : ExprC)  (r : ExprC)])

(define-type ArithS
  [numS (n : number)]
  [plusS (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)] ;; binary minus
  [multS (l : ArithS) (r : ArithS)]
  [uminusS (e : ArithS)])

(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])

(define-type Binding
  [bind (name : symbol) (val : number)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

;; -----------------
;; Parsing
;; -----------------
(define (desugar [a : ArithS]) : ExprC
  (type-case ArithS a
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l) 
                        (desugar r))]
    [multS (l r) (multC (desugar l) 
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [uminusS (e) (multC (numC -1) (desugar e))]
  )
)

;; ---------------------
;; Interpreting
;; ---------------------
(define (interp [e : ExprC] [env : Env] [fds : (listof FunDefC)]) : number
  (type-case ExprC e
    [numC (n) n]
    [idC (i) (lookup i env)]
    [appC (f p) (local ([define fd (get-fundef f fds)])
                  (interp (fdC-body fd) 
                          (extend-env (bind (fdC-arg fd)
                                            (interp p env fds))
                                      mt-env)
                          fds))]
    [plusC (l r) (+ (interp l env fds) (interp r env fds))]
    [multC (l r) (* (interp l env fds) (interp r env fds))]))

(define (substA [what : number] [for : symbol] [in : ExprC]) : ExprC
  (subst (numC what) for in))

(define (subst [what : ExprC] [for : symbol] [in : ExprC]) : ExprC
  (type-case ExprC in
    [numC (n) in]
    [idC (x) (cond 
              [(symbol=? for x) what]
              [else in])]
    [appC (f e) (appC f (subst what for e))]
    [plusC (l r) (plusC (subst what for l) 
                        (subst what for r))]
    [multC (l r) (multC (subst what for l) 
                        (subst what for r))]))

(define (get-fundef [n : symbol] [fds : (listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds) (error 'get-fundef "reference to undefined function")]
    [(cons? fds) (cond
                   [(equal? n (fdC-name (first fds))) (first fds)]
                   [else (get-fundef n (rest fds))])]))

(define (lookup [i : symbol] [env : Env]) : number
  (cond
    [(empty? env) (error 'lookup "undefined symbol")]
    [(cons? env) (cond
                    [(equal? i (bind-name (first env))) (bind-val (first env))]
                    [else (lookup i (rest env))])]))

;; ---------------------
;; Tests
;; ---------------------

(test (interp (plusC (numC 10) (appC 'const5 (numC 10)))
               mt-env
              (list (fdC 'const5 '_ (numC 5))))
       15)

(test (interp (plusC (numC 10) (appC 'double (plusC (numC 1) (numC 2))))
               mt-env
              (list (fdC 'double 'x (plusC (idC 'x) (idC 'x)))))
       16)

(test (interp (plusC (numC 10) (appC 'quadruple (plusC (numC 1) (numC 2))))
               mt-env
              (list (fdC 'quadruple 'x (appC 'double (appC 'double (idC 'x))))
                    (fdC 'double 'x (plusC (idC 'x) (idC 'x)))))
       22)

(test (interp (appC 'f1 (numC 3))
                         mt-env
                        (list (fdC 'f1 'x (appC 'f2 (numC 4)))
                              (fdC 'f2 'y (plusC (idC 'x) (idC 'y)))))
       100)
