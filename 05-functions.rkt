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
  [fdc (name : symbol) (arg : symbol) (body : ExprC)])

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
(define (interp [e : ExprC] [fds : (listof FunDefC)]) : number
  (type-case ExprC e
    [numC (n) n]
    [idC (_) (error 'interp "shouldn't get here")]
    [appC (f p) (local ([define fd (get-fundef f fds)])
                  (interp (substA (interp p fds)
                                  (fdC-arg fd)
                                  (fdC-body fd))
                           fds))]
    [plusC (l r) (+ (interp l fds) (interp r fds))]
    [multC (l r) (* (interp l fds) (interp r fds))]))

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

;; ---------------------
;; Helpers
;; ---------------------
(define (fdC-name [f : FunDefC]) : symbol
  (type-case FunDefC f
    [fdc (n a b) n]))

(define (fdC-arg [f : FunDefC]) : symbol
  (type-case FunDefC f
    [fdc (n a b) a]))

(define (fdC-body [f : FunDefC]) : ExprC
  (type-case FunDefC f
    [fdc (n a b) b]))

;; ---------------------
;; Tests
;; ---------------------

;; Functions tests
;; ---------------------

;; (define double x (+ x x))
(fdc 'double 'x (plusC (idC 'x) (idC 'x)))

;; (define quadruple x (double (double x)))
(fdc 'quadruple 'x (appC 'double (appC 'double (idC 'x))))

;; (define const5 _ 5)
(fdc 'const5 '_ (numC 5))

;; Conditional test cases
;; ---------------------
;;(= (interp (desugar (boolS #t))) #t)
;;(= (interp (desugar
;;  (ifS (trueS (numS 5) (plusS (numS 4) (numS 1))))))
;;5)
;;
;;(= (interp (desugar
;;  (ifS (falseS (numS 5) (plusS (numS 3) (numS 1))))))
;;4)
