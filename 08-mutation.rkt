#lang plai-typed

;; ----------------
;; Types
;; ----------------
(define-type ExprC
  [numC  (n : number)]
  [boolC (b : boolean)]
  [idC   (x : symbol)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [ifC   (c : ExprC) (l : ExprC) (r : ExprC)]
  [appC  (f : ExprC) (a : ExprC)]
  [lamC  (arg : symbol) (body : ExprC)])

(define-type ExprS
  [numS    (n : number)]
  [boolS   (b : boolean)]
  [idS     (x : symbol)]
  [plusS   (l : ExprS)  (r : ExprS)]
  [bminusS (l : ExprS)  (r : ExprS)] ;; binary minus
  [uminusS (e : ExprS)]              ;; unary minus
  [multS   (l : ExprS)  (r : ExprS)]
  [ifS     (c : ExprS) (l : ExprS) (r : ExprS)]
  [appS    (f : ExprS)  (a : ExprS)]
  [lamS    (a : symbol) (b : ExprS)])

(define-type Value
  [numV  (n : number)]
  [boolV (b : boolean)]
  [closV (arg : symbol) (body : ExprC) (env : Env)])

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

;; -----------------
;; Parsing
;; -----------------

;; Parse -> Desugar -> Interp is our pipeline

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-boolean? s) (boolS (s-exp->boolean s))]
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-list? s)
      (let ([sl (s-exp->list s)])
        (cond
          [(s-exp-list? (first sl)) (appS (parse (first sl)) 
                                          (parse (second sl)))]
          [(s-exp-symbol? (first sl))
            (case (s-exp->symbol (first sl))
              [(+) (plusS   (parse (second sl)) (parse (third sl)))]
              [(*) (multS   (parse (second sl)) (parse (third sl)))]
              [(-) (cond 
                     [(eq? (length sl) 3) 
                      (bminusS (parse (second sl)) 
                               (parse (third sl)))]
                     [else (uminusS (parse (second sl)))])]
              [(if)  (ifS (parse (second sl)) 
                          (parse (third sl))
                          (parse (fourth sl)))]
              [(lam) (lamS  (s-exp->symbol (second sl)) 
                            (parse (third sl)))]
              [else (appS (parse (first sl)) (parse (second sl)))])]))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [else (error 'parse "invalid input")]
  )
)

(define (desugar [a : ExprS]) : ExprC
  (type-case ExprS a
    [numS    (n)     (numC  n)]
    [boolS   (b)     (boolC b)]
    [idS     (i)     (idC   i)]
    [plusS   (l r)   (plusC (desugar l) (desugar r))]
    [multS   (l r)   (multC (desugar l) (desugar r))]
    [bminusS (l r)   (plusC (desugar l) 
                            (multC (numC -1) (desugar r)))]
    [uminusS (e)     (multC (numC -1) (desugar e))]
    [ifS     (c l r) (ifC (desugar c) (desugar l) (desugar r))]
    [appS    (f a)   (appC (desugar f) (desugar a))]
    [lamS    (a b)   (lamC a (desugar b))]))

;; ---------------------
;; Interpreting
;; ---------------------
(define (interp [e : ExprC] [env : Env]) : Value
  (type-case ExprC e
    [numC  (n)     (numV   n)]
    [boolC (b)     (boolV  b)]
    [idC   (i)     (lookup i env)]
    [plusC (l r)   (num+ (interp l env) (interp r env))]
    [multC (l r)   (num* (interp l env) (interp r env))]
    [ifC   (c l r) (type-case Value (interp c env)
                      [boolV (b) (if b (interp l env) (interp r env))]
                      [else (error 'interp "non-conditional in if")])]
    [appC  (f p) (local ([define fd (interp f env)])
                  (interp (closV-body fd)
                          (extend-env (bind (closV-arg fd)
                                            (interp p env))
                                      (closV-env fd))))]
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

;; Run the whole pipeline with (compare program expected)
(define (compare [s : s-expression] [v : Value]) : void
    (test (interp (desugar (parse s)) mt-env) v))

(compare '(+ 10 ((lam x 5) 10)) 
         (numV 15))

(compare '(+ 10 ((lam x (+ x x)) (+ 1 2))) 
         (numV 16))

(compare '(((lam x (lam y (+ x y))) 4) 5) 
         (numV 9))

;; Testing conditionals
(compare '(if #t 10 15) 
         (numV 10))

(compare '(if #f 10 15) 
         (numV 15))

;; Undefined symbol x!
;; This is what we want x should remain free in the inner function
;;(compare '(((lam f (lam x (f 10))) (lam y (+ x y))) 10)
;;          (numV 10))
