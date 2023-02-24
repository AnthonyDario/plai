#lang plai-typed

;; ----------------------
;; Chapter 8 Mutation
;; ----------------------

;; We are modelling mutation using boxes
;; We can use a box to store a value, modify the value, and retrieve the value
;;
;;      box : ('a -> (boxof 'a))            Create a box out of a value
;;      unbox : ((boxof 'a) -> 'a)          Retrieve the value from the box
;;      set-box! : ((boxof 'a) 'a -> void)  Modify the value inside the box
;; 
;; It can also be helpful to mutate groups of values, so we can use begin to
;; write a sequence of operations (presumably mutable), and return the result
;; of the last one

;; Exercise: How would you limit store locations only to boxes?
;;           We would need to change the function application so that it makes
;;           a new box.

;; ----------------
;; Types
;; ----------------
(define-type ExprC
  [numC    (n : number)]
  [boolC   (b : boolean)]
  [idC     (x : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [ifC     (c : ExprC) (l : ExprC) (r : ExprC)]
  [appC    (f : ExprC) (a : ExprC)]
  [lamC    (a : symbol) (body : ExprC)]
  [boxC    (a : ExprC)]
  [unboxC  (a : ExprC)]
  [setboxC (b : ExprC) (v : ExprC)]
  [seqC    (b1 : ExprC) (b2 : ExprC)])

(define-type ExprS
  [numS    (n : number)]
  [boolS   (b : boolean)]
  [idS     (x : symbol)]
  [plusS   (l : ExprS)  (r : ExprS)]
  [bminusS (l : ExprS)  (r : ExprS)] ;; binary minus
  [uminusS (e : ExprS)]              ;; unary minus
  [multS   (l : ExprS)  (r : ExprS)]
  [ifS     (c : ExprS)  (l : ExprS) (r : ExprS)]
  [appS    (f : ExprS)  (a : ExprS)]
  [lamS    (a : symbol) (b : ExprS)]
  [letS    (n : symbol) (a : ExprS) (b : ExprS)]
  [boxS    (a : ExprS)]
  [unboxS  (a : ExprS)])

(define-type Value
  [numV  (n : number)]
  [boolV (b : boolean)]
  [boxV  (l : Location)]
  [closV (arg : symbol) (body : ExprC) (env : Env)])

;; We need a result type for our interpreter to return
;; This is because the can modify the store as well as returning a value
(define-type Result
  [v*s (v : Value) (s : Store)])

;; -----------------
;; State
;; -----------------

;; We need to define a store so we can keep track of mutated state. If we try
;; and use the environment we can lose out on lexical scoping:
;;
;;      (+ (let ([b (box 0)])
;;           1)
;;         b)
;;
;; Here the 'b' is unbound because its scope ends at the end of the 'let'.
;; However if we extend the environment and then let it be used in the second
;; branch of the addition, 'b' will be bound

;; One more example:
;;
;;      (let ([a (box 1)])
;;        (let ([f (lambda (x) (+ x (unbox a)))])  
;;          (begin                                 
;;            (set-box! a 2)                       
;;            (f 10))))                            
;;
;; Here the function 'f' will unbox a when it is called. It would make sense
;; for the unboxing in the call to 'f' on the last line to produce 2 since we
;; just set the value of the box to 2

;; We won't ever find an unmapped memory location because the only way to
;; create one in out interpreter is to assign a value to it. 

;; The store is a partial map from names to "memory locations" which we
;; represent as numbers
(define-type-alias Location number)

;; Here, the binding links a name to a location
(define-type Binding
  [bind (name : symbol) (val : Location)]) 

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

;; Now we can retrieve a value from a location
(define-type Storage
  [cell (location : Location) (val : Value)])

(define-type-alias Store (listof Storage))
(define mt-store empty)
(define override-store cons)

;; Helpers
;; -----------------

(define (lookup [for : symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'lookup (string-append "undefined symbol: " (symbol->string for)))]
    [(cons? env) (cond
                    [(equal? for (bind-name (first env))) (bind-val (first env))]
                    [else (lookup for (rest env))])]))

(define (fetch [loc : Location] [sto : Store]) : Value
    (cond
      [(empty? sto) (error 'fetch "Could not find store location")]
      [(cons? sto) (cond
                      [(equal? loc (cell-location (first sto))) (cell-val (first sto))]
                      [else (fetch loc (rest sto))])]))

;; Initially in order to update the state we just added a new cell to the
;; storage (using the 'override-store' function). This works as long as the
;;'fetch' function retrieves the newest cell matching the location. 
;;
;; To make our update more robust, we will actually go in and change the value
;; in the location
(define (update [l : Location] [v : Value] [sto : Store]) : Store
  (cond
    [(empty? sto) (error 'update "Trying to update non-existant location")]
    [(cons? sto) (cond
                   [(equal? l (cell-location (first sto))) (cons (cell l v) (rest sto))]
                   [else (update l v (rest sto))])]))

;; This will increment every time it is called, useful for creating new store
;; locations
(define new-loc
  (let ([n (box 0)])
    (lambda ()
      (begin
        (set-box! n (add1 (unbox n)))
        (unbox n)))))

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
              [(if)  (ifS  (parse (second sl)) 
                           (parse (third sl))
                           (parse (fourth sl)))]
              [(lam) (lamS (s-exp->symbol (second sl)) 
                           (parse (third sl)))]
              [(let) (letS (s-exp->symbol (second sl))
                           (parse (third sl))
                           (parse (fourth sl)))]
              [(box)   (boxS   (parse (second sl)))]
              [(unbox) (unboxS (parse (second sl)))]
              [else  (appS (parse (first sl)) (parse (second sl)))])]))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [else (error 'parse "invalid input")]))

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
    [lamS    (a b)   (lamC a (desugar b))]
    [letS    (n v b) (appC (lamC n (desugar b)) (desugar v))]
    [boxS    (a)     (boxC   (desugar a))]
    [unboxS  (a)     (unboxC (desugar a))]))

;; ---------------------
;; Interpreting
;; ---------------------
(define (interp [e : ExprC] [env : Env] [sto : Store]) : Result
  (type-case ExprC e
    [numC  (n)     (v*s (numV   n) sto)]
    [boolC (b)     (v*s (boolV  b) sto)]
    [idC   (i)     (v*s (fetch (lookup i env) sto) sto)]
    [plusC (l r)   (type-case Result (interp l env sto)
                     [v*s (v-l s-l)
                          (type-case Result (interp r env s-l)
                            [v*s (v-r s-r)
                                 (v*s (num+ v-l v-r) s-r)])])]
    [multC (l r)   (type-case Result (interp l env sto)
                     [v*s (v-l s-l)
                          (type-case Result (interp r env s-l)
                            [v*s (v-r s-r)
                                 (v*s (num+ v-l v-r) s-r)])])]
    [ifC   (c l r) (type-case Result (interp c env sto)
                     [v*s (v-c s-c)
                          (type-case Value v-c
                            [boolV (b) (if b (interp l env s-c) (interp r env s-c))]
                            [else (error 'interp "non-conditional in if")])])]
    [appC (f p) (type-case Result (interp f env sto)
                  [v*s (v-f s-f)
                       (type-case Result (interp p env s-f)
                         [v*s (v-p s-p)
                              (let ([where (new-loc)])
                                (interp (closV-body v-f)
                                        (extend-env (bind (closV-arg v-f)
                                                          where)
                                                    (closV-env v-f))
                                        (override-store (cell where v-p) s-p)))])])]
    [lamC    (a b)   (v*s (closV a b env) sto)]
    [boxC    (a)     (type-case Result (interp a env sto)
                       [v*s (v-a s-a)
                            (let ([where (new-loc)])
                              (v*s (boxV where)
                                   (override-store (cell where v-a)
                                                    s-a)))])]
    [unboxC  (a)     (type-case Result (interp a env sto)
                       [v*s (v-a s-a)
                            (v*s (fetch (boxV-l v-a) s-a) s-a)])]
    ;; TODO: Instead of just writing a new binding, update the location
    [setboxC (b v)   (type-case Result (interp b env sto)
                       [v*s (v-b s-b)
                            (type-case Result (interp v env s-b)
                              [v*s (v-v s-v)
                                   (v*s v-v
                                        (update (boxV-l v-b) v-v s-v))])])]
    [seqC    (b1 b2) (type-case Result (interp b1 env sto)
                       [v*s (v-b1 s-b1)
                            (interp b2 env s-b1)])]))

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
    (test (v*s-v (interp (desugar (parse s)) mt-env mt-store)) v))

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

;; Testing boxes
(test (v*s-v (interp (boxC (numC 5))
                       mt-env mt-store))
      (boxV 5)) ;; Kinda weird since the location is 5

(test (v*s-v (interp (unboxC (boxC (numC 5)))
                      mt-env mt-store))
      (numV 5))

(test (v*s-v (interp (unboxC (unboxC (boxC (boxC (numC 5)))))
                      mt-env mt-store))
      (numV 5))

;; Testing sequences
; (let ([b (box 0)])
;   (begin (begin (set-box! b (+ 1 (unbox b)))
;                 (set-box! b (+ 1 (unbox b))))
;           (unbox b)))
;(parse '(let b (box 0) ()
