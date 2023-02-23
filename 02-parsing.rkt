#lang plai-typed

(define-type ArithC
  [numC (n : number)]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

(define (parse [s : s-expression]) : ArithC
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-list? s)
      (let ([sl (s-exp->list s)])
        (case (s-exp->symbol (first sl))
          [(+) (plusC (parse (second sl)) (parse (third sl)))]
          [(*) (multC (parse (second sl)) (parse (third sl)))]
          [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]
  )
)

(parse '(+ (* 1 2) (+ 2 3)))
;; If you forget to quote you get a type error
;;(parse (+ (* 1 2) (+ 2 3)))

;; --------------
;; Chapter 3
;; --------------
(define (interp [a : ArithC]) : number
  (type-case ArithC a
    [numC (n) n]
    [plusC (l r) (+ (interp l) (interp r))]
    [multC (l r) (* (interp l) (interp r))]))

(= (interp (parse '(+ (* 1 2) (+ 2 3)))) 
    7)
(= (interp (parse '(* (+ 1 2) (+ 2 3)))) 
    15)

(= (interp (parse '(* (* 2 2) (* 2 2)))) 
    16)

;; --------------
;; Chapter 4
;; --------------

(define-type ArithS
  [numS (n : number)]
  [plusS (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)] ;; binary minus
  [multS (l : ArithS) (r : ArithS)]
  [uminusS (e : ArithS)])

;;(define (interp [a : ArithC]) : number
;;  (type-case ArithC a
;;    [numC (n) n]
;;    [plusC (l r) (+ (interp l) (interp r))]
;;    [multC (l r) (* (interp l) (interp r))]))
;; Take an ArithS expression and turn it into an ArithC one
(define (desugar [a : ArithS]) : ArithC
  (type-case ArithS a
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l) 
                        (desugar r))]
    [multS (l r) (multC (desugar l) 
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [uminusS (e) (multC (numC -1) (desugar e))]
    ;; Adding uminusS this way doesn't work (Not sure why...)
    ;; But it does make us rely on the implementation of bminusS
    ;; So if that changes, then unary subtraction changes
    ;; [uminusS (e) (desugar (bminusS (numS 0) e))] 
  ))

;; Don't forget the recursive call! Then you get a type error
(desugar (bminusS (multS (uminusS (numS 5)) (numS 4))
                  (numS 15)))

(desugar (uminusS (bminusS (multS (uminusS (numS 5)) (numS 4))
                  (numS 15))))
