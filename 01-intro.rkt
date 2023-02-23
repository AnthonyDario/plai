#lang plai-typed

(define-type MisspelledAnimal
  [caml (humps : number)]
  [yacc (height : number)])

(define ma1 : MisspelledAnimal (caml 2))
(define ma2 : MisspelledAnimal (yacc 1.9))

(define (good? [ma : MisspelledAnimal]) : boolean
  (type-case MisspelledAnimal ma
    [caml (h) (>= h 2)]
    [yacc (h) (> h 2.1)]
  )
)

(test (good? ma1) #t)
(test (good? ma2) #f)
