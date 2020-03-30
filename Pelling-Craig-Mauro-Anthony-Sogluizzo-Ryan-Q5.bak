#lang eopl
(require test-engine/racket-tests)
;INSTANCE VARIABLES
(define current-num 'uninitialized)
(define accum 'uninitialized)

;fact-iter: num -> num
;Purpose: to return the factorial of the given number using continuations
(define (fact-iter n)
  (begin
    (set! current-num n)
    (set! accum 1)
    (fact-iter-k)))

;fact-iter-k: ->num
;Purpose: to calculate factorial using the instance variables
(define (fact-iter-k)
  (cond [(zero? current-num) accum]
        [else (begin
                (set! accum (* accum current-num))
                (set! current-num (- current-num 1))
                (fact-iter-k))]))

;Tests
(check-expect (fact-iter 5) 120)
(check-expect (fact-iter 0) 1)
(check-expect (fact-iter 3) 6)

(test)
