#lang eopl
(require test-engine/racket-tests)
; Exercise 1.15

;duple: num X -> list of X
;Purpose: to return X n number of times in a list
(define (duple n x)
  (cond [(zero? n) '()]
        [else (cons x (duple (- n 1) x))]))
(check-expect (duple 3 2) '(2 2 2))
(check-expect (duple 2 '(hello)) '((hello) (hello)))
(check-expect (duple 0 "yes") '())


; Exercise 1.16

;invert: lst -> lst
;Purpose: to reverse each list in lst
;Assumption: lst is a list of lists of length 2
(define (invert lst)
  (map reverse lst))

(check-expect (invert '((1 2) (2 3) (3 4))) '((2 1) (3 2) (4 3)))
(check-expect (invert '()) '())
(check-expect (invert '(())) '(()))

; Exercise 1.17

;down: lst -> lst
;Purpose: to wrap parentheses around each top-level element in the given list
(define (down lst)
  (map list lst))

(check-expect (down '(1 2 3)) '((1) (2) (3)))
(check-expect (down '()) '())
(check-expect (down '(a (more (complicated)) (object))) '((a) ((more (complicated))) ((object))))

; Exercise 1.24

;every?: pred lst -> boolean
;Purpose: returns false if any element in lst doexnt satisfy pred
;Essentially create andmap
(define (every? pred lst)
  (cond [(null? lst) #t]
        [else (and (pred (car lst)) (every? pred (cdr lst)))]))

(check-expect (every? even? '(2 3 4)) #f)
(check-expect (every? odd? '(1 3 5)) #t)
(check-expect (every? number? '()) #t)


; Exercise 1.25

;exists?: pred lst -> boolean
;Purpose: outputs true if any element of lst satisfys the given pred
;Essentially create ormap
(define (exists? pred lst)
  (cond [(null? lst) #f]
        [else (or (pred (car lst)) (every? pred (cdr lst)))]))

(check-expect (exists? even? '(2 4 6)) #t)
(check-expect (exists? even? '(1 3 5)) #f)
(check-expect (exists? odd? '(1 2 4 6)) #t)
(check-expect (exists? odd? '()) #f)

; Exercise 1.27

;flatten: slist -> list
;Purpose: to return the list of all sexp in the slist at the top level in the order they were found
(define (flatten slist)
  (cond [(null? slist) '()]
        [else (if (symbol? (car slist))
                  (cons (car slist) (flatten (cdr slist)))
                  (append (flatten (car slist))
                               (flatten (cdr slist))))]))

(check-expect (flatten '(a b c)) '(a b c))
(check-expect (flatten '((a) ((b ())) c)) '(a b c))
(check-expect (flatten '()) '())

; Exercise 1.28

;merge: loi loi -> loi
;Purpose: to combine and sort the 2 given lists
;Assumption: both loi are already sorted in ascedning order
(define (merge loi1 loi2)
  (cond [(null? loi1) loi2]
        [(null? loi2) loi1]
        [(< (car loi1) (car loi2)) (cons (car loi1) (merge (cdr loi1) loi2))]
        [else (cons (car loi2) (merge loi1 (cdr loi2)))]))

(check-expect (merge '(1 4) '(1 2 3)) '(1 1 2 3 4))
(check-expect (merge '() '(1 5 6 14)) '(1 5 6 14))
(check-expect (merge '(3 6 12 15 23) '()) '(3 6 12 15 23))
(check-expect (merge '() '()) '())

; Exercise 1.29

;sort: lst -> lst
;Purpose: returns the given list in ascending order
(define (sort lst)
  (cond [(null? lst) '()]
        [else (insert (car lst) (sort (cdr lst)))]))

(check-expect (sort '()) '())
(check-expect (sort '(6 2 7 2 3)) '(2 2 3 6 7))
(check-expect (sort '(1)) '(1))

;insert: num lst -> list
;Purpose: to insert the given element into the proper place in the list in order to keep it in ascending order
;Assumption: lst is sorted
(define (insert num lst)
  (cond [(or (null? lst) (< num (car lst))) (cons num lst)]
        [else (cons (car lst) (insert num (cdr lst)))]))

(check-expect (insert 5 '(1 2 3 4 6 7)) '(1 2 3 4 5 6 7))
(check-expect (insert 1 '(2 3 4)) '(1 2 3 4))
(check-expect (insert 0 '()) '(0))




(test)
