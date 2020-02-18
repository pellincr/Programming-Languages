#lang eopl
(require test-engine/racket-tests)
; Exercise 2.1

;Bignums
;n  -> () -> n=0
;   -> (r . [q]) -> n = qN + r, 0<=r<n

;addition: bignum bignum -> bignum
;Purpose: to add the 2 given bignums
;Assumption: they are both written with the same base
(define (addition bn1 bn2)
  (addition-helper (reverse bn1) (reverse bn2)))

(check-expect (addition '(1 2) '(2 2)) '(3 4))
(check-expect (addition '() '(1 2)) '(1 2))
(check-expect (addition '(1 2) '()) '(1 2))

;addition-helper: bignum bignum -> bignum
;Purpose: adds the 2 bignums together
;Assumption: the input bignums are reversed in order to work with the smallest place first
(define (addition-helper bn1 bn2)
  (cond [(null? bn1) (reverse bn2)]
        [(null? bn2) (reverse bn1)]
        [else (reverse (cons (+ (car bn1) (car bn2)) (addition-helper (cdr bn1) (cdr bn2))))]))
(check-expect (addition-helper '(2 1) '(2 2)) '(3 4))
(check-expect (addition-helper '() '(2 1)) '(1 2))
(check-expect (addition-helper '(2 1) '()) '(1 2))

;subtraction: bignum bignum -> bignum
;Purpose: to subtract the 2 given bignums
;Assumption: the bignums are written in the same base
(define (subtraction bn1 bn2)
  (subtraction-helper (reverse bn1) (reverse bn2)))

(check-expect (subtraction '(2 2) '(1 2)) '(1))
(check-expect (subtraction '(3 4) '(3)) '(3 1))
(check-expect (subtraction '(1 2) '()) '(1 2))
(check-expect (subtraction '() '(1 2)) '(-1 -2))

;subtraction-helper: bignum bugnum -> bignum
;Purpose: to subtract the first bignum by the second
;Assumption: the given bignums are reversed inorder to work with the same place at the same time
(define (subtraction-helper bn1 bn2)
  (cond [(null? bn2) (reverse bn1)]
        [(null? bn1) (reverse (map (lambda (x) (* x -1)) bn2))]
        [else (remove-tail-0s (reverse (cons (- (car bn1) (car bn2)) (subtraction-helper (cdr bn1) (cdr bn2)))))]))

(check-expect (subtraction-helper '(2 2) '(2 1)) '(1))
(check-expect (subtraction-helper '(4 3) '(3)) '(3 1))
(check-expect (subtraction-helper '(2 1) '()) '(1 2))
(check-expect (subtraction-helper '() '(2 1)) '(-1 -2))

;remove-tail-0s: bignum -> bignum
;Purpose: to remove the uncessesary 0s at the end of a big num
(define (remove-tail-0s bn)
  (cond [(null? bn) '()]
        [(zero? (car (reverse bn))) (remove-tail-0s (reverse (cdr (reverse bn))))]
        [else bn]))

(check-expect (remove-tail-0s '(1 0)) '(1))
(check-expect (remove-tail-0s '(1 0 0 0)) '(1))
(check-expect (remove-tail-0s '()) '())
(check-expect (remove-tail-0s '(2 0 1 0 0)) '(2 0 1))

;Multiply: bignum bignum -> bignum
;Purpose: to multiply the 2 given bignums
;Assumption: the bignums are written in the same base
;DOES NOT WORK AS INTENDED (does not extend a bignum ex. will go to '(10) before '(0 1)
(define (multiply bn1 bn2)
  (cond [(null? bn1) '()]
        [(null? bn2) '()]
        [(eq? '(1) bn1) bn2]
        [(eq? '(1) bn2) bn1]
        [else (addition bn1 (multiply bn1 (subtraction bn2 '(1))))]))

(check-expect (multiply '(1) '(3)) '(3))
(check-expect (multiply '(3) '(1)) '(3))
(check-expect (multiply '() '(5)) '())
(check-expect (multiply '(5) '()) '())
(check-expect (multiply '(2) '(3)) '(6))

; ;Divide: bignum bignum -> bignum
; ;Purpose: to divide the first bignum by the second
; ;Assumption: the bignums are written in the same base
; (define (divide bn1 bn2)
;   (cond [(null? bn2) (eopl:error "Divide by 0 error")]
;         [(null? bn1) '()]
;         [else ]))
;
;
; ;factorial: bignum -> bignum
; ;Purpose: to return the factorial of the given bignum
; (define (factorial bn)
;   (cond [(null? bn) '(1)]
;         [else (multiply bn (factorial (subtract bn '(1))))]))



; Exercise 2.4
; constructor
; (empty-stack) -> ∅
; (push var F) -> G where G is one element larger than F
;
; observer
; (top F) -> val
; (empty-stack? F) -> boolean
;
; mutator
; (pop F) -> J where J is one element less than F
;



; Exercise 2.7-9

;empty-env: → Env
;Purpose: creates the empty environment
(define empty-env
  (lambda () (list 'empty-env)))

;extend-env: Var × SchemeVal × Env → Env
;Purpose: creates an extended environment
(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))

;apply-env : Env × Var → SchemeVal
;Purpose: to return the val associated with the given var in the given environment
(define apply-env
  (lambda (env search-var)
    (cond
      ((eqv? (car env) 'empty-env)
       (report-no-binding-found search-var))
      ((eqv? (car env) 'extend-env)
       (let ((saved-var (cadr env))
             (saved-val (caddr env))
             (saved-env (cadddr env)))
         (if (eqv? search-var saved-var)
             saved-val
             (apply-env saved-env search-var))))
      (else
       (report-invalid-env env)))))

;empty-env?: env -> boolean
;Purpose: to determine if the given environment is empty
(define (empty-env? env)
  (eq? (car env) 'empty-env))

(check-expect (empty-env? (empty-env)) #t)
(check-expect (empty-env? (extend-env 'a 2 (empty-env))) #f)


;has-binding?: env var -> boolean
;Purpose: determines if the given variable has a values asociated to it in teh given environment
(define (has-binding? env var)
  (cond [(empty-env? env) #f]
        [else (if (eq? (cadr env) var)
                  #t
                  (has-binding? (cadddr env) var))]))

(check-expect (has-binding? (empty-env) 'a) #f)
(check-expect (has-binding? (extend-env 'a 3 (empty-env)) 'a) #t)
(check-expect (has-binding? (extend-env 'a 3 (extend-env 'b 2 (empty-env))) 'b) #t)
(check-expect (has-binding? (extend-env 'a 3 (extend-env 'b 2 (extend-env 'c 1 (empty-env)))) 'd) #f)

;report-no-binding-found: var -> error
;Purpose: to return an error stating that there was no binding for the given variable
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s found in the environment" search-var)))

;report-invalid-env: env -> error
;Purpose: to return an error stating that environment was not properly created
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Environment not properly created: ~s" env)))

; Exercise 2.12

;empty-stack: -> stack
;Purpose: creates the empty stack
(define empty-stack
  (lambda ()
    (lambda(sym)
      (if (eq? sym 'empty-stack?)
          #t
          (eopl:error "No elements in the stack to retrieve")))))

;push: var stack -> stack
;Purpose: to create a stack containing the given var
(define push
  (lambda (var stack)
    (lambda (sym)
      (cond[(eq? sym 'top) var]
           [(eq? sym 'empty-stack?) #f]
           [else stack]))))

;top: stack -> var
;Purpose: to return the top element of the stack
(define top
  (lambda (stack)
    (stack 'top)))

(check-expect (top (push 4 (empty-stack))) 4)
(check-expect (top (push 3 (push 4 (empty-stack))))3)

;pop: stack -> stack
;Purpose: returns the stack without the top element
(define pop
  (lambda (stack)
    (stack 'pop)))

(check-expect (empty-stack? (pop (push 4 (empty-stack)))) #t)
(check-expect (empty-stack? (pop (push 3 (push 4 (empty-stack)))))#f)

;empty-stack?: stack -> boolean
;Purpose: to determine if the given stack is empty
(define empty-stack?
  (lambda (stack)
    (stack 'empty-stack?)))

(check-expect (empty-stack? (empty-stack)) #t)
(check-expect (empty-stack? (push 4 (empty-stack))) #f)

; Exercise 2.21


(define-datatype environment environment?
  (empty-env2)
  (extend-env2
   (var symbol?)
   (val number?)
   (env environment?)))

;has-binding2?: env symbol -> boolean
;Purpose: determines if the given symbol has an associated value in the given environment using the environment datatype
(define (has-binding2? env sym)
  (cases environment env
    (empty-env2 () #f)
    (extend-env2 (var val inner-env) (or (eq? var sym)
                                         (has-binding2? inner-env sym)))))

(check-expect (has-binding2? (extend-env2 'a 3 (empty-env2)) 'a) #t)
(check-expect (has-binding2? (empty-env2) 'a) #f)
(check-expect (has-binding2? (extend-env2 'a 2 (extend-env2 'b 3 (empty-env2))) 'b)#t)
(check-expect (has-binding2? (extend-env2 'a 2 (extend-env2 'b 1 (extend-env2 'c 3 (empty-env2)))) 'd) #f)

; Exercise 2.22

;implement stack using the define-datatype definition
(define-datatype stack2 stack2?
  (empty-stack2)
  (push2
   (top2 number?)
   (pop2 stack2?)))

;empty-stack2?: stack -> boolean
;Purpose: to determine if the given stack is empty by using the datatype definition
(define (empty-stack2? s)
  (cases stack2 s
    (empty-stack2 () #t)
    (push2(t p) #f)))

(check-expect (empty-stack2? (empty-stack2)) #t)
(check-expect (empty-stack2? (push2 3 (empty-stack2))) #f)

;pop2: stack -> stack
;Purpose: to get the stack without the top element by using the datatype definition
(define (pop2 s)
  (cases stack2 s
    (empty-stack2 () (eopl:error "Cannont pop an empty stack"))
    (push2 (t p) p)))

(check-expect (empty-stack2? (pop2 (push2 3 (empty-stack2)))) #t)
(check-expect (empty-stack2? (pop2 (push2 1 (push2 2 (empty-stack2))))) #f)

;top2: stack -> num
;Purpose: to get the top element of the stack by using the datatype definition
(define (top2 s)
  (cases stack2 s
    (empty-stack2 () (eopl:error "Cannot get the top of an empty stack"))
    (push2 (t p) t)))

(check-expect (top2 (push2 3 (empty-stack2))) 3)
(check-expect (top2 (push2 1 (push2 2 (empty-stack2)))) 1)



; Exercise 2.24

(define-datatype bintree bintree?
  (leaf-node
   (num integer?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

;bintree-to-list: btree -> list
;Purpose: to convert the given binary tree into a list
(define (bintree-to-list btree)
  (cases bintree btree
    (leaf-node (num) (list 'leaf-node num))
    (interior-node (k l r) (list 'interior-node k (bintree-to-list l) (bintree-to-list r)))))

(check-expect (bintree-to-list (leaf-node 0)) '(leaf-node 0))
(check-expect (bintree-to-list (interior-node 'a (leaf-node 0) (leaf-node 1))) '(interior-node
                                                                                 a
                                                                                 (leaf-node 0)
                                                                                 (leaf-node 1)))
(check-expect (bintree-to-list (interior-node 'a (interior-node 'b (leaf-node 0) (leaf-node 1)) (leaf-node 2)))
              '(interior-node
                a
                (interior-node
                 b
                 (leaf-node 0)
                 (leaf-node 1))
                (leaf-node 2)))

; Exercise 2.25


;max-interior: btree -> symbol
;Purpose: to return the interior node attached to the largest leaf-node
;Assumption: there must be at least 1 interior node
(define (max-interior btree)
  (cases bintree btree
    (leaf-node (num) (eopl:error "Given ~s is not an interior-node" btree))
    (interior-node (k l r)
                   (cond [(and (>= (+ (sum-tree r) (sum-tree l)) (sum-tree r)) (>= (sum-tree k) (sum-tree r))) k]
                         [(and (>= (sum-tree l) (sum-tree k)) (>= (sum-tree l) (sum-tree r))) l]
                         [(and (>= (sum-tree r) (sum-tree l)) (>= (sum-tree r) (sum-tree k))) r]))))
(define tree-1
  (interior-node 'foo (leaf-node 2) (leaf-node 3)))

(define tree-2
  (interior-node 'bar (leaf-node -1) tree-1))

(define tree-3
  (interior-node 'baz tree-2 (leaf-node 1)))

(check-expect (max-interior tree-2) 'foo)
(check-expect (max-interior tree-3) 'baz)


;sum-tree: btree -> symbol
;Purpose: to output the sum of all the leaves of the given bintree
(define (sum-tree btree)
  (cases bintree btree
    (leaf-node (num) num)
    (interior-node (k l r) (+ (sum-tree l) (sum-tree r)))))

(check-expect (sum-tree (interior-node 'a (leaf-node 4) (leaf-node 5))) 9)
(check-expect (sum-tree (interior-node 'a (leaf-node 3) (interior-node 'b (leaf-node 4) (leaf-node 10)))) 17)
(check-expect (sum-tree (leaf-node 19)) 19)



(test)
