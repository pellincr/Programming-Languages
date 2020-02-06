#lang eopl

(require test-engine/racket-tests)

;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)

    (comment ("%" (arbno (not #\newline))) skip)

    (identifier
     (letter (arbno (or letter digit "_" "-" "?"))) symbol)

    (number (digit (arbno digit)) number)

    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)

    (expression (number) const-exp)

    (expression ("minus" "(" expression ")") minus-exp)

    (expression("-" "(" expression "," expression ")")diff-exp)

    (expression ("+" "(" expression "," expression ")") add-exp)

    (expression ("*" "(" expression "," expression ")") mult-exp)

    (expression ("/" "(" expression "," expression ")" ) quot-exp)

    (expression ("zero?" "(" expression ")") zero?-exp)

    (expression ("equal?" "(" expression "," expression ")" ) eq?-exp)

    (expression ("greater?" "(" expression "," expression ")") greater?-exp)

    (expression ("less?" "(" expression "," expression ")") less?-exp)

    (expression
     ("if" expression "then" expression "else" expression) if-exp)

    (expression (identifier) var-exp)

    (expression
     ("let" identifier "=" expression "in" expression) let-exp)

    (expression
     ("cons" "(" expression "," expression ")") cons-exp)

    (expression
     ("car" "(" expression ")" ) car-exp)

    (expression
     ("cdr" "(" expression ")" ) cdr-exp)

    (expression
     ("null?" "(" expression ")" ) null?-exp)

    (expression
     ("empty-list") MTList-exp)

    (expression
     ("list" "(" (arbno "," expression) ")" ) list-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;    ENVIRONMENT

;; example of a data type built without using define-datatype

(define (empty-env-record) '())

(define (extended-env-record sym val old-env)
  (cons (list sym val) old-env))

(define empty-env-record? null?)

(define (environment? x)
  (or (empty-env-record? x)
      (and (pair? x)
           (symbol? (car (car x)))
           (expval? (cadr (car x)))
           (environment? (cdr x)))))

(define (extended-env-record->sym r) (car (car r)))

(define (extended-env-record->val r) (cadr (car r)))

(define (extended-env-record->old-env r) (cdr r))

;; end of example of a data type built without define-datatype

;;;;; Implementation of environment interface
(define empty-env
  (lambda ()
    (empty-env-record)))

(define empty-env?
  (lambda (x)
    (empty-env-record? x)))

(define extend-env
  (lambda (sym val old-env)
    (extended-env-record sym val old-env)))

(define apply-env
  (lambda (env search-sym)
    (if (empty-env? env)
        (eopl:error 'apply-env "No binding for ~s" search-sym)
        (let ((sym (extended-env-record->sym env))
              (val (extended-env-record->val env))
              (old-env (extended-env-record->old-env env)))
          (if (eqv? search-sym sym)
              val
              (apply-env old-env search-sym))))))

(define (init-env)
  (extend-env
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10)
     (empty-env)))))


;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (list-val
   (myList list?)))

;;; observers:

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

;; expval->list : ExpVal -> list
(define expval->list
  (lambda (v)
    (cases expval v
      (list-val (list) list)
      (else (expval-extractor-error 'list v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-observers "Looking for a ~s, found ~s"
                variant value)))

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-env)))))

;; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp

    (const-exp (num) (num-val num))

    (var-exp (var) (apply-env env var))

    (minus-exp (exp)
               (let ((val (value-of exp env)))
                 (let ((num (expval->num val)))
                   (num-val (- 0 num)))))

    (diff-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (- num1 num2)))))

    (add-exp (exp1 exp2)
             (let ((val1 (value-of exp1 env))
                   (val2 (value-of exp2 env)))
               (let ((num1(expval->num val1))
                     (num2 (expval->num val2)))
                 (num-val (+ num1 num2)))))

    (mult-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (* num1 num2)))))

    (quot-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (quotient num1 num2)))))


    (zero?-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (let ((num1 (expval->num val1)))
                   (if (zero? num1)
                       (bool-val #t)
                       (bool-val #f)))))

    (eq?-exp (exp1 exp2)
             (let ((val1 (value-of exp1 env))
                   (val2 (value-of exp2 env)))
               (let ((num1 (expval->num val1))
                     (num2 (expval->num val2)))
                 (bool-val (= num1 num2)))))

    (greater?-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (bool-val (> num1 num2)))))

    (less?-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (bool-val (< num1 num2)))))

    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval->bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))

    (let-exp (var exp1 body)
             (let ((val1 (value-of exp1 env)))
               (value-of body
                         (extend-env var val1 env))))

    (cons-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((list2 (expval->list val2)))
                  (list-val (cons val1 list2)))))

    (car-exp (exp)
             (let ((val (value-of exp env)))
               (let ((list1 (expval->list val)))
                 (car list1))))

    (cdr-exp (exp)
             (let ((val (value-of exp env)))
               (let ((list1 (expval->list val)))
                 (list-val (cdr list1)))))

    (null?-exp (exp)
               (let ((val (value-of exp env)))
                 (let ((list1 (expval->list val)))
                   (bool-val (null? list1)))))

    (MTList-exp ()
                (list-val '()))

    (list-exp (exps)
              (let ((vals (map (lambda(exp) (value-of exp env)) exps)))
                (list-val (list (car vals) (value-of (list-val (cdr vals)) env)))))
    ))

;;;;;;   EVALUATION WRAPPERS

;; eval : String -> ExpVal
(define (eval string)
  (value-of-program (scan&parse string)))

;;;;; EXAMPLES OF EVALUATION

; (eval "if zero?(1) then 1 else 2")
; (eval "minus(x)")
; (eval "-(x, v)")
; (eval "+(x, v)")
; (eval "*(x, v)")
; (eval "/(x, v)")
; (eval "if zero?(-(x, x)) then x else 2")
; (eval "if zero?(-(x, v)) then x else 2")
; (eval "equal?(x, v)")
; (eval "greater?(x, v)")
; (eval "less?(x, v)")
; (eval "let x = 2 in -(x, 2)")
; (eval "cons(x,empty-list)")
; (eval "car(cons(x,empty-list))")
; (eval "cdr(cons(x, empty-list))")
; (eval "null?(cons(x, empty-list))")
; (eval "null?(empty-list)")

(check-expect (eval "if zero?(1) then 1 else 2")
              (num-val 2))
(check-expect (eval "minus(x)")
              (num-val -10))
(check-expect (eval "-(x, v)")
              (num-val 5))
(check-expect (eval "+(x,v)")
              (num-val 15))
(check-expect (eval "*(x, v)")
              (num-val 50))
(check-expect (eval "/(x, v)")
              (num-val 2))
(check-expect (eval "if zero?(-(x, x)) then x else 2")
              (num-val 10))
(check-expect (eval "if zero?(-(x, v)) then x else 2")
              (num-val 2))
(check-expect (eval "equal?(x, v)")
              (bool-val #f))
(check-expect (eval "greater?(x, v)")
              (bool-val #t))
(check-expect (eval "less?(x, v)")
              (bool-val #f))
(check-expect (eval "let x = 2 in -(x, 2)")
              (num-val 0))
(check-expect (eval "cons(x,empty-list)")
              (list-val (list (num-val 10))))
(check-expect (eval "car(cons(x,empty-list))")
              (num-val 10))
(check-expect (eval "cdr(cons(x, empty-list))")
              (list-val '()))
(check-expect (eval "null?(cons(x, empty-list))")
              (bool-val #f))
(check-expect (eval "null?(empty-list)")
              (bool-val #t))
(check-expect (eval "list(x v)")
              (list-val (list 10 5)))
(test)