#lang eopl
(require test-engine/racket-tests)

;Binary-search-tree ::= () | (Int Binary-search-tree Binary-search-tree)
;path: int bst -> listof-symbols
;Assumption: int n is an element of the given bst
;Purpose: to return the list of left and rights showing how to find n in the given bst
(define (path n bst)
  (cond [(eq? (car bst) n) '()]
        [(> (car bst) n) (cons 'left (path n (cadr bst)))]
        [else (cons 'right (path n (caddr bst)))]))

(check-expect (path 17 '(17 () ())) '())
(check-expect (path 20 '(15 (10 () ()) (20 () ()))) '(right))
(check-expect (path 17 '(14 (7 () (12 () ()))
                            (26 (20 (17 () ()) ()) (31 () ())))) '(right left left))




;Binary-Tree ::== leaf | (interior-node bin-tree bin-tree)
;Interior-node ::== symbol

;leaf: num -> bin-tree
;purpose: to create a leaf for a bintree
(define (leaf num)
  (if (number? num) num
  (eopl:error "Given value ~s is not a number" num)))

;interior-node: symbol bin-tree bin-tree -> bin-tree
;purpose: to create an interior node for a bin-tree
(define (interior-node sym lchild rchild)
  (if (symbol? sym)
      (list sym lchild rchild)
  (eopl:error "Given value ~s is not a symbol" sym)))

;leaf?: leaf -> boolean
;Purpose: to determine if the given value is a leaf
(define (leaf? l)
  (number? l))

(check-expect (leaf? (leaf 5)) #t)
(check-expect (leaf? 'hi) #f)


;lson: interior-node -> bin-tree
;Purpose: to get the left child of the given interior node
(define (lson inode)
  (cadr inode))

(check-expect (lson (interior-node 's (leaf 10) (leaf 11))) 10)
(check-expect (lson (interior-node 's (interior-node 'j (leaf 8) (leaf 6))
                                   (interior-node 'j (leaf 7) (leaf 5))))
              (interior-node 'j (leaf 8) (leaf 6)))

;rson: interior-node -> bin-tree
;Purpose: to get the right child of the given interior node
(define (rson inode)
  (caddr inode))

(check-expect (rson (interior-node 's (leaf 10) (leaf 11))) 11)
(check-expect (rson (interior-node 's (interior-node 'j (leaf 8) (leaf 6))
                                   (interior-node 'j (leaf 7) (leaf 5))))
              (interior-node 'j (leaf 7) (leaf 5)))

;contents-of: interior-node -> symbol
;Purpose: to get the node value of the given interior node
(define (contents-of inode)
  (if (leaf? inode) inode
      (car inode)))

(check-expect (contents-of (leaf 14)) 14)
(check-expect (contents-of (interior-node 's (leaf 10) (leaf 11))) 's)


;number-leaves: bintree -> bintree
;purpose: to replace the leaves with the number of leaf it is in the tree
(define (number-leaves btree)
  ;INVENTORY
  ;(leaf? btree)-determines if the bintree is a leaf
  ;(lson btree) -returns the left child of the given btree
  ;(rson btree) -returns the right child of the given btree
  ;(contents-of btree) - returns the current value of the interior node
  (car (number-leaves-helper btree 0)))

;number-leaves-helper: bintree accum -> (list bintree num)
;purpose: to output a list with the first element being the bintree with the leaves replaced with the number of leaf that it is, and the
;second element being the total number of leaves encountered
;ACCUM INV: accum = the number of leaves processed until the next recursion.

(define (number-leaves-helper btree ctr)
  ;INVENTORY
  ;(leaf? btree)-determines if the bintree is a leaf
  ;(lson btree) -returns the left child of the given btree
  ;(rson btree) -returns the right child of the given btree
  ;(contents-of btree) - returns the current value of the interior node
  (cond [(leaf? (contents-of btree)) (cons ctr (+ 1 ctr))]
        [else
         (letrec [(left-side (number-leaves-helper (lson btree) ctr))
                  (right-side (number-leaves-helper (rson btree) (cdr left-side)))]
         (cons (interior-node(contents-of btree)
                            (car left-side)
                            (car right-side))
                    (cdr right-side)))]))
;---------------------------------------------------------------------------
;checks for helper function:
 (check-expect(number-leaves-helper (interior-node 'bar
                                       (leaf 29)
                                       (leaf 12))0)
'((bar 0 1) . 2))

(check-expect (number-leaves-helper (interior-node 'foo
                                                   (interior-node 'bar
                                                                  (leaf 40)
                                                                  (leaf 90))
                                                   (interior-node 'mickey
                                                                  (leaf 111)
                                                                  (leaf 124)))0)
              '((foo (bar 0 1) (mickey 2 3)) . 4))

(check-expect (number-leaves-helper (interior-node 'foo
                                                   (interior-node 'bar
                                                                  (leaf 12)
                                                                  (leaf 20))
                                                   (interior-node 'mickey
                                                                  (interior-node 'fuz
                                                                                 (leaf 25)
                                                                                 (leaf 40))
                                                                 (leaf 60)))0)
             '((foo (bar 0 1) (mickey (fuz 2 3)4)) . 5))
                                                   


;checks for main function:

(check-expect (number-leaves
               (leaf 3))
              0)
;according to the language, a leaf is a number, or a bintree.
;the book asks to produce a bintree, which could be a leaf which is a number.

(check-expect (number-leaves
                (interior-node 'foo
                               (interior-node 'bar
                                              (leaf 26)
                                              (leaf 12))
                               (interior-node 'baz
                                              (leaf 11)
                                              (interior-node 'quux
                                                             (leaf 117)
                                                             (leaf 14)))))
              '(foo (bar 0 1) (baz 2 (quux 3 4))))

(check-expect  (number-leaves (interior-node 'foo
                                 (leaf 10)
                                 (leaf 12)))
               '(foo 0 1))

(check-expect (number-leaves (interior-node 'foo
                                           (interior-node 'boo
                                                          (leaf 10)
                                                          (leaf 12))
                                           (leaf 30)))
                             '(foo (boo 0 1)2))
(test)
