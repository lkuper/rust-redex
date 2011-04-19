;; A Redex model of the lambda-gc language from Morrisett, Felleisen,
;; and Harper, "Abstract Models of Memory Management"
;; (http://www.cs.cmu.edu/~rwh/papers/gc/fpca95.pdf).

#lang racket
(require redex)

(define-language lambda-gc
  ;; Programs.
  (Var variable-not-otherwise-mentioned)
  (Int number)
  (Exp Var Int (pair Exp_1 Exp_2) (proj1 Exp) (proj2 Exp) (lambda (Var) Exp)
       (Exp_1 Exp_2))
  (Hval Int (pair Var_1 Var_2) (lambda (Var) Exp))
  (Heap ((Var Hval) ...))
  (Prog (letrec Heap in Exp))
  (Ans (letrec Heap in Var))

  ;; Evaluation contexts and instruction expressions.
  (Ctxt hole (pair Ctxt Exp) (pair Var Ctxt) (proj1 Ctxt) (proj2 Ctxt)
        (Ctxt Exp) (Var Ctxt))
  (Instr Hval (proj1 Var) (proj2 Var) (Var Var))

  ;; This is just so we can define the domain of 'project'.
  (label proj1 proj2))

(define lambda-gc-red
  (reduction-relation
   lambda-gc

   (---> (letrec Heap in (in-hole Ctxt Hval))
         ;; We use append rather than cons (here and in the app rule)
         ;; to match the semantics of the paper, where new bindings
         ;; get added at the end of the heap rather than the
         ;; beginning.
         (letrec ,(append (term Heap) `((,(term Var) ,(term Hval))))
           in (in-hole Ctxt Var))
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "alloc")
   (---> (letrec Heap in (in-hole Ctxt (proj1 Var)))
         (letrec Heap in (in-hole Ctxt (project proj1 Heap Var))) 
         "proj1")
   (---> (letrec Heap in (in-hole Ctxt (proj2 Var)))
         (letrec Heap in (in-hole Ctxt (project proj2 Heap Var))) 
         "proj2")
   (---> (letrec Heap in (in-hole Ctxt (Var_1 Var_2)))

         ;; The equivalent of z = H(y) from the paper: Var =
         ;; H(Var_2).
         (letrec ,(append (term Heap) `((,(term Var)
                                         ,(term (heap-lookup Heap
                                                             Var_2)))))

           ;; If we took this right from the paper we'd put (in-hole
           ;; Ctxt Exp) here.  But instead we're doing Exp but with
           ;; free occurrences of Var_3 replaced with Var (which is
           ;; fresh).  Then we can put Var on the heap.
           in (in-hole Ctxt (subst Exp Var_3 Var)))
         (where (lambda (Var_3) Exp) (heap-lookup Heap Var_1))
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "app")
   with
   [(--> (in-hole Ctxt a) (in-hole Ctxt b)) (---> a b)]))

(define-metafunction lambda-gc
  project : label Heap Var -> Var
  ;; second and third, instead of first and second, because pairs
  ;; start with the tag 'pair.
  [(project proj1 Heap Var) ,(second (term (heap-lookup Heap Var)))]
  [(project proj2 Heap Var) ,(third (term (heap-lookup Heap Var)))])

(define-metafunction lambda-gc
  heap-lookup : Heap Var -> Hval
  [(heap-lookup Heap Var) ,(second (assq (term Var) (term Heap)))])

;; A few tests.

(define (test-suite)
  (test-->> lambda-gc-red
            (term (letrec () in 3))
            (term (letrec ((Var 3))
                    in Var)))

  (test-->> lambda-gc-red
            (term (letrec () in (pair 3 4)))
            (term (letrec ((Var 3)
                           (Var1 4)
                           (Var2 (pair Var Var1)))
                    in Var2)))

  (test-->> lambda-gc-red
            (term (letrec () in (proj1 (pair 3 4))))
            (term (letrec ((Var 3)
                           (Var1 4)
                           (Var2 (pair Var Var1)))
                    in Var)))

  ;; The example from the lambda-gc TR
  ;; (http://www.cs.cmu.edu/~rwh/papers/gc/tr.pdf).
  (test-->> lambda-gc-red
            (term (letrec ((x 1)) in ((lambda (y) (proj1 y)) (pair x x))))
            (term (letrec ((x 1)
                           (Var (lambda (y) (proj1 y)))
                           (Var1 (pair x x))
                           (Var2 (pair x x)))
                    in x)))

  ;; This test would break if we weren't doing capture-avoiding
  ;; substitution right.
  (test-->> lambda-gc-red
            (term (letrec () in (pair ((lambda (x) x) (proj2 (pair 1 2)))
                                      ((lambda (x) x) (proj2 (pair 3 4))))))
            (term (letrec ((Var (lambda (x) x))
                           (Var1 1)
                           (Var2 2)
                           (Var3 (pair Var1 Var2))
                           (Var4 2)
                           (Var5 (lambda (x) x))
                           (Var6 3)
                           (Var7 4)
                           (Var8 (pair Var6 Var7))
                           (Var9 4)
                           (Var10 (pair Var4 Var9)))
                    in
                    Var10)))

  ;; So would this one.
  (test-->> lambda-gc-red
            (term (letrec () in ((lambda (f)
                                  (pair (f (pair 1 2))
                                        (f (pair 3 4))))
                                 (lambda (p) (proj2 p)))))

            (term (letrec ((Var (lambda (f) (pair (f (pair 1 2)) (f (pair 3 4)))))
                            (Var1 (lambda (p) (proj2 p)))
                            (Var2 (lambda (p) (proj2 p)))
                            (Var3 1)
                            (Var4 2)
                            (Var5 (pair Var3 Var4))
                            (Var6 (pair Var3 Var4))
                            (Var7 3)
                            (Var8 4)
                            (Var9 (pair Var7 Var8))
                            (Var10 (pair Var7 Var8))
                            (Var11 (pair Var4 Var8)))
                     in
                     Var11)))
  (test-results))


;; Capture-avoiding substitution, borrowed from the Redex book,
;; pp. 221-223.
(define-metafunction lambda-gc
  ;; (subst expr old-var new-expr)
  ;; "expr, but with free occurrences of old-var replaced with
  ;; new-expr"

  ;; 1. Var_1 bound, so don't continue in lambda body
  [(subst (lambda (Var_1) any_1) Var_1 any_2)
   (lambda (Var_1) any_1)]

  ;; 2. do capture-avoiding substitution by generating a fresh name
  [(subst (lambda (Var_1) any_1) Var_2 any_2)
   (lambda (Var_3)
     (subst (subst-var any_1 Var_1 Var_3) Var_2 any_2))
   (where Var_3 ,(variable-not-in (term (Var_2 any_1 any_2))
                                  (term Var_1)))]

  ;; 3. replace Var_1 with any_1
  [(subst Var_1 Var_1 any_1) any_1]

  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) Var_1 any_1)
   ((subst any_2 Var_1 any_1) ...)]
  [(subst any_2 Var_1 any_1) any_2])

(define-metafunction lambda-gc
  [(subst-var (any_1 ...) Var_1 Var_2)
   ((subst-var any_1 Var_1 Var_2) ...)]
  [(subst-var Var_1 Var_1 Var_2) Var_2]
  [(subst-var any_1 Var_1 Var_2) any_1])

