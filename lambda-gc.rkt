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
  (Instr Hval (Proj Var) (Var Var))
  (Proj proj1 proj2))

(define lambda-gc-red
  (reduction-relation
   lambda-gc

   (--> (letrec Heap in (in-hole Ctxt Hval))
         ;; We use append rather than cons (here and in the app rule)
         ;; to match the semantics of the paper, where new bindings
         ;; get added at the end of the heap rather than the
         ;; beginning.
         (letrec ,(append (term Heap) `((,(term Var) ,(term Hval))))
           in (in-hole Ctxt Var))

         ;; Make sure that Var is a fresh variable, so we don't
         ;; conflict with bindings already in the heap.
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "alloc")

   (--> (letrec Heap in (in-hole Ctxt (Proj Var)))
         (letrec Heap in (in-hole Ctxt (project Proj Heap Var))) 
         "proj")

   (--> (letrec Heap in (in-hole Ctxt (Var_1 Var_2)))
         (letrec
             ,(append (term Heap)
                      ;; New binding on the heap: the equivalent of
                      ;; {z = H(y)} from the paper.
                      `((,(term Var) ,(term (heap-lookup Heap Var_2)))))

           ;; Put Exp in the evaluation context, replacing any
           ;; occurrences of Var_3 (the binder from the lambda
           ;; expression on the heap) with our fresh variable Var.
           in (in-hole Ctxt (subst Exp Var_3 Var)))

         ;; Var_1 should already be bound to a lambda expression in
         ;; the heap.
         (where (lambda (Var_3) Exp) (heap-lookup Heap Var_1))

         ;; Make sure that Var is a fresh variable, so we don't
         ;; conflict with bindings already in the heap.
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "app")))

(define-metafunction lambda-gc
  project : Proj Heap Var -> Var
  ;; Use second and third, instead of first and second, because pairs
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
            (term (letrec ((x 1)) in ((lambda (y) (proj1 y))
                                      (pair x x))))
            (term (letrec ((x 1)
                           (Var (lambda (y) (proj1 y)))
                           (Var1 (pair x x))
                           (Var2 (pair x x)))
                    in x)))


  (test-->> lambda-gc-red
            (term (letrec () in (pair ((lambda (x) x)
                                       (proj2 (pair 1 2)))
                                      ((lambda (x) x)
                                       (proj2 (pair 3 4))))))
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

  ;; Naive substitution works -- here 'Var4' replaces 'x' in (lambda
  ;; (x) x), but it isn't a problem because the formal parameter 'x'
  ;; gets replaced with 'Var4' too!
  (test-->> lambda-gc-red
            (term (letrec () in (pair ((lambda (x)
                                         ((lambda (x) x) 3))
                                       (proj2 (pair 1 2)))
                                      ((lambda (x) x)
                                       (proj2 (pair 3 4))))))

            ;; should be a pair of 3 and 4
            (term (letrec ((Var
                            (lambda (x)
                              ((lambda (x) x)
                               3)))
                           (Var1 1)
                           (Var2 2)
                           (Var3
                            (pair Var1 Var2))
                           (Var4 2)
                           (Var5
                            (lambda (Var4)
                              Var4))
                           (Var6 3)
                           (Var7 3)
                           (Var8 (lambda (x) x))
                           (Var9 3)
                           (Var10 4)
                           (Var11
                            (pair Var9 Var10))
                           (Var12 4)
                           (Var13
                            (pair Var7 Var12)))
                    in
                    Var13)))

  ;; And if 'Var4' appears literally in the term, it's not a problem
  ;; because the variable-not-in feature in the app rule doesn't allow
  ;; us to pick any variable that already appears anywhere in the heap
  ;; at all.
  (test-->> lambda-gc-red
            (term (letrec () in (pair ((lambda (x)
                                         ((lambda (x)
                                            ((lambda (Var4)
                                               x) x)) 3))
                                       (proj2 (pair 1 2)))
                                      ((lambda (x) x)
                                       (proj2 (pair 3 4))))))
            ;; should be a pair of 3 and 4
            (term (letrec ((Var
                            (lambda (x)
                              ((lambda (x)
                                 ((lambda (Var4)
                                    x)
                                  x))
                               3)))
                           (Var1 1)
                           (Var2 2)
                           (Var3
                            (pair Var1 Var2))
                           (Var5 2)
                           (Var6
                            (lambda (Var5)
                              ((lambda (Var4)
                                 Var5)
                               Var5)))
                           (Var7 3)
                           (Var8 3)
                           (Var9
                            (lambda (Var4)
                              Var8))
                           (Var10 3)
                           (Var11
                            (lambda (x) x))
                           (Var12 3)
                           (Var13 4)
                           (Var14
                            (pair Var12 Var13))
                           (Var15 4)
                           (Var16
                            (pair Var8 Var15)))
                    in
                    Var16)))

  (test-->> lambda-gc-red
            (term (letrec () in ((lambda (f)
                                   (pair (f (pair 1 2))
                                         (f (pair 3 4))))
                                 (lambda (p) (proj2 p)))))

            (term (letrec ((Var (lambda (f)
                                  (pair (f (pair 1 2))
                                        (f (pair 3 4)))))
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

  ;; If some variable is already in the heap with a particular name,
  ;; we don't autogenerate that name again.
  (test-->> lambda-gc-red
            (term (letrec ((Var 0)
                           (Var1 1)
                           (Var2 2)) in (pair Var (pair Var1 Var2))))
            (term (letrec ((Var 0)
                           (Var1 1)
                           (Var2 2)
                           (Var3 (pair Var1 Var2))
                           (Var4 (pair Var Var3)))
                    in
                    Var4)))
  
  ;; And using existing names as formal parameters isn't a problem,
  ;; either.
  (test-->> lambda-gc-red
            (term (letrec ((Var 0)
                           (Var1 1)
                           (Var2 2)) in
                           ((lambda (Var1) Var1)
                            (pair
                             Var (pair Var1 Var2)))))
            (term (letrec ((Var 0)
                           (Var1 1)
                           (Var2 2)
                           (Var3 (lambda (Var1) Var1))
                           (Var4 (pair Var1 Var2))
                           (Var5 (pair Var Var4))
                           (Var6 (pair Var Var4)))
                    in
                    Var6)))
  
  (test-results))

;; This is just dumb textual substitution.  Capture-avoiding
;; substitution isn't necessary.
(define-metafunction lambda-gc
  ;; (subst expr old-var new-expr): Read the arguments left-to-right
  ;; as "expr, but with occurrences of old-var replaced with
  ;; new-expr".

  [(subst Var_1 Var_1 any_1) any_1]

  [(subst (any_2 ...) Var_1 any_1)
   ((subst any_2 Var_1 any_1) ...)]

  [(subst any_2 Var_1 any_1) any_2])


