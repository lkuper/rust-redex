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
         (letrec ,(append (term Heap) `((,(term Var_3) ,(term (heap-lookup Heap Var_2)))))
           in (in-hole Ctxt Exp))
         (where (lambda (Var_3) Exp) (heap-lookup Heap Var_1))
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
                           (y (pair x x)))
                    in x)))

  ;; This test shows that variable capture is a problem.  (lambda (x)
  ;; x) gets allocated on the heap twice, and two variables named x
  ;; get allocated on the heap, bound to different values.  We either
  ;; need to do alpha-conversion, or figure out how to transliterate
  ;; capture-avoiding substitution into this setting.
  (test-->> lambda-gc-red
            (term (letrec () in (pair ((lambda (x) x) (proj2 (pair 1 2)))
                                      ((lambda (x) x) (proj2 (pair 3 4))))))
            '() ;; dummy value until I figure out how to fix it
            )

  ;; And another: what if the same procedure gets applied twice?  This
  ;; is wrong, too: (lambda (p) proj2 p) only goes onto the heap once,
  ;; but then two pairs end up being bound to p in the heap.  So we
  ;; again end up getting the wrong answer: '(2 2) instead of '(2 4).
  (test-->> lambda-gc-red
            (term (letrec () in ((lambda (f)
                                  (pair (f (pair 1 2))
                                        (f (pair 3 4))))
                                 (lambda (p) (proj2 p)))))
            '() ;; dummy value until I figure out how to fix it
            )
  
  (test-results))
