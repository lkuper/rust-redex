#lang racket
(require redex/reduction-semantics
         "rust.rkt")

(define (typeck-test-suite)
  ;; TODO: This is just a start -- we should test fancier types.

  (test-equal
   (term (typeck () 3))
   (term int))

  (test-equal
   (term (typeck () (3 + 3)))
   (term int))

  (test-equal
   (term (typeck () (3 - 3)))
   (term int))

  (test-equal
   (term (typeck () (3 - 5)))
   (term int))

  (test-equal
   (term (typeck () ((neg 3) - 5)))
   (term int))

  (test-equal
   (term (typeck () (3 * 5)))
   (term int))

  (test-equal
   (term (typeck () ((neg 3) * (3 + 3))))
   (term int))

  (test-equal
   (term (typeck () false))
   (term bool))

  (test-equal
   (term (typeck () true))
   (term bool))

  (test-equal
   (term (typeck () (not (not (not false)))))
   (term bool))

  (test-equal
   (term (typeck () (box 3)))
   (term (Box int)))

  (test-equal
   (term (typeck () (box (not (not (not false))))))
   (term (Box bool)))

  (test-equal
   (term (typeck () (tup 1)))
   (term (Tup int)))

  (test-equal
   (term (typeck () (tup 1 2 3)))
   (term (Tup int int int)))

  (test-equal
   (term (typeck () (tup 1 false (3 + 3))))
   (term (Tup int bool int)))

  (test-equal
   (term (typeck () (tup (tup 1 2 (box 3)) true)))
   (term (Tup (Tup int int (Box int)) bool)))

  (test-equal
   (term (typeck () (tup (tup 1 2 (box 3)) true (4 * (5 + 3))
                         (not false) (neg 6))))
   (term (Tup (Tup int int (Box int)) bool int bool int)))

  (test-equal
   (term (typeck () (tup (neg (neg (neg (neg (5 + (3 - 7)))))))))
   (term (Tup int)))

  (test-equal
   (term (typeck () (index (tup 2) 0)))
   (term int))

  (test-equal
   (term (typeck () (index (tup 2) (1 - 1))))
   (term int))

  (test-equal
   (term (typeck () (index (tup 2 3 4) (1 - 1))))
   (term int))

  (test-equal
   (term (typeck () (index (tup 2 3 4 5) (1 + (1 + 1)))))
   (term int))

  (test-equal
   (term (typeck () (index (tup 2 3 4 false) (1 + (1 + 1)))))
   (term bool))

  (test-equal
   (term (typeck () (index (tup true false true false)
                           (index (tup 0 1 2) 2))))
   (term bool))

  (test-equal
   (term (typeck () (index (tup (box true) (box 1))
                           (index (tup 0 1 2) (deref (box 0))))))
   (term (Box bool)))

  (test-equal
   (term (typeck () (deref (box 0))))
   (term int))

  (test-equal
   (term (typeck () (deref (deref (box (box 0))))))
   (term int))

  (test-equal
   (term (typeck () (deref (box (deref (box 0))))))
   (term int))

  (test-equal
   (term (typeck () (tup (deref (box (deref (box false)))))))
   (term (Tup bool)))

  (test-results))

(define (meta-test-suite)
  (test-equal
   (term (result-value (()
                        ((Var 3))
                        Var)))
   (term 3))

  (test-equal
   (term (result-value (()
                         ((Var 3)
                          (Var1 3)
                          (Var2 6))
                         Var2)))
   (term 6))

  (test-equal
   (term (result-value (()
                        ((Var true)
                         (Var1 false)
                         (Var2 true)
                         (Var3 false)
                         (Var4 true)
                         (Var5 (tup Var2 Var3 Var4))
                         (Var6 2)
                         (Var7 (tup Var Var1 Var4)))
                        Var7)))
   (term (tup true false true)))

  (test-equal
   (term (result-value (()
                        ((Var 3)
                         (Var1 4)
                         (Var2 true)
                         (Var3 false)
                         (Var4 (box Var))
                         (Var5 (box Var4))
                         (Var6 (tup Var2 Var3))
                         (Var7 (tup Var1 Var4 Var5 Var6)))
                        Var7)))
   (term (tup 4 (box 3) (box (box 3)) (tup true false))))

  (test-results))

(define (expr-test-suite)
  (test-->> baby-rust-red
            (create-program (term 3))
            (term
             (()
              ((Var 3))
              Var)))

  (test-->> baby-rust-red
            (create-program (term (3 + 3)))
            (term
             (()
              ((Var 3)
               (Var1 3)
               (Var2 6))
              Var2)))

  (test-->> baby-rust-red
            (create-program (term (3 + (2 + 1))))
            (term
             (()
              ((Var 3)
               (Var1 2)
               (Var2 1)
               (Var3 3)
               (Var4 6))
              Var4)))

  (test-->> baby-rust-red
            (create-program (term ((3 + 2) + 1)))
            (term
             (()
              ((Var 3)
               (Var1 2)
               (Var2 5)
               (Var3 1)
               (Var4 6))
              Var4)))

  (test-->> baby-rust-red
            (create-program (term true))
            (term
             (()
              ((Var true))
              Var)))

  (test-->> baby-rust-red
            (create-program (term (not true)))
            (term
             (()
              ((Var true)
               (Var1 false))
              Var1)))

  (test-->> baby-rust-red
            (create-program (term (deref (box 3))))
            (term
             (()
              ((Var 3)
               (Var1 (box Var)))
              Var)))

  (test-->> baby-rust-red
            (create-program (term (deref (box (3 + 3)))))
            (term
             (()
              ((Var 3)
               (Var1 3)
               (Var2 6)
               (Var3 (box Var2)))
              Var2)))

  (test-->> baby-rust-red
            (create-program (term (deref (box (not (not false))))))
            (term
             (()
              ((Var false)
               (Var1 true)
               (Var2 false)
               (Var3 (box Var2)))
              Var2)))

  (test-->> baby-rust-red
            (create-program (term (tup 1 2 3)))
            (term
             (()
              ((Var 1)
               (Var1 2)
               (Var2 3)
               (Var3 (tup Var Var1 Var2)))
              Var3)))

  (test-->> baby-rust-red
            (create-program (term (tup 1 2 (3 + 3))))
            (term
             (()
              ((Var 1)
               (Var1 2)
               (Var2 3)
               (Var3 3)
               (Var4 6)
               (Var5 (tup Var Var1 Var4)))
              Var5)))

  (test-->> baby-rust-red
            (create-program (term (index (tup 1 2 (3 + 3)) 0)))
            (term
             (()
              ((Var 1)
               (Var1 2)
               (Var2 3)
               (Var3 3)
               (Var4 6)
               (Var5 (tup Var Var1 Var4))
               (Var6 0))
              Var)))

  (test-->> baby-rust-red
            (create-program (term (index (tup 1 2 (3 + 3)) 2)))
            (term
             (()
              ((Var 1)
               (Var1 2)
               (Var2 3)
               (Var3 3)
               (Var4 6)
               (Var5 (tup Var Var1 Var4))
               (Var6 2))
              Var4)))

  (test-->> baby-rust-red
            (create-program
             (term (tup true false (index (tup true false true) 2))))
            (term
             (()
              ((Var true)
               (Var1 false)
               (Var2 true)
               (Var3 false)
               (Var4 true)
               (Var5 (tup Var2 Var3 Var4))
               (Var6 2)
               (Var7 (tup Var Var1 Var4)))
              Var7)))

  (test-->> baby-rust-red
            (create-program
             (term (index (tup true false
                               (index (tup true false true) 2)) 0)))
            (term
             (()
              ((Var true)
               (Var1 false)
               (Var2 true)
               (Var3 false)
               (Var4 true)
               (Var5 (tup Var2 Var3 Var4))
               (Var6 2)
               (Var7 (tup Var Var1 Var4))
               (Var8 0))
              Var)))

  (test-->> baby-rust-red
            (create-program
             (term (index (tup true false
                               (index (tup true false true) 2)) 2)))
            (term
             (()
              ((Var true)
               (Var1 false)
               (Var2 true)
               (Var3 false)
               (Var4 true)
               (Var5 (tup Var2 Var3 Var4))
               (Var6 2)
               (Var7 (tup Var Var1 Var4))
               (Var8 2))
              Var4)))

  (test-results))

(define (program-test-suite)

  (test-->> baby-rust-red
            (term (((f (fn (type int -> int) (param x) (x + 1))))
                   ()
                   (f 3)))
            (term
             (((f (fn (type int -> int)
                      (param x)
                      (x + 1))))
              ((Var 3)
               (Var1 3)
               (Var2 1)
               (Var3 4))
              Var3)))

  ;; Names of formal parameters don't matter.
  (test-->> baby-rust-red
            (term (((f (fn (type int -> int)
                           (param Var)
                           (Var + 1))))
                   ()
                   (f 3)))
            (term
             (((f (fn (type int -> int)
                      (param Var)
                      (Var + 1))))
              ((Var 3)
               (Var1 3)
               (Var2 1)
               (Var3 4))
              Var3)))
  
  (test-->> baby-rust-red
            (term (((f (fn (type int -> int)
                           (param Var2)
                           (Var2 + 1))))
                   ()
                   (f 3)))
            (term
             (((f (fn (type int -> int)
                      (param Var2)
                      (Var2 + 1))))
              ((Var 3)
               (Var1 3)
               (Var2 1)
               (Var3 4))
              Var3)))

  (test-->> baby-rust-red
            (term (((f (fn (type int -> int)
                           (param x)
                           (square (square x))))
                    (square (fn (type int -> int)
                                (param x)
                                (x * x))))
                   ()
                   (f 3)))
            (term (((f (fn (type int -> int)
                           (param x)
                           (square (square x))))
                    (square (fn (type int -> int)
                                (param x)
                                (x * x))))
                   ((Var 3)
                    (Var1 3)
                    (Var2 3)
                    (Var3 9)
                    (Var4 9)
                    (Var5 81))
                   Var5)))

  (test-equal
   (make-value (term (tup (deref (box (deref (box (3 + 3))))))))
   (term (tup 6)))

  (test-results))

(define (test-all)
  (typeck-test-suite)
  (meta-test-suite)
  (expr-test-suite)
  (program-test-suite))

