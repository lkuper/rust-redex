#lang racket
(require redex)

(define-language baby-rust

  ;; TODO: Figure out how to model the stack.
  ;; TODO: Figure out how to model assignment.

  ;; Programs.
  (Program (Items Heap Expr))
  ;; A baby-rust program comprises:
  ;;
  ;;   * A list of zero or more Items
  ;;   * A list, initially empty, for the heap
  ;;   * A "main" expression
  ;;
  ;; As the program runs, the heap grows.

  ;; Items.
  (Items ((Var Item) ...))
  (Item FnDefn TyDefn)
  ;; The Items list is a list of bindings from variables to Items,
  ;; which may be function definitions or type definitions.
  
  ;; In real Rust, modules, objects, and iterators are also items, and
  ;; since modules can nest, items aren't entirely top-level, just
  ;; top-level within a module.  But in baby-rust, Items really are
  ;; top-level.

  ;; Heaps.
  (Heap ((Var Hval) ...))
  ;; A Heap is a list of bindings from variables to Hvals.

  ;; Results.
  (Result (Items Heap Var))
  ;; A Result is what you get when you're done running a baby-rust
  ;; program.  It comprises:
  ;;
  ;;   * A list of zero or more Items
  ;;   * A list containing everything that was allocated on the heap
  ;;   * A variable that points into the heap at the result of the
  ;;     program

  ;; Function definitions.
  (FnDefn (fn (type Ty -> Ty) (param Var) Expr))
  ;; A function definition comprises an 'fn tag, a type, a formal
  ;; parameter name, and a body. Note that in baby-rust, functions can
  ;; only take one argument.

  ;; Type definitions.
  (TyDefn (type Ty))

  ;; Base types.
  (BaseTy int bool)

  ;; Types.
  (Ty BaseTy (Ty -> Ty) (Tup Ty ...) (Box Ty))
  ;; Types in baby-rust include base types, function types, tuple
  ;; types, and box types.  We're not modeling any mutability
  ;; information for box and tuple types yet.

  ;; Expressions.
  (Expr Lit
        (Unary Expr)
        (Expr Binary Expr)
        (tup Expr ...)
        (Expr Expr)
        (let Ty Lval = Expr)
        Var
        Index)
  ;; baby-rust expressions include literals, unary and binary
  ;; operations, tuples, "call expressions" (applications),
  ;; assignments, "path expressions" (variables), and index
  ;; expressions.

  ;; Built-in operators.
  (Op Unary Binary)

  ;; Lvals.
  (Lval Var Index)
  ;; In real Rust, lvals (expressions that can appear on the left side
  ;; of an assignment) can include path expressions (the namespacey
  ;; generalization of variables), field expressions (of records and
  ;; objects), index expressions (of vectors and tuples), and
  ;; self-methods (self.foo).  We don't have any of those things in
  ;; our model except for variables and tuple indices.

  ;; TODO: Do we really just want Expr here?  An arbitrary expression
  ;; could evaluate to an Index expression, right?

  ;; Evaluation contexts.
  (EvalCtxt hole
            (EvalCtxt Expr)
            (Var EvalCtxt)
            (Unary EvalCtxt)
            (EvalCtxt Binary Expr)
            (Var Binary EvalCtxt)
            (tup Var ... EvalCtxt Expr ...)
            (deref EvalCtxt)
            (box EvalCtxt)
            (index EvalCtxt Expr)
            (index Var EvalCtxt))

  ;; Heap values.
  (Hval Lit (tup Var ...) (box Var))

  (Instr Hval
         (Var Var)
         (Unary Var)
         (Var Binary Var)
         (deref Var)
         (index Var Var))
  ;; An Instr is something that we have to define the ---> reduction
  ;; relation on.  Expressions have to keep being evaluated using the
  ;; standard --> reduction semantics, but Instrs mean that we either
  ;; have to allocate something in the heap, look something up in the
  ;; heap, or maybe both.

  ;; Unary operators.
  (Unary neg not)

  ;; Binary operators.
  (Binary + - *)

  ;; Tuple indexing expressions.
  (Index (index (tup Expr ...) Expr))

  ;; Literals.
  (Lit number false true)

  ;; Any symbol not mentioned as a literal in the grammar of the
  ;; language is fair game to be a variable.
  (Var variable-not-otherwise-mentioned)

  ;;; Stuff for typechecking

  ;; A type environment is a mapping, possibly empty, of bindings from
  ;; variables to types.
  (gamma empty (gamma Var Ty))

  ;; Domain of the typeck metafunction.
  (Expr/FnDefn Expr FnDefn)

  ;; Range of the typeck metafunction.
  (Ty/illtyped Ty illtyped))

(define baby-rust-red
  (reduction-relation
   baby-rust

   ;; Program -> Program/Result

   ;; Allocate Hvals on the heap.
   (---> (Items Heap
                (in-hole EvalCtxt
                         Hval))
         (Items ,(append (term Heap) `((,(term Var) ,(term Hval))))
                (in-hole EvalCtxt
                         Var))
         ;; Make sure that Var is a fresh variable, so we don't
         ;; conflict with bindings already in the heap.
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "Alloc")

   ;; If we get to a (Var_1 Var_2) function application, then Var_1 is
   ;; going to point to some function in Items, and Var_2 is going to
   ;; point to some hval in the heap.  (Var_2 can't point to an Item
   ;; -- they're not first-class -- and Var_1 can't point to an hval
   ;; because they can't be functions.)
   (---> (Items Heap
                (in-hole EvalCtxt
                         (Var_1 Var_2)))
         (Items ,(append (term Heap)
                         ;; Put a new binding on the heap
                         `((,(term Var) ,(term (heap-lookup Heap Var_2)))))

                ;; Expr is the body of the function Var_1 points to
                ;; (henceforth "f").  We put Expr in the evaluation
                ;; context, replacing any free occurrences of Var_3
                ;; (which is f's formal parameter) with the fresh name
                ;; Var.
                (in-hole EvalCtxt
                         (subst Expr Var_3 Var)))

         ;; Var_1 should already be the name of some function in
         ;; Items.
         (where (fn (type Ty_1 -> Ty_2) (param Var_3) Expr)
                (item-lookup Items Var_1))

         ;; Make sure that Var is really a fresh name, so we don't
         ;; conflict with bindings already in the heap.
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "App")
   
   (---> (Items Heap
          (in-hole EvalCtxt
                   (Unary Var)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-op Unary Heap Var)))
         "UnaryOp")

   (---> (Items Heap
          (in-hole EvalCtxt
                   (Var_1 Binary Var_2)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-op Binary Heap Var_1 Var_2)))
         "BinaryOp")

   (---> (Items Heap
          (in-hole EvalCtxt
                   (deref Var))) 
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-deref Heap Var)))
         "Deref")

   (---> (Items Heap
          (in-hole EvalCtxt
                   (index Var_1 Var_2)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-index Heap Var_1 Var_2)))
         "Index")

   with
   [(--> (in-hole EvalCtxt a) (in-hole EvalCtxt b)) (---> a b)]))

(define-metafunction baby-rust
  heap-lookup : Heap Var -> Hval
  [(heap-lookup Heap Var) ,(second (assq (term Var) (term Heap)))])

(define-metafunction baby-rust
  item-lookup : Items Var -> Item
  [(item-lookup Items Var) ,(second (assq (term Var) (term Items)))])

;; Don't know if we'll need these next two...

(define-metafunction baby-rust
  fnbody-lookup : Items Var -> Expr
  [(fnbody-lookup Items Var)
   ;; Pull Quux out of a binding that looks like
   ;; (Var (fn (type Foo -> Bar) (param Baz) Quux))
   (fourth (second (assq (term Var) (term Items))))])

(define-metafunction baby-rust
  fnparam-lookup : Items Var -> Var
  [(fnparam-lookup Items Var)
   ;; Pull Baz out of a binding that looks like
   ;; (Var (fn (type Foo -> Bar) (param Baz) Quux))
   (second (third (second (assq (term Var) (term Items)))))])

(define-metafunction baby-rust
  lookup-op : Op Heap Var ... -> Hval
  [(lookup-op + Heap Var_1 Var_2)
   ,(+ (term (heap-lookup Heap Var_1))
       (term (heap-lookup Heap Var_2)))]
  [(lookup-op - Heap Var_1 Var_2)
   ,(- (term (heap-lookup Heap Var_1))
       (term (heap-lookup Heap Var_2)))]
  [(lookup-op * Heap Var_1 Var_2)
   ,(* (term (heap-lookup Heap Var_1))
       (term (heap-lookup Heap Var_2)))]
  [(lookup-op neg Heap Var)
   ,(- (term (heap-lookup Heap Var)))]
  [(lookup-op not Heap Var)
   ,(let ((b (term (heap-lookup Heap Var))))
      (cond
        [(equal? b (term true)) (term false)]
        [(equal? b (term false)) (term true)]))])

(define-metafunction baby-rust
  lookup-deref : Heap Var -> Var
  [(lookup-deref Heap Var)
   ;; second because boxes begin with the tag 'box.
   ,(second (term (heap-lookup Heap Var)))])

(define-metafunction baby-rust
  lookup-index : Heap Var Var -> Var
  [(lookup-index Heap Var_1 Var_2)
   ;; cdr because tuples begin with the tag 'tup.
   ,(list-ref (cdr (term (heap-lookup Heap Var_1)))
              (term (heap-lookup Heap Var_2)))])


;; Capture-avoiding substitution, mostly borrowed from the Redex book,
;; pp. 221-223.
(define-metafunction baby-rust
  ;; (subst expr old-var new-expr): Read the arguments left-to-right
  ;; as "expr, but with free occurrences of old-var replaced with
  ;; new-expr".

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

(define-metafunction baby-rust
  [(subst-var (any_1 ...) Var_1 Var_2)
   ((subst-var any_1 Var_1 Var_2) ...)]
  [(subst-var Var_1 Var_1 Var_2) Var_2]
  [(subst-var any_1 Var_1 Var_2) any_1])

;; Typechecking.  TODO: Make this work!
(define-metafunction baby-rust
  typeck : gamma Expr/FnDefn -> Ty/illtyped

  ;; Literals
  [(typeck gamma Lit) (typeck-Lit Lit)]

  ;; TODO: Maybe generalize unary and binary expressions into one case.

  ;; Unary expressions
  [(typeck gamma (Unary Expr))
   Ty
   ;; Unary operator typechecks as Ty_1 -> Ty
   (where (Ty_1 -> Ty) (typeck-Unary Unary))
   ;; Operand typechecks
   (where Ty_1 (typeck gamma Expr))]

  ;; Binary expressions
  [(typeck gamma (Expr_1 Binary Expr_2))
   Ty
   ;; Binary operator typechecks as Ty_1 Ty_2 -> Ty
   (where (Ty_1 -> Ty) (typeck-Binary Binary ))
   ;; Operands typecheck
   (where Ty_1 (typeck gamma Expr_1))
   (where Ty_2 (typeck gamma Expr_2))]

  ;; Variables
  [(typeck (gamma x Ty) x)
   Ty]
  [(typeck (gamma y Ty) x)
   (typeck gamma x)]

  ;; Functions
  [(typeck gamma (fn (type Ty_1 -> Ty_2) (param Var) Expr))
   (Ty_1 -> Ty_2)
   (where Ty_2 (typeck (gamma Var Ty_1) Expr))]

  ;; Call expressions
  [(typeck gamma (Expr_1 Expr_2))
   Ty_2
   (where (Ty_1 -> Ty_2) (typeck gamma Expr_1))
   (where Ty_1 (typeck gamma Expr_2))]

  ;; Tuples
  [(typeck gamma (Tup Expr ...))
   (Tup Ty ...)
   (where (Ty ...) ((typeck gamma Expr) ...))]

  ;; Tuple index expressions
  [(typeck gamma (index (tup Expr_1 ...) Expr_2))
   Ty
   ;; For these, we need to make sure that Expr_2 is a number, and
   ;; that the expr in Expr_1 at that number's position has the type
   ;; Ty.  This involves escaping to Scheme to calculate that position
   ;; in the list.

   ;; TODO: Am I doinitrite?
   (where number (typeck gamma Expr_2))
   (where Ty (typeck gamma ,(list-ref (term (tup Expr_1 ...)) (term Expr_2))))]

  ;; Boxes
  [(typeck gamma (box Expr))
   (Box Ty)
   (where Ty (typeck gamma Expr))]

  ;; Fall-through
  [(typeck gamma Expr/FnDefn) illtyped])

(define-metafunction baby-rust
  typeck-Lit : Lit -> BaseTy
  [(typeck-Lit number) int]
  [(typeck-Lit false) bool]
  [(typeck-Lit true) bool])

;; Tests

;; Wraps a term in the extra stuff (Heap and Items) to make an entire
;; Program.
(define (create-program t)
  (term (()
         ()
         ,t)))

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

  (test-results))


