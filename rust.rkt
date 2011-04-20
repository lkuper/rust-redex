#lang racket
(require redex)

(define-language baby-rust

  ;; TODO: Figure out how to model the heap and stack.
  
  ;; Programs.
  (Program (Items Heap Expr))
  ;; A baby-rust program, as the programmer writes it, comprises zero
  ;; or more Items followed by a Main expression.  As the program
  ;; runs, heap values (Hvals) are allocated.

  ;; NB: If we do it this way then we have to sometimes look both in
  ;; Items and in Heap for a bound variable.

  (Heap ((Var Hval) ...))

  ;; Results.
  (Result (Items Heap Var))
  ;; This is what you get when you're done running a baby-rust
  ;; program.  Var should be bound to something in the heap.

  ;; Items.
  (Items ((Var Item) ...))
  (Item FnDefn TyDefn)
  ;; In Rust, 'items' include modules, function definitions,
  ;; iterators, objects, and type definitions.  We're just modeling
  ;; function and type definitions right now.  ('Definitions' might be
  ;; a better word than 'items' for everything in this syntactic
  ;; category.)

  ;; In Rust, since modules can nest, items aren't entirely top-level,
  ;; just top-level within a module.  But in baby-rust, since we're
  ;; not modeling modules yet, our Items really are top-level.

  ;; Type definitions.
  (TyDefn (type Ty))

  ;; Function definitions.
  (FnDefn (fn (type Ty -> Ty) (param Var) Expr))
  ;; A function definition, comprising a type, a formal parameter
  ;; name, and a body. Note that in baby-rust, functions can only take
  ;; one argument.

  ;; Base types.
  (BaseTy int bool)
  
  ;; Types.
  (Ty BaseTy (Ty -> Ty) (Tup Ty ...) (Box Ty))
  ;; baby-rust types include base types, function types, tuple types,
  ;; and box types.

  ;; In Rust, box types and tuple types carry mutability annotations
  ;; (mutable, immutable, or maybe mutable).  In tuple types, each
  ;; element contains its own mutability annotation (as opposed to
  ;; Rust vectors, in which either the entire vector is mutable or it
  ;; isn't).  We're not modeling any mutability information yet.

  ;; Expressions.
  (Expr Lit
        (Unary Expr)
        (Expr Binary Expr)
        (tup Expr ...)
        (Expr Expr)
        (let Ty LVal = Expr)
        Var
        Index)
  ;; baby-rust expressions include literals, unary and binary
  ;; operations, tuples, "call expressions" (applications),
  ;; assignments, "path expressions" (variables), and index
  ;; expressions.

  ;; Unops and binops.
  (Op Unary Binary)
  ;; Convenient for defining lookup-op.
  
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

  ;; Type environments
  (gamma empty (gamma Var Ty))
  ;; A type environment is a mapping, possibly empty, of bindings from
  ;; variables to types.

  ;; Values
  (Value Lit (tup Value ...) (box Value))

  ;; Evaluation contexts
  (EvalCtxt hole
            (EvalCtxt Expr)
            (Var EvalCtxt)
            (Unary EvalCtxt)
            (EvalCtxt Binary Expr)
            (Var Binary EvalCtxt)
            (tup Var ... EvalCtxt Expr ...)
            (deref EvalCtxt)
            (box EvalCtxt)
            (index (tup Var ... EvalCtxt Expr ...) Expr)
            (index Var EvalCtxt))

  ;; Heap values
  (Hval Value)

  ;; Instructions.
  (Instr Hval
         (Var Var)
         (Unary Var)
         (Var Binary Var)
         (tup Var ...)
         (deref Var)
         (box Var)
         (index Var Var))
  ;; An Instr is something that we have to define the ---> reduction
  ;; relation on.  Expressions have to keep being evaluated using the
  ;; standard --> reduction semantics, but Instrs mean that we either
  ;; have to allocate something in the heap, look something up in the
  ;; heap, or maybe both.

  ;; Unary expressions
  (Unary neg not)
  ;; A few of what Rust offers.

  ;; Binary expressions
  (Binary + - *)
  ;; A few of what Rust offers.

  ;; Tuple indexing
  (Index (index (tup Expr ...) Expr))

  ;; Literals
  (Lit number false true)

  ;; Variables
  (Var variable-not-otherwise-mentioned)
  ;; Any symbol not mentioned as a literal in the grammar of the
  ;; language is fair game to be a variable.

  ;; Domain of the typeck metafunction
  (Expr/FnDefn Expr FnDefn)

  ;; Range of the typeck metafunction
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
         (where (Var_1 (fn (type Ty_1 -> Ty_2) (param Var_3) Expr))
                (item-lookup Items Var_1))

         ;; Make sure that Var is really a fresh name, so we don't
         ;; conflict with bindings already in the heap.
         (where Var ,(variable-not-in (term Heap) (term Var)))
         "App")
   
   (---> (Items Heap
          (in-hole EvalCtxt
                   (Op Var)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-op Op Heap Var)))
         "UnaryOp")

   (---> (Items Heap
          (in-hole EvalCtxt
                   (Var_1 Op Var_2)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-op Op Heap Var_1 Var_2)))
         "BinaryOp")

   (---> (Items Heap
          (in-hole EvalCtxt
                   (index (tup Var ...) number)))
         (Items Heap
          (in-hole EvalCtxt
                   ,(list-ref (term (Var ...)) (term number))))
         "Index")

   (---> (Items Heap
          (in-hole EvalCtxt
                   (deref (box Var)))) 
         (Items Heap
          (in-hole EvalCtxt
                   Var))
         "Deref")
   
   with
   [(--> (in-hole EvalCtxt a) (in-hole EvalCtxt b)) (---> a b)]))

(define-metafunction baby-rust
  heap-lookup : Heap Var -> Hval
  [(heap-lookup Heap Var) ,(second (assq (term Var) (term Heap)))])

(define-metafunction baby-rust
  item-lookup : Items Var -> Item
  [(item-lookup Items Var) (assq (term Var) (term Items))])

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
  lookup-op : Op Heap Var ... -> Value
  [(lookup-op + Heap Var_1 Var_2) ,(+ (term (heap-lookup Heap Var_1))
                                      (term (heap-lookup Heap Var_2)))]
  [(lookup-op - Heap Var_1 Var_2) ,(- (term (heap-lookup Heap Var_1))
                                      (term (heap-lookup Heap Var_2)))]
  [(lookup-op * Heap Var_1 Var_2) ,(* (term (heap-lookup Heap Var_1))
                                      (term (heap-lookup Heap Var_2)))]
  [(lookup-op neg Heap Var) ,(- (term (heap-lookup Heap Var)))]

  ;; FIXME.
  [(lookup-op not Heap Var) ,(not (term (heap-lookup Heap Var)))])

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
            (term (()
                   ((Var 3))
                   Var)))

  (test-->> baby-rust-red
            (create-program (term (3 + 3)))
            (term (()
                   ((Var 3)
                    (Var1 3)
                    (Var2 6))
                   Var2)))

  (test-->> baby-rust-red
            (create-program (term (3 + (2 + 1))))
            (term (()
                   ((Var 3)
                    (Var1 2)
                    (Var2 1)
                    (Var3 3)
                    (Var4 6))
                   Var4)))

  (test-->> baby-rust-red
            (create-program (term ((3 + 2) + 1)))
            (term (()
                   ((Var 3)
                    (Var1 2)
                    (Var2 5)
                    (Var3 1)
                    (Var4 6))
                   Var4)))

  (test-->> baby-rust-red
            (create-program (term true))
            (term (()
                   ((Var true))
                   Var)))

  (test-->> baby-rust-red
            (create-program (term (not true)))
            (term (()
                   ((Var false))
                   Var)))

  (test-->> baby-rust-red
            (term (deref (box 3)))
            (term 3))

  (test-->> baby-rust-red
            (term (deref (box (3 + 3))))
            (term 6))

  (test-->> baby-rust-red
            (term (deref (box (not (not false)))))
            (term false))

  (test-->> baby-rust-red
            (term (tup 1 2 3))
            (term (tup 1 2 3)))

  (test-->> baby-rust-red
            (term (tup 1 2 (3 + 3)))
            (term (tup 1 2 6)))

  (test-->> baby-rust-red
            (term (index (tup 1 2 (3 + 3)) 0))
            (term 1))

  (test-->> baby-rust-red
            (term (index (tup 1 2 (3 + 3)) 2))
            (term 6))

  (test-->> baby-rust-red
            (term (tup true false (index (tup true false true) 2)))
            (term (tup true false true)))

  (test-->> baby-rust-red
            (term (index (tup true false (index (tup true false true) 2)) 0))
            (term true))

  (test-->> baby-rust-red
            (term (index (tup true false (index (tup true false true) 2)) 2))
            (term true))

  (test-results))

(define (program-test-suite)
  
  (test-->> baby-rust-red
            (term (((x (type int))
                    (f (fn (type int -> int) (param x) (x + 1))))
                   ()
                   (f 3)))
            (term (((x (type int))
                    (f (fn (type int -> int) (param x) (x + 1))))
                   () ;; some bindings in here
                   Var5)) ;; or something
)

  (test-results))


