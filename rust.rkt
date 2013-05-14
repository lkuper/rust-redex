#lang racket
(require redex)

(provide baby-rust
         baby-rust-red
         typeck
         make-value
         result-value
         create-program)

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
  (Ty BaseTy (Ty Ty ... -> Ty) (Tup Ty ...) (Box Ty))
  ;; Types in baby-rust include base types, function types, tuple
  ;; types, and box types.  Multiple types to the left of the arrow
  ;; have to be OK because built-ins like + have that type.  We're not
  ;; modeling any mutability information for box and tuple types yet.

  ;; Expressions.
  (Expr Lit
        (Unary Expr)
        (Expr Binary Expr)
        (tup Expr ...)
        (deref Expr)
        (box Expr)
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

  ;; TODO: Do we really want to be this limiting?  An arbitrary (Expr
  ;; Expr) could evaluate to an Index or Var expression, right?

  ;; Evaluation contexts.
  (EvalCtxt hole
            (Unary EvalCtxt)
            (EvalCtxt Binary Expr)
            (Var Binary EvalCtxt)
            (tup Var ... EvalCtxt Expr ...)
            (deref EvalCtxt)
            (box EvalCtxt)
            (EvalCtxt Expr)
            (Var EvalCtxt)
            (index EvalCtxt Expr)
            (index Var EvalCtxt))

  ;; Heap values.
  (Hval Lit (tup Var ...) (box Var))

  ;; Only for check-result.
  (Val Lit (tup Val ...) (box Val))

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
  (TyEnv ((Var Ty) ...))

  ;; Domain of the typeck metafunction.
  (Expr/FnDefn Expr FnDefn)

  ;; Range of the typeck metafunction.
  (Ty/illtyped Ty illtyped))

(define baby-rust-red
  (reduction-relation
   baby-rust

   ;; Program -> Program/Result

   ;; Allocate Hvals on the heap.
   (--> (Items Heap
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
   (--> (Items Heap
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
   
   (--> (Items Heap
          (in-hole EvalCtxt
                   (Unary Var)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-op Unary Heap Var)))
         "UnaryOp")

   (--> (Items Heap
          (in-hole EvalCtxt
                   (Var_1 Binary Var_2)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-op Binary Heap Var_1 Var_2)))
         "BinaryOp")

   (--> (Items Heap
          (in-hole EvalCtxt
                   (deref Var))) 
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-deref Heap Var)))
         "Deref")

   (--> (Items Heap
          (in-hole EvalCtxt
                   (index Var_1 Var_2)))
         (Items Heap
          (in-hole EvalCtxt
                   (lookup-index Heap Var_1 Var_2)))
         "Index")))

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

;; This is just dumb substitution -- it doesn't have to be
;; capture-avoiding substitution.
(define-metafunction baby-rust
  ;; (subst expr old-var new-expr): Read the arguments left-to-right
  ;; as "expr, but with occurrences of old-var replaced with
  ;; new-expr".

  [(subst Var_1 Var_1 any_1) any_1]

  [(subst (any_2 ...) Var_1 any_1)
   ((subst any_2 Var_1 any_1) ...)]

  [(subst any_2 Var_1 any_1) any_2])

;; Typechecking.
(define-metafunction baby-rust
  typeck : TyEnv Expr/FnDefn -> Ty/illtyped

  ;; Literals
  [(typeck TyEnv Lit) (typeck-Lit Lit)]

  ;; TODO: Maybe generalize unary and binary expressions into one case.

  ;; Unary expressions
  [(typeck TyEnv (Unary Expr))
   Ty
   ;; Unary operator typechecks as Ty_1 -> Ty
   (where (Ty_1 -> Ty) (typeck-Unary Unary))
   ;; Operand typechecks
   (where Ty_1 (typeck TyEnv Expr))]

  ;; Binary expressions
  [(typeck TyEnv (Expr_1 Binary Expr_2))
   Ty
   ;; Binary operator typechecks as Ty_1 Ty_2 -> Ty
   (where (Ty_1 Ty_2 -> Ty) (typeck-Binary Binary))
   ;; Operands typecheck
   (where Ty_1 (typeck TyEnv Expr_1))
   (where Ty_2 (typeck TyEnv Expr_2))]

  ;; Variables
  [(typeck ((Var_1 Ty_1) (Var Ty) ...) Var_1)
   Ty_1]
  [(typeck ((Var_1 Ty_1) (Var Ty) ...) Var_2)
   (typeck ((Var Ty) ...) Var_2)]

  ;; Functions
  [(typeck TyEnv (fn (type Ty_1 -> Ty_2) (param Var) Expr))
   (Ty_1 -> Ty_2)
   ;; Function body needs to have the correct type in an extended type
   ;; environment
   (where Ty_2 (typeck ,(cons (term (Var Ty_1)) (term TyEnv)) Expr))]

  ;; Call expressions
  [(typeck TyEnv (Expr_1 Expr_2))
   Ty_2
   (where (Ty_1 -> Ty_2) (typeck TyEnv Expr_1))
   (where Ty_1 (typeck TyEnv Expr_2))]

  ;; Tuples
  [(typeck TyEnv (tup Expr ...))
   (Tup Ty ...)
   (where (Ty ...) ((typeck TyEnv Expr) ...))]

  ;; Tuple index expressions
  [(typeck TyEnv (index (tup Expr_1 ...) Expr_2))
   Ty
   ;; For these, we need to make sure that Expr_2 has type int and
   ;; that the expr in Expr_1 at that number's position has the type
   ;; Ty.  This involves escaping to Racket to calculate that position
   ;; in the list.

   ;; Index has to be an int
   (where int (typeck TyEnv Expr_2))
   ;; Whole tuple has to typecheck
   (where Ty_1 (typeck TyEnv (tup Expr_1 ...)))

   ;; Evaluate Expr_2 and pull the correct item out of the list.
   ;; (Caveat: Expr_2 better be a closed expression, because we're
   ;; evaluating it with an empty heap and an empty Items list.)
   (where Ty ,(list-ref (cdr (term Ty_1))
                        (make-value (term Expr_2))))]

  ;; Deref expressions
  [(typeck TyEnv (deref Expr))
   ;; The thing we're dereferencing had better be a box
   Ty
   (where (Box Ty) (typeck TyEnv Expr))]

  ;; Boxes
  [(typeck TyEnv (box Expr))
   (Box Ty)
   (where Ty (typeck TyEnv Expr))]

  ;; Fall-through
  [(typeck TyEnv Expr/FnDefn) illtyped])

(define-metafunction baby-rust
  typeck-Lit : Lit -> BaseTy
  [(typeck-Lit number) int]
  [(typeck-Lit false) bool]
  [(typeck-Lit true) bool])

(define-metafunction baby-rust
  typeck-Unary : Unary -> Ty
  [(typeck-Unary neg) (int -> int)]
  [(typeck-Unary not) (bool -> bool)])

(define-metafunction baby-rust
  typeck-Binary : Binary -> Ty
  [(typeck-Binary +) (int int -> int)]
  [(typeck-Binary -) (int int -> int)]
  [(typeck-Binary *) (int int -> int)])

;; It's annoying to have to look at a Result and figure out whether
;; the thing you actually wanted was computed.  That's what
;; result-value is for: it takes a Result and returns a Val, such as 3
;; or (tup true false true) or (box (box 15)).
(define-metafunction baby-rust
  result-value : Result -> Val
  [(result-value (Items Heap Var))
   (recursive-lookup Heap Var)])

(define-metafunction baby-rust
  recursive-lookup : Heap Var -> Val
  [(recursive-lookup Heap Var)
   ,(let ((result (term (heap-lookup Heap Var))))
      (cond
        ;; The result of a heap-lookup is going to be an Hval.
        [(redex-match baby-rust Lit (term ,result))
         ;; It's a Lit.
         result]
        [(redex-match baby-rust (box Var_1) (term ,result))
         ;; It's a box.
         (term (box (recursive-lookup Heap ,(second (term ,result)))))]
        [(redex-match baby-rust (tup Var_1 ...) (term ,result))
         ;; It's a tuple.

         ;; Augh, wish I could figure out a way to do this with
         ;; ellipses...
         (cons 'tup
               (map (lambda (v)
                      (term (recursive-lookup Heap ,v)))
                    (cdr result)))]))])

;; Wraps a term in the extra stuff (Heap and Items) to make an entire
;; Program.
(define (create-program t)
  (term (()
         ()
         ,t)))

(define (make-value t)
  ;; make-value : term -> term
  ;; Wraps t in a dummy program, reduces it, takes the first (only, I
  ;; hope) Result from reduction, and converts it to a Value.  Useful
  ;; for testing and for partial evaluation during typechecking.
  (term (result-value
          ,(first
            (apply-reduction-relation*
             baby-rust-red
             (create-program
              t))))))
