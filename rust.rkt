#lang racket
(require redex)

(define-language baby-rust
  ;; Base types
  (BaseTy int bool)
  ;; baby-rust only has one base type, int.
  
  ;; Types
  (Ty BaseTy (Ty -> Ty) (Tup Ty ...) (Box Ty))
  ;; baby-rust types include base types, function types, tuple types,
  ;; and box types.

  ;; In Rust, box types and tuple types carry mutability annotations
  ;; (mutable, immutable, or maybe mutable).  In tuple types, each
  ;; element contains its own mutability annotation (as opposed to
  ;; Rust vectors, in which either the entire vector is mutable or it
  ;; isn't).  We're not modeling any mutability information yet.

  ;; In Rust, functions carry an effect annotation (pure, impure, or
  ;; unsafe) which we're not modeling yet.

  ;; Expressions
  (Expr Lit (Op Expr Expr ...) (fn Ty Var -> Ty { Expr }) (tup Expr ...)
        (Expr Expr) (let Ty LVal = Expr))
  ;; baby-rust expressions include literals, unary expressions, binary
  ;; expressions, functions, tuples, tuple indices, "call expressions"
  ;; (applications), and assignments.  In this model, functions can
  ;; only take one argument.

  ;; Tuple indices can be expressions, but they have to evaluate to a
  ;; number.

  ;; LVals
  (Lval Var (index (tup Val ...) number))
  ;; In real Rust, lvals (things on the left side of an assignment)
  ;; can include paths (the namespacey generalization of variables),
  ;; fields (of records and objects), indices (of vectors and tuples),
  ;; and self-methods (self.foo).  We don't have any of those things
  ;; in our model except for variables and tuple indices.

  ;; Type environments
  (gamma empty (gamma Var Ty))
  ;; A type environment is a mapping, possibly empty, of bindings from
  ;; variables to types.

  ;; Values
  (Value Lit (fn Ty Var -> Ty { Expr }) (tup Value ...))

  ;; Evaluation contexts
  (EvalCtxt hole (EvalCtxt Expr) (Value EvalCtxt) (Unary EvalCtxt)
            (EvalCtxt Binary Expr)
            (Value Binary EvalCtxt)
            (tup Value ... EvalCtxt Expr ...))

  (Op Unary Binary)

  ;; Unary expressions
  (Unary box deref index neg not)
  ;; A few of what Rust offers.  NB: Lower-case 'box' is term-level
  ;; box, rather than the type Box.

  ;; Binary expressions
  (Binary + - *)
  ;; A few of what Rust offers.

  ;; Literals
  (Lit number false true)

  ;; Variables
  (Var variable-not-otherwise-mentioned)

  ;; Range of the typeck metafunction
  (Ty/illtyped Ty illtyped)
)

(define baby-rust-red
  (reduction-relation
   baby-rust

   ;; TODO: write subst
   (---> ((fn Ty Var -> Ty { Expr }) Value)
         (subst Var Value Expr))
   (---> (op Value ...)
         (lookup-op op Value ...))
   with
   [(--> (in-hole E a) (in-hole E b)) (---> a b)]))

(define-metafunction baby-rust
  lookup-op : op Value ... -> Value
  [(lookup-op + number_1 number_2) ,(+ (term number_1) (term number_2))]
  [(lookup-op - number_1 number_2) ,(- (term number_1) (term number_2))]
  [(lookup-op * number_1 number_2) ,(* (term number_1) (term number_2))]
  [(lookup-op neg number) ,(- (term number))]
  [(lookup-op not true) false]
  [(lookup-op not false) true]
  [(lookup-op box Value) (box Value)]
  [(lookup-op deref (box Value)) Value]
  [(lookup-op index number (tup Value ...))
   ,(list-ref (term (Value ...)) (term number))]
  )

(define-metafunction baby-rust
  typeck : gamma Expr -> Ty/illtyped

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
  [(typeck gamma (fn Ty_1 Var -> Ty_2 { Expr }))
   (Ty_1 -> Ty_2)
   (where Ty_2 (typeck (gamma Var Ty_1) Expr))]

  ;; Call expressions
  [(typeck gamma (Expr_1 Expr_2))
   Ty_2
   (where (Ty_1 -> Ty_2) (typeck gamma Expr_1))
   (where Ty_1 (typeck gamma Expr_2))]

  ;; Tuple types
  [(typeck gamma (Tup Expr ...))
   (Tup Ty ...)
   (where (Ty ...) ((typeck gamma Expr) ...))]

  ;; Box types
  [(typeck gamma (Box Expr))
   (Box Ty)
   (where Ty (typeck gamma Expr))]

  ;; Fall-through
  [(typeck gamma Expr) illtyped])

(define-metafunction baby-rust
  typeck-Lit : Lit -> BaseTy
  [(typeck-Lit number) int]
  [(typeck-Lit false) bool]
  [(typeck-Lit true) bool])
