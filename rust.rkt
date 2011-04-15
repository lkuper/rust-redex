#lang racket
(require redex)

(define-language baby-rust
  
  ;; Programs
  (Program (Item ... Main))
  ;; A baby-rust program comprises zero or more top-level Items
  ;; followed by a Main expression, which is just a distinguished kind
  ;; of function.

  ;; Items
  (Item Fn Ty)
  ;; In Rust, 'items' include modules, functions, iterators, objects,
  ;; and types.  We're just modeling functions and types right now.  A
  ;; better word for these might be 'definitions'.  In Rust, since
  ;; modules can nest, items aren't entirely top-level, but they're
  ;; top-level within a module.  But for us, since we're not modeling
  ;; modules yet, our Items really are top-level.

  ;; Functions
  (Fn (fn Ty Var -> Ty { Expr }))
  ;; This just exists so I don't have to write out (fn ... ) in as
  ;; many places.

  ;; Main expressions
  (Main Fn)
  ;; TODO: is there some special subset of functions that Main can be?
  ;; Is its type constrained at all?
  
  ;; Base types
  (BaseTy int bool)
  
  ;; Types
  (Ty BaseTy (Ty -> Ty) (Tup Ty ...) (Box Ty))
  ;; baby-rust types include base types, function types, tuple types,
  ;; and box types.

  ;; In Rust, box types and tuple types carry mutability annotations
  ;; (mutable, immutable, or maybe mutable).  In tuple types, each
  ;; element contains its own mutability annotation (as opposed to
  ;; Rust vectors, in which either the entire vector is mutable or it
  ;; isn't).  We're not modeling any mutability information yet.

  ;; Expressions
  (Expr Lit (Op Expr Expr ...) (tup Expr ...) (Expr Expr) (let Ty LVal = Expr))
  (Op Unary Binary)
  ;; baby-rust expressions include literals, unary and binary
  ;; operations (which include tuple indexing operations), functions,
  ;; tuples, "call expressions" (applications), and assignments.  In
  ;; this model, functions can only take one argument.

  ;; LVals
  (LVal Var (index (tup Expr ...) Expr))
  ;; In real Rust, lvals (expressions that can appear on the left side
  ;; of an assignment) can include path expressions (the namespacey
  ;; generalization of variables), field expressions (of records and
  ;; objects), index expressions (of vectors and tuples), and
  ;; self-methods (self.foo).  We don't have any of those things in
  ;; our model except for variables and tuple indices.

  ;; NB: Tuple indices have to evaluate to a number.

  ;; Type environments
  (gamma empty (gamma Var Ty))
  ;; A type environment is a mapping, possibly empty, of bindings from
  ;; variables to types.

  ;; Values
  (Value Lit (tup Value ...))

  ;; Evaluation contexts
  (EvalCtxt hole (EvalCtxt Expr) (Value EvalCtxt) (Unary EvalCtxt)
            (EvalCtxt Binary Expr)
            (Value Binary EvalCtxt)
            (tup Value ... EvalCtxt Expr ...))

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

  ;; Domain of the typeck metafunction
  (Expr/Fn Expr Fn)

  ;; Range of the typeck metafunction
  (Ty/illtyped Ty illtyped)
)

(define baby-rust-red
  (reduction-relation
   baby-rust

   ;; TODO: This isn't right.  Before we model reduction we're going
   ;; to have to model the heap and stack.  See: \gc?
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
  typeck : gamma Expr/Fn -> Ty/illtyped

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

  ;; Tuples
  [(typeck gamma (Tup Expr ...))
   (Tup Ty ...)
   (where (Ty ...) ((typeck gamma Expr) ...))]

  ;; Boxes
  [(typeck gamma (Box Expr))
   (Box Ty)
   (where Ty (typeck gamma Expr))]

  ;; Fall-through
  [(typeck gamma Expr/Fn) illtyped])

(define-metafunction baby-rust
  typeck-Lit : Lit -> BaseTy
  [(typeck-Lit number) int]
  [(typeck-Lit false) bool]
  [(typeck-Lit true) bool])
