From Formalizing.Stlc Require Export lang.

(** This file defines notations and coercions for the STLC language. *)

(** Coercions to make programs easier to type. *)
Coercion of_val : val >-> expr.
Coercion App : expr >-> Funclass.
Coercion Var : string >-> expr.

(** Define some derived forms. *)
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).


(** Lambda syntax inspired by Coq. *)
(** The [λ] notation is used for lambda abstractions, with the binder being either a
  * named variable or an anonymous binder. The [λ] notation is defined in two
  * scopes: [expr_scope] for expressions and [val_scope] for values. The [λ]
  * notation allows for multiple binders in a single lambda abstraction, similar to
  * how it is done in Coq. *)
Notation "λ: x , e" := (Lam x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x%binder (Lam y%binder .. (Lam z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "λ: x , e" := (LamV x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:'  x ,  '/  ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (LamV x%binder (Lam y%binder .. (Lam z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : val_scope.

(** Syntactic sugar for let-binding and sequencing. *)
Notation "'let:' x := e1 'in' e2" := (Let x%binder e1%E e2%E)
  (only parsing, at level 200, x at level 1, e1, e2 at level 200) : expr_scope.
Notation "e1 ;; e2" := (Seq e1%E e2%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.