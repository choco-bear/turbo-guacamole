Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.StlcMore Require Import notation free_variables.
From Intro2TT Require Import Tactics.

(** ** Alpha Equivalence *)
(** This file defines the notion of alpha equivalence for expressions in the
    StlcMore language. Alpha equivalence is a relation that identifies expressions
    that differ only by the names of their bound variables. *)

Definition binding_var (e : expr) : option string :=
  match e with
  | Lam (BNamed x) _ => Some x
  | _ => None
  end.
Inductive alpha_equiv : expr → expr → Prop :=
  | alpha_rename x y e :
      y ∉ FV e →
      Some y ≠ binding_var e →
      alpha_equiv (λ: x, e) (λ: y, subst' x y e)
  | alpha_compatAppL e1 e2 e :
      alpha_equiv e1 e2 →
      alpha_equiv (App e1 e) (App e2 e)
  | alpha_compatAppR e1 e2 e :
      alpha_equiv e1 e2 →
      alpha_equiv (App e e1) (App e e2)
  | alpha_compatLam e1 e2 x :
      alpha_equiv e1 e2 →
      alpha_equiv (λ: x, e1) (λ: x, e2)
  | alpha_refl e :
      alpha_equiv e e
  | alpha_sym e1 e2 :
      alpha_equiv e1 e2 →
      alpha_equiv e2 e1
  | alpha_trans e1 e2 e3 :
      alpha_equiv e1 e2 →
      alpha_equiv e2 e3 →
      alpha_equiv e1 e3
  .
#[export] Hint Constructors alpha_equiv : core.
Global Instance alpha_equiv_equivalence : Equivalence alpha_equiv. split; eauto. Defined.

(* We also define a more readable notation for alpha equivalence, using '≡ₐ'. *)
Notation "e1 '≡ₐ' e2" := (alpha_equiv e1%E e2%E) (at level 70) : stdpp_scope.
Notation "e1 '≢ₐ' e2" := (¬ alpha_equiv e1%E e2%E) (at level 70) : stdpp_scope.

(** Examples *)
Goal (λ: "x", "x" (λ: "z", "x" "y")) "z" ≡ₐ (λ: "z", "z" (λ: "x", "z" "y")) "z".
Proof.
  apply alpha_compatAppL; eauto.
  etrans; [apply (alpha_rename _ "u"); by eauto|simpl].
  etrans; [|apply alpha_sym, (alpha_rename _ "u"); by eauto]. simpl.
  apply alpha_compatLam, alpha_compatAppR, alpha_rename; by eauto.
Qed.