Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.Stlc Require Import notation free_variables.
From Intro2TT Require Import Tactics.

(** ** Alpha Equivalence *)
(** This file defines the notion of alpha equivalence for expressions in the
    Stlc language. Alpha equivalence is a relation that identifies expressions
    that differ only by the names of their bound variables. *)

Definition binding_var (e : expr) : option string :=
  match e with
  | Lam (BNamed x) _ => Some x
  | _ => None
  end.
Inductive alpha_equiv : expr → expr → Prop :=
  | ARename x y e :
      y ∉ FV e →
      Some y ≠ binding_var e →
      alpha_equiv (λ: x, e) (λ: y, subst' x y e)
  | ACompatLam e1 e2 x :
      alpha_equiv e1 e2 →
      alpha_equiv (λ: x, e1) (λ: x, e2)
  | ACompatAppL e1 e2 e :
      alpha_equiv e1 e2 →
      alpha_equiv (App e1 e) (App e2 e)
  | ACompatAppR e1 e2 e :
      alpha_equiv e1 e2 →
      alpha_equiv (App e e1) (App e e2)
  | ARefl e :
      alpha_equiv e e
  | ASym e1 e2 :
      alpha_equiv e1 e2 →
      alpha_equiv e2 e1
  | ATrans e1 e2 e3 :
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
  apply ACompatAppL; eauto.
  etrans; [apply (ARename _ "u"); by eauto|simpl].
  etrans; [|apply ASym, (ARename _ "u"); by eauto]. simpl.
  apply ACompatLam, ACompatAppR, ARename; by eauto.
Qed.


(** Compatibility Lemmas *)
Lemma alpha_compatApp e1 e2 e3 e4 :
  e1 ≡ₐ e2 → e3 ≡ₐ e4 → e1 e3 ≡ₐ e2 e4.
Proof. (* TODO *) Admitted.

Lemma alpha_compatLam x e1 e2 :
  e1 ≡ₐ e2 → (λ: x, e1) ≡ₐ (λ: x, e2).
Proof. (* TODO *) Admitted.

Lemma alpha_subst x e1 e2 es1 es2 :
  e1 ≡ₐ e2 → es1 ≡ₐ es2 → subst x es1 e1 ≡ₐ subst x es2 e2.
Proof. (* TODO *) Admitted.
Lemma alpha_subst' x e1 e2 es1 es2 :
  e1 ≡ₐ e2 → es1 ≡ₐ es2 → subst' x es1 e1 ≡ₐ subst' x es2 e2.
Proof. destruct x; simpl; eauto using alpha_subst. Qed.