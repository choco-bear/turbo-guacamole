Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.SystemF Require Import lang notation tactics types.
From Intro2TT Require Import Tactics.

(** ** Soundness of the System F. *)
(** This file proves the soundness of the System F, showing that if an expression is
  * well-typed, then it can be reduced to a value. *)

Implicit Types
  (e : expr)
  (A : ty).

(** Progress Theorem *)
Theorem typed_progress e A :
  TY 0; ∅ ⊢ e : A →
  reducible e ∨ is_val e.
Proof.
  remember ∅ as Γ; remember 0 as n; induction 1;
  intuition; simplify_val; simpl in *; try rewrite !is_val_of_val;
  match goal with
  | |- _ ∨ True => by right
  | |- _ ∨ False => left
  | |- _ ∨ _ => first [ right; solve_val | left]
  end; subst; first done; eauto; simplify_val_typing.
  all: try match goal with x : bool |- _ => destruct x end;
       apply base_reducible_reducible; unfold base_reducible; simpl; eauto.
Qed.