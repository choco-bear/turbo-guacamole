Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.StlcMore Require Import notation syn_type ctx_step.
From Intro2TT Require Import Tactics.

(** ** Contextual typing for the STLC language *)
(** This file defines contextual typing for the simply typed lambda calculus (STLC)
  * language. *)

Definition ctx_type (K : ectx) (A B : ty) : Prop :=
  ∀ e, ∅ ⊢ e : A → ∅ ⊢ fill K e : B.


Lemma decomposition_ctx_type K A e :
  ∅ ⊢ fill K e : A →
  ∃ B, ctx_type K B A ∧ ∅ ⊢ e : B.
Proof.
  induction K in e, A |-*; ii; unfold ctx_type in *; simpl in *.
  all: repeat match goal with
  | IH : ∀ A e, _ ⊢ fill ?K _ : _ → _,
    H  : _ ⊢ fill ?K _ : _ |- _ =>
      apply IH in H as (? & ? & ?)
  | H : _ ⊢ App _ _ : _ |- _ =>
      eapply app_inversion in H as (? & ? & ?)
  | H : _ ⊢ UnOp ?op _ : _ |- _ =>
      destruct op; eapply un_op_inversion in H as [? ?]
  | H : _ ⊢ BinOp ?op _ _ : _ |- _ =>
      destruct op; eapply bin_op_inversion in H as (? & ? & ?)
  | H : _ ⊢ If _ _ _ : _ |- _ =>
      eapply if_inversion in H as (? & ? & ?)
  | H : _ ⊢ (_, _) : _ |- _ =>
      eapply pair_inversion in H as (? & ? & ? & ? & ?)
  | H : _ ⊢ Fst _ : _ |- _ =>
      eapply fst_inversion in H as [? ?]
  | H : _ ⊢ Snd _ : _ |- _ =>
      eapply snd_inversion in H as [? ?]
  | H : _ ⊢ InjL _ : _ |- _ =>
      eapply injL_inversion in H as (? & ? & ? & ?)
  | H : _ ⊢ InjR _ : _ |- _ =>
      eapply injR_inversion in H as (? & ? & ? & ?)
  | H : _ ⊢ Case _ _ _ : _ |- _ =>
      eapply case_inversion in H as (? & ? & ? & ? & ?)
  end; subst; eauto.
Qed.

Lemma composition_ctx_type K A B e :
  ctx_type K B A →
  ∅ ⊢ e : B →
  ∅ ⊢ fill K e : A.
Proof. unfold ctx_type; eauto. Qed.

