Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.SystemF Require Import lang notation types.
From Intro2TT Require Import Tactics.

(** ** Contextual typing for the System F *)
(** This file defines contextual typing for the System F. *)

Implicit Types
  (K : ectx)
  (A B : ty)
  (e : expr).

Definition ctx_type K A B : Prop :=
  ∀ e, TY 0; ∅ ⊢ e : A → TY 0; ∅ ⊢ fill K e : B.

Lemma decomposition_ctx_type K A e :
  TY 0; ∅ ⊢ fill K e : A →
  ∃ B, ctx_type K B A ∧ TY 0; ∅ ⊢ e : B.
Proof.
  induction K in e, A |-*; ii; unfold ctx_type in *; simpl in *.
  all: repeat match goal with
  | IH : ∀ A e, TY _; _ ⊢ fill ?K _ : _ → _,
    H  : TY _; _ ⊢ fill ?K _ : _ |- _ =>
      apply IH in H as (? & ? & ?)
  | H : TY _; _ ⊢ App _ _ : _ |- _ =>
      eapply app_inversion in H as (? & ? & ?)
  | H : TY _; _ ⊢ _ <> : _ |- _ =>
      eapply tapp_inversion in H as (? & ? & ? & ? & ?)
  | H : TY _; _ ⊢ (pack _) : _ |- _ =>
      eapply pack_inversion in H as (? & ? & ? & ? & ? & ?)
  | H : TY _; _ ⊢ (unpack _ as <> in _) : _ |- _ =>
      eapply unpack_anon_inversion in H as (? & ? & ? & ?)
  | H : TY _; _ ⊢ (unpack _ as BNamed _ in _) : _ |- _ =>
      eapply unpack_inversion in H as (? & ? & ? & ?)
  | H : TY _; _ ⊢ (unpack _ as ?x in _) : _ |- _ =>
      destruct x
  | H : TY _; _ ⊢ UnOp _ _ : _ |- _ =>
      eapply un_op_inversion in H as (? & ? & ?)
  | H : TY _; _ ⊢ BinOp _ _ _ : _ |- _ =>
      eapply bin_op_inversion in H as (? & ? & ? & ? & ?)
  | H : TY _; _ ⊢ If _ _ _ : _ |- _ =>
      eapply if_inversion in H as (? & ? & ?)
  | H : TY _; _ ⊢ (_, _) : _ |- _ =>
      eapply pair_inversion in H as (? & ? & ? & ? & ?)
  | H : TY _; _ ⊢ Fst _ : _ |- _ =>
      eapply fst_inversion in H as [? ?]
  | H : TY _; _ ⊢ Snd _ : _ |- _ =>
      eapply snd_inversion in H as [? ?]
  | H : TY _; _ ⊢ InjL _ : _ |- _ =>
      eapply injL_inversion in H as (? & ? & ? & ? & ?)
  | H : TY _; _ ⊢ InjR _ : _ |- _ =>
      eapply injR_inversion in H as (? & ? & ? & ? & ?)
  | H : TY _; _ ⊢ Case _ _ _ : _ |- _ =>
      eapply case_inversion in H as (? & ? & ? & ? & ?)
  end; subst; eauto.
Qed.

Lemma composition_ctx_type K A B e :
  ctx_type K B A →
  TY 0; ∅ ⊢ e : B →
  TY 0; ∅ ⊢ fill K e : A.
Proof. unfold ctx_type; eauto. Qed.