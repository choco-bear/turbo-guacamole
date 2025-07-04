From Formalizing.StlcMore Require Import steps type.
From Intro2TT Require Import Tactics.

(** ** Soundness of the STLC language. *)
(** This file proves the soundness of the STLC language, showing that if an expression
    is well-typed, then it can be reduced to a value. *)

Lemma typed_substitutivity Γ (x : string) e e' A B :
  ∅ ⊢ e' : A →
  (<[x := A]> Γ) ⊢ e : B →
  Γ ⊢ subst x e' e : B.
Proof.
  intros He'. revert B Γ; induction e; intros B Γ; simpl.
  - intros H%lit_inversion; destruct l; subst; eauto.
  - intros H%var_inversion; destruct (decide (x = x0)); subst.
    + apply lookup_insert_rev in H; subst; eauto using map_empty_subseteq.
    + rewrite (lookup_insert_ne Γ) in H; eauto.
  - destruct x0.
    + intros (C & D & -> & H)%lam_anon_inversion; eauto.
    + intros (C & D & -> & H)%lam_inversion.
      destruct (decide (x = s)); subst.
      * rewrite (insert_insert Γ) in H; rewrite decide_True; eauto.
      * rewrite decide_False; try naive_solver.
        econstructor. apply IHe. rewrite (insert_commute Γ); eauto.
  - intros (C & H1%IHe1 & H2%IHe2)%app_inversion; eauto.
  - destruct op; intros [-> H%IHe]%un_op_inversion; eauto.
  - destruct op; intros (-> & H1%IHe1 & H2%IHe2)%bin_op_inversion; eauto.
  - intros (H1%IHe1 & H2%IHe2 & H3%IHe3)%if_inversion; eauto.
  - intros (C & D & -> & H1%IHe1 & H2%IHe2)%pair_inversion; eauto.
  - intros (C & H%IHe)%fst_inversion; eauto.
  - intros (C & H%IHe)%snd_inversion; eauto.
  - intros (C & D & -> & H%IHe)%injL_inversion; eauto.
  - intros (C & D & -> & H%IHe)%injR_inversion; eauto.
  - intros (C & D & H1%IHe1 & H2%IHe2 & H3%IHe3)%case_inversion; eauto.
Qed.

Local Ltac simplify_literals :=
  repeat match goal with
  | H : (_ ⊢ of_val _ : Int) |- _ => apply canonical_values_int in H as [? ->]; clear H
  | H : (_ ⊢ of_val _ : Bool) |- _ => apply canonical_values_bool in H as [? ->]; clear H
  | H : (_ ⊢ of_val _ : String) |- _ => apply canonical_values_string in H as [? ->]; clear H
  end; eauto; try naive_solver.

Definition ectx_typing (K: ectx) (A B: ty) :=
  ∀ e, ∅ ⊢ e : A → ∅ ⊢ (fill K e) : B.

Lemma fill_typing_decompose K e A:
  ∅ ⊢ fill K e : A →
  ∃ B, ∅ ⊢ e : B ∧ ectx_typing K B A.
Proof.
  unfold ectx_typing; induction K in e,A |-*; simpl; eauto.
  all: inversion 1; subst; edestruct IHK as [? [Hit Hty]]; eauto.
Qed.

Lemma fill_typing_compose K e A B:
  ∅ ⊢ e : B →
  ectx_typing K B A →
  ∅ ⊢ fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.

Lemma typed_preservation_base_step e e' A:
  ∅ ⊢ e : A →
  base_step e e' →
  ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep.
  destruct Hstep as [  ]; subst; try solve_by_invert.
  4-7: inversion Hty; subst. (* SLOW *)
  4-5: by inversion H3.
  4-5: inversion H4; eauto.
  {
    eapply app_inversion in Hty as (B & H1 & H2).
    destruct x as [|x].
    { eapply lam_anon_inversion in H1 as (C & D & [= -> ->] & Hty). done. }
    eapply lam_inversion in H1 as (C & D & Heq & Hty).
    injection Heq as -> ->.
    eapply typed_substitutivity; eauto.
  } {
    destruct l, l', op; simpl in *; simplify_option_eq; inversion Hty; subst;
    inversion H4; destruct A0; simplify_option_eq; eauto.
  } {
    destruct l1, l2, l', op; simpl in *;
    simplify_option_eq; inversion Hty; subst;
    inversion H6; destruct A0, B; simplify_option_eq; eauto.
  }
Qed.

(** Preservation Theorem *)
Theorem typed_preservation e e' A:
  ∅ ⊢ e : A →
  contextual_step e e' →
  ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep. inversion Hstep; subst.
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply typed_preservation_base_step.
Qed.

(** Progress Theorem *)
Theorem typed_progress e A:
  ∅ ⊢ e : A → is_val e ∨ reducible e.
Proof.
  remember ∅ as Γ; induction 1; intuition; try (by left); unfold reducible;
  repeat match goal with
  | H : reducible _ |- _ => destruct H
  end; simplify_val; repeat match goal with
  | H : ∃ _, _ |- _ => destruct H; intuition
  end; simpl in *; subst; try naive_solver;
  try solve [ simplify_literals; destruct x2; naive_solver
            | apply canonical_values_sum in H as (? & [-> | ->] & H); simplify_val; naive_solver ].
  - apply canonical_values_arr in H as (x' & e & ->); try (right; eexists); eauto.
  - destruct op, A, B; simpl in *; try naive_solver; simplify_val; simplify_literals.
  - destruct op, A, B, C; simpl in *; try naive_solver; simplify_val; simplify_literals.
  - apply canonical_values_prod in H as (? & ? & -> & H1 & H2); simplify_val; naive_solver.
  - apply canonical_values_prod in H as (? & ? & -> & H1 & H2); simplify_val; naive_solver.
Qed.

(** Soundness Theorem *)
Corollary typed_soundness e1 e2 A:
  ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed.
