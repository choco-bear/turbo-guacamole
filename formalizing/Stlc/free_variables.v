Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.Stlc Require Import notation tactics.
From Intro2TT Require Import Tactics lib.maps.

(** ** Free Variables *)
(** This file defines the notion of free variables in the Stlc. *)

Global Instance singleton_binder_gset_string : Singleton binder (gset string).
  intros [|x]; [exact ∅ | exact {[x]}]. Defined.
Fixpoint free_variables (e : expr) : gset string :=
  match e with
  | Var x => {[x]}
  | Lam x e => free_variables e ∖ {[x]}
  | App e1 e2 => free_variables e1 ∪ free_variables e2
  end.
Notation FV := free_variables.

(** Examples *)
Goal FV (λ: "x", "x" "y") = {["y"]}.
Proof. eauto. Qed.

Goal FV ("x" (λ: "x", "x" "y"))%E = {["x"; "y"]}.
Proof. eauto. Qed.

Goal FV (λ: "x", "x") = ∅.
Proof. eauto. Qed.

(** Free variables and closedness *)
Lemma is_closed_free_variables X e :
  is_closed (elements X) e → FV e ⊆ X.
Proof.
  revert X; induction e; intros X H; simpl in *; simplify_closed; try set_solver.
  destruct (decide (x ∈ X)).
  - apply (is_closed_weaken _ (elements X)) in H; [|set_solver].
    intros y Hy. apply IHe; set_solver.
  - pose proof (fin_sets.elements_union_singleton _ _ n).
    rewrite <-H0 in H. apply IHe in H. intros y Hy. rewrite elem_of_difference in Hy.
    destruct Hy as [Hy Hy']. apply H, elem_of_union in Hy. intuition.
Qed.

Lemma is_closed_free_variables' X e :
  is_closed X e → elements (FV e) ⊆ X.
Proof.
  revert X; induction e; intros X H; simpl in *; simplify_closed; try set_solver.
  - rewrite fin_sets.elements_singleton. set_solver.
  - change {[_]} with ({[x]} : gset _).
    intros y [Hy Hne%not_elem_of_singleton]%elem_of_elements%elem_of_difference.
    apply IHe in H. assert (y ∈ x :: X → y ∈ X) by by inversion 1.
    apply H0, H. set_solver.
Qed.

Lemma free_variables_is_closed X e :
  FV e ⊆ X → is_closed (elements X) e.
Proof.
  revert X; induction e; intros X H; simpl in *; simplify_closed; try set_solver.
  destruct x as [|x]; first (apply IHe; set_solver).
  change {[_]} with ({[x]} : gset string) in H.
  destruct (decide (x ∈ X)).
  - apply (is_closed_weaken (elements X)); first apply IHe; set_solver.
  - simpl; rewrite <-fin_sets.elements_union_singleton; eauto.
    apply IHe. intros y Hy. apply elem_of_union.
    destruct (decide (x = y)); [subst; left|right; apply H]; set_solver.
Qed.

(** Free variables and substitution *)
Lemma free_variables_no_subst x es e :
  x ∉ FV e → FV (subst x es e) = FV e.
Proof.
  revert x es; induction e as [y|y e|];
    simpl; intros x es Hx; des_ifs;
  repeat match goal with
  | x : binder |- _ => destruct x
  | H : context [{[BNamed ?s]}] |- _ =>
      change {[BNamed s]} with ({[s]} : gset string) in H
  | |- context [{[BNamed ?s]}] =>
      change {[BNamed s]} with ({[s]} : gset string)
  end; set_solver.
Qed.

Lemma free_variables_do_subst x es e :
  FV es = ∅ → x ∈ FV e → FV (subst x es e) = FV e ∖ {[x]}.
Proof.
  revert x es; induction e as [y|y e|];
    simpl; intros x es Hes Hy; des_ifs;
  repeat match goal with
  | x : binder |- _ => destruct x
  | H : context [{[BNamed ?s]}] |- _ =>
      change {[BNamed s]} with ({[s]} : gset string) in H
  | |- context [{[BNamed ?s]}] =>
      change {[BNamed s]} with ({[s]} : gset string)
  end.
  1-6: set_solver.
  destruct (decide (x ∈ FV e1)); destruct (decide (x ∈ FV e2)).
  all: repeat match goal with
  | H : ?x ∈ _ ∪ _ |- _ =>
      apply elem_of_union in H; destruct H as [H|H]
  | H : ?x ∈ ?X, H' : ?x ∉ ?X |- _ =>
      exfalso; apply H', H
  | H : ?x ∉ FV ?e |- _ =>
      rewrite (free_variables_no_subst x _ e); eauto
  | H : ?x ∈ FV ?e, IH : context[FV (subst _ _ ?e) = FV ?e ∖ {[_]}] |- context[FV (subst _ _ ?e)] =>
      rewrite IH; eauto
  | |- context[(_ ∪ _) ∖ _] =>
      rewrite <-sets.union_difference
  end.
  4: rewrite (sets.not_elem_of_difference x (FV e1)); eauto.
  3: rewrite (sets.not_elem_of_difference x (FV e2)); eauto.
  all: by rewrite ?difference_shadow.
Qed.

Lemma free_variables_subst' x es e :
  FV es = ∅ → {[x]} ⊆ FV e → FV (subst' x es e) = FV e ∖ {[x]}.
Proof.
  destruct x as [|x]; [simpl; set_solver|].
  change {[_]} with ({[x]} : gset string).
  intros Hes Hx%sets.singleton_subseteq_l.
  by apply free_variables_do_subst.
Qed.

Lemma subst_free_variables x es e :
  x ∉ FV e → subst x es e = e.
Proof.
  intro Hx.
  eapply (subst_is_closed (elements (FV e)));
    last by rewrite elem_of_elements.
  by apply free_variables_is_closed.
Qed.

Lemma subst_free_variables_empty x es e :
  FV e = ∅ → subst x es e = e.
Proof. intros Hes. apply subst_free_variables. set_solver. Qed.
Lemma subst'_free_variables_empty x es e :
  FV e = ∅ → subst' x es e = e.
Proof. destruct x as [|x]; [simpl; set_solver|apply subst_free_variables_empty]. Qed.

Lemma subst_subst_neq x y M N L : x ≠ y → x ∉ FV L →
  subst y L (subst x N M) = subst x (subst y L N) (subst y L M).
Proof. (* TODO *) Admitted.