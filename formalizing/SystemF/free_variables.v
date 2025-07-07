Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.SystemF Require Import lang notation tactics.
From Intro2TT Require Import Tactics lib.maps.

Global Instance singleton_binder_gset_string : Singleton binder (gset string).
  intros [|x]; [exact (∅ : gset string) | exact ({[x]} : gset string)]. Defined.
Lemma singleton_binder_bnamed_rewrite x :
  {[BNamed x]} = ({[x]} : gset string).
Proof. reflexivity. Qed.
Lemma singleton_binder_anon_rewrite :
  {[BAnon]} = (∅ : gset string).
Proof. reflexivity. Qed.

(** ** Free Variables *)
(** This file defines the notion of free variables in the System F. *)

Fixpoint free_variables (e : expr) : gset string :=
  match e with
  | Lit _ => ∅
  | Var x => {[x]}
  | Lam x e => free_variables e ∖ {[x]}
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 => free_variables e1 ∪ free_variables e2
  | UnOp _ e | TApp e | TLam e | Pack e | Fst e | Snd e | InjL e | InjR e => free_variables e
  | Unpack x e1 e2 => free_variables e1 ∪ free_variables e2 ∖ {[x]}
  | If e1 e2 e3 | Case e1 e2 e3 => free_variables e1 ∪ free_variables e2 ∪ free_variables e3
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
  all: destruct (decide (x ∈ X)).
  - apply (is_closed_weaken _ (elements X)) in H; [|set_solver].
    intros y Hy. apply IHe; set_solver.
  - pose proof (fin_sets.elements_union_singleton _ _ n).
    rewrite <-H0 in H. apply IHe in H. intros y Hy. rewrite elem_of_difference in Hy.
    destruct Hy as [Hy Hy']. apply H, elem_of_union in Hy. intuition.
  - apply (is_closed_weaken _ (elements X)) in H0; [|set_solver].
    intros y Hy. apply IHe1 in H. apply IHe2 in H0. set_solver.
  - pose proof (fin_sets.elements_union_singleton _ _ n).
    rewrite <-H1 in H0. apply IHe1 in H. apply IHe2 in H0. intros y Hy.
    change {[BNamed _]} with ({[x]} : gset _) in Hy. set_solver.
Qed.

Lemma is_closed_free_variables' X e :
  is_closed X e → elements (FV e) ⊆ X.
Proof.
  revert X; induction e; intros X H; simpl in *; simplify_closed; try set_solver.
  - rewrite fin_sets.elements_singleton. set_solver.
  - change {[_]} with ({[x]} : gset _).
    intros y [Hy Hne%not_elem_of_singleton]%elem_of_elements%elem_of_difference.
    apply IHe in H. assert (y ∈ x :: X → y ∈ X) by by inversion 1. set_solver.
  - change {[_]} with ({[x]} : gset _).
    apply IHe1 in H. apply IHe2 in H0.
    intros y [Hy|Hy]%elem_of_elements%elem_of_union; first set_solver.
    revert Hy; intros [Hy Hne%not_elem_of_singleton]%elem_of_difference.
    assert (y ∈ x :: X → y ∈ X) by by inversion 1. set_solver.
Qed.

Lemma free_variables_is_closed X e :
  FV e ⊆ X → is_closed (elements X) e.
Proof.
  revert X; induction e; intros X H; simpl in *; simplify_closed; try set_solver;
  destruct x as [|x]; [apply IHe; set_solver| |apply IHe2; set_solver|];
  change {[_]} with ({[x]} : gset string) in H; destruct (decide (x ∈ X)).
  - apply (is_closed_weaken (elements X)); first apply IHe; set_solver.
  - simpl; rewrite <-fin_sets.elements_union_singleton; eauto.
    apply IHe. intros y Hy. apply elem_of_union.
    destruct (decide (x = y)); [subst; left|right; apply H]; set_solver.
  - apply (is_closed_weaken (elements X)); first apply IHe2; set_solver.
  - simpl; rewrite <-fin_sets.elements_union_singleton; eauto.
    apply IHe2. intros y Hy. apply elem_of_union.
    destruct (decide (x = y)); [subst; left|right; apply H]; set_solver.
Qed.

(** Free variables and substitution *)
Lemma free_variables_no_subst x es e :
  x ∉ FV e → FV (subst x es e) = FV e.
Proof.
  revert x es; induction e as [|y|y e| | | | | | | |y e1 e2| | | | | |];
    simpl; intros x es Hx; des_ifs;
  repeat match goal with
  | H : BNamed ?x = BNamed ?y |- _ => subst_inject H
  | H : BNamed ?x ≠ BNamed ?y |- _ =>
      destruct (decide (x = y)); [subst; exfalso; auto|clear H]
  | x : binder |- _ => destruct x as [|x]
  | H : context[{[BNamed ?s]}] |- _ =>
      rewrite !singleton_binder_bnamed_rewrite in H
  | |- context[{[BNamed ?s]}] =>
      rewrite !singleton_binder_bnamed_rewrite
  | H : context[{[<>%binder]}] |- _ =>
      rewrite singleton_binder_anon_rewrite in H
  | |- context[{[<>%binder]}] =>
      rewrite singleton_binder_anon_rewrite
  | H : context [_ ∖ ∅] |- _ =>
      rewrite sets.difference_empty_r in H
  | |- context [_ ∖ ∅] =>
      rewrite sets.difference_empty_r
  | H : _ ∉ _ ∪ _ |- _ =>
      rewrite sets.not_elem_of_union in H; destruct H
  | H : _ ∉ _ ∖ _ |- _ =>
      rewrite not_elem_of_difference in H; destruct H
  | H : ?x ∉ FV ?e, IH : context[FV (subst _ _ ?e) = FV ?e] |- _ =>
      rewrite IH; eauto
  | H : ?x ≠ ?y, H' : ?x ∈ {[?y]} |- _ =>
      set_solver
  | H : ?x ∉ {[?y]} |- _ =>
      rewrite sets.not_elem_of_singleton in H
  end; intuition.
Qed.

Lemma free_variables_do_subst x es e :
  FV es = ∅ → x ∈ FV e → FV (subst x es e) = FV e ∖ {[x]}.
Proof.
  revert x es; induction e as [|y|y e| | | | | | | |y| | | | | |];
    simpl; intros x es Hes Hy; des_ifs;
  repeat match goal with
  | x : binder |- _ => destruct x as [|x]
  | H : context [{[BNamed ?s]}] |- _ =>
      rewrite !singleton_binder_bnamed_rewrite in H
  | |- context [{[BNamed ?s]}] =>
      rewrite !singleton_binder_bnamed_rewrite
  end; try by eauto.
  1-5,9: set_solver.
  all: destruct (decide (x ∈ FV e1)); destruct (decide (x ∈ FV e2));
    try destruct (decide (x ∈ FV e3)).
  all: repeat match goal with
  | H : ?x ∈ ?X ∖ _, H' : ?x ∉ ?X |- _ =>
      rewrite elem_of_difference in H; intuition
  | H : ?x ∉ ?X |- context[?X ∖ {[?x]}] =>
      rewrite <-(sets.difference_not_elem x X); eauto
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
  | |- context[_ ∖ {[<>%binder]}] =>
      rewrite !singleton_binder_anon_rewrite
  | |- context[_ ∖ ∅] =>
      rewrite !sets.difference_empty_r
  | |- context[_ ∖ _ ∖ _] =>
      rewrite (sets.difference_commute _ {[y]} {[x]})
  end; reflexivity.
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