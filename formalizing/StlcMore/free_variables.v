Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.StlcMore Require Import notation tactics.
From Intro2TT.lib Require Import maps.

(** ** Free Variables *)
(** This file defines the notion of free variables in the StlcMore. *)

Global Instance singleton_binder_gset_string : Singleton binder (gset string).
  intros [|x]; [exact ∅ | exact {[x]}]. Defined.
Fixpoint free_variables (e : expr) : gset string :=
  match e with
  | Lit _ => ∅
  | Var x => {[x]}
  | Lam x e => free_variables e ∖ {[x]}
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 => free_variables e1 ∪ free_variables e2
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e => free_variables e
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

(** free variables and closedness *)
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