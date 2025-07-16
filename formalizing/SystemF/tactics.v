From Intro2TT Require Import Tactics.
From Formalizing.SystemF Require Import lang.

(* Try to solve [is_closed] goals using a number of heuristics (that shouldn't make the goal unprovable) *)
Ltac simplify_closed :=
  simpl; intros;
  repeat match goal with
  | H : False |- _ => exfalso; assumption
  | H : Is_true (false) |- _ => simpl in H; exfalso; assumption
  | H : _ ∧ _ |- _ => destruct H
  | H : Is_true (is_closed (?x :b: _) _) |- _ => destruct x as [|x]; simpl in H; simpl
  | H : Is_true (_ && _) |- _ => simpl in H; apply andb_True in H
  | H : Is_true (bool_decide _) |- _ => apply bool_decide_unpack in H
  | |- Is_true (is_closed [] _) => first [assumption | done]
  | |- Is_true (is_closed _ (lang.subst _ _ _)) => rewrite subst_is_closed_nil; last solve[simplify_closed]
  | |- Is_true (is_closed ?X ?v) => assert_fails (is_evar X); eapply is_closed_weaken
  | |- Is_true (is_closed _ _) => eassumption
  | |- Is_true (_ && true) => rewrite andb_true_r
  | |- Is_true (true && _) => rewrite andb_true_l
  | |- Is_true (?a && ?a) => rewrite andb_diag
  | |- Is_true (_ && _)  => simpl; rewrite !andb_True; split_and!
  | |- _ ⊆ ?A => match type of A with | list _ => simplify_list_subseteq end
  | |- _ ∈ ?A => match type of A with | list _ => simplify_list_elem end
  | |- _ ∉ ?A => match type of A with | list _ => simplify_list_elem end
  | |- _ ≠ _ => congruence
  | |- Is_true (bool_decide (_ ∈ _)) => apply bool_decide_pack
  end; try fast_done.


Ltac simplify_sets :=
  simpl; intros;
  repeat match goal with
  | H : False |- _ => exfalso; assumption
  | H : _ ∧ _ |- _ => destruct H
  | H : context[_ ∈ _ ∖ _] |- _ => rewrite elem_of_difference in H
  | H : context[_ ∈ _ ∪ _] |- _ => rewrite elem_of_union in H
  | H : context[_ ∈ _ ∩ _] |- _ => rewrite elem_of_intersection in H
  | H : ?P ∨ _, H' : ¬ ?P |- _ => destruct H as [H|H]
  | H : _ ∨ ?P, H' : ¬ ?P |- _ => destruct H as [H|H]
  | H : ?P, H' : ¬ ?P |- _ => exfalso; apply H', H
  | H : context[dom (<[_:=_]> ?Γ)] |- _ => rewrite (dom_insert Γ) in H
  | H : context[dom (_ <$> _)] |- _ => rewrite dom_fmap in H
  | H : _ ∈ dom _ |- _ => apply elem_of_dom in H
  | H : _ ∈ {[_]} |- _ => apply elem_of_singleton_1 in H; subst
  | H : _ ∉ {[_]} |- _ => apply not_elem_of_singleton in H
  | |- _ ⊆ _ => ii
  | |- _ ∈ dom _ => apply elem_of_dom
  end; try fast_done.