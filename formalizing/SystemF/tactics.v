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