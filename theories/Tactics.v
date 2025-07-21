From Coq Require Import Bool Bool.Bool Strings.String.
From Coq.Arith Require Import Arith Compare_dec.
From stdpp Require Export relations tactics.
From stdpp Require Import binders strings gmap.
From Intro2TT.lib Require Export facts.
From Intro2TT.lib Require Import maps.

(** Solve by inverts *)
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with
      | S (S (?n')) => subst; solve_by_inverts (S n') 
      | 1 => subst; simpl in *; eauto
      end ]
  end end.

Ltac solve_by_invert := solve_by_inverts 1.

(** Solve by injects *)
Inductive Tmarker := Omarker.
Ltac mk_marker :=
  let marker := fresh "marker" in
  pose proof Omarker as marker; revert marker.
Ltac intros_until_marker :=
  intro; match goal with
         | H : Tmarker |- _ => clear H 
         | H : _ |- _ => intros_until_marker 
         end.
Ltac subst_inject H :=
  mk_marker; injection H; intros_until_marker; subst; clear H.
Ltac solve_by_injects n :=
  match goal with | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        subst_inject H;
        match n with
        | S (S (?n')) => subst; solve_by_injects (S n')
        | _ => subst; by try naive_solver
      end ] end end.
Ltac solve_by_inject := solve_by_injects 1.

(** bdestruct *)
Section BDestruct.
  Definition geb (n m : nat) := m <=? n.
  Hint Unfold geb : core.
  Infix ">=?" := geb (at level 70) : nat_scope.

  Definition gtb (n m : nat) := m <? n.
  Hint Unfold gtb : core.
  Infix ">?" := gtb (at level 70) : nat_scope.

  Lemma nat_eqb_reflect : forall x y, reflect (x = y) (x =? y).
  Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.eqb_eq.
  Qed.

  Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
  Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.ltb_lt.
  Qed.

  Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
  Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.leb_le.
  Qed.

  Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
  Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.ltb_lt.
  Qed.

  Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
  Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.leb_le.
  Qed.

  Lemma string_eqb_reflect : forall x y : string, reflect (x = y) (x =? y)%string.
  Proof.
    intros x y. apply iff_reflect. symmetry.
    apply String.eqb_eq.
  Qed.
End BDestruct.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect nat_eqb_reflect string_eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
      [ | try first [apply not_lt in H | apply not_le in H]]].



(** list manipulations *)
Ltac simplify_list_elem :=
  simpl;
  repeat match goal with
         | |- ?x ∈ ?y :: ?l => apply elem_of_cons; first [left; reflexivity | right]
         | |- _ ∉ [] => apply not_elem_of_nil
         | |- _ ∉ _ :: _ => apply not_elem_of_cons; split
  end; try fast_done.
Ltac simplify_list_subseteq :=
  simpl;
  repeat match goal with
         | |- ?x :: _ ⊆ ?x :: _ => apply list_subseteq_cons_l
         | |- ?x :: _ ⊆ _ => apply list_subseteq_cons_elem; first solve [simplify_list_elem]
         | |- elements _ ⊆ elements _ => apply elements_subseteq; set_solver
         | |- [] ⊆ _ => apply list_subseteq_nil
         | |- ?x :b: _ ⊆ ?x :b: _ => apply list_subseteq_cons_binder
         end;
  try fast_done.


(** destruct if *)
(* This tactic destructs if expressions in the goal and hypotheses.
   It simplifies the goal by removing branches that are impossible. *)
Ltac des_ifs :=
  repeat match goal with
  | |- context [if ?e then _ else _] =>
    destruct e; simpl; try congruence
  | H : context [if ?e then _ else _] |- _ =>
    destruct e; simpl in H; try congruence
  end.

(** Some tactics for convenience *)
Ltac i := intros.
Ltac ii := repeat intro.