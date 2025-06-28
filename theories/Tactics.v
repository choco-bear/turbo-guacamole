From Coq Require Import Bool Bool.Bool Strings.String.
From Coq.Arith Require Import Arith Compare_dec.
From stdpp Require Export tactics.

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
Ltac intros_until_marker :=
  intro; match goal with
         | H : Tmarker |- _ => clear H 
         | H : _ |- _ => intros_until_marker 
         end.
Ltac subst_inject H :=
  pose proof Omarker as marker; revert marker;
  injection H; intros_until_marker; subst; clear H.
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