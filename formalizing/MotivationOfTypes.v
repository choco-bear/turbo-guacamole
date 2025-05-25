Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From stdpp Require Import relations.
Require Import Intro2TT.Tactics.
Set Default Goal Selector "!".

(** ** Syntax *)

(** _Terms_ are defined inductively as follows: *)
Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

(** The below are just for the custom notations. *)
Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at  level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(** _Values_ are [true], [false], and numeric values... *)
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.



(** ** Operational Semantics *)

(** Reduction *)
Reserved Notation "t '↝' t'" (at level 40).
Inductive reduction : tm -> tm -> Prop :=
  | Red_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> ↝ t1
  | Red_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> ↝ t2
  | Red_If : forall c c' t2 t3,
      c ↝ c' ->
      <{ if c then t2 else t3 }> ↝ <{ if c' then t2 else t3 }>
  | Red_Succ : forall t1 t1',
      t1 ↝ t1' ->
      <{ succ t1 }> ↝ <{ succ t1' }>
  | Red_Pred0 :
      <{ pred 0 }> ↝ <{ 0 }>
  | Red_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> ↝ v
  | Red_Pred : forall t1 t1',
      t1 ↝ t1' ->
      <{ pred t1 }> ↝ <{ pred t1' }>
  | Red_Iszero0 :
      <{ iszero 0 }> ↝ <{ true }>
  | Red_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> ↝ <{ false }>
  | Red_Iszero : forall t1 t1',
      t1 ↝ t1' ->
      <{ iszero t1 }> ↝ <{ iszero t1' }>
where "t '↝' t'" := (reduction t t').

Hint Constructors reduction : core.

Notation reduction_normal_form := (nf reduction).

Definition stuck (t : tm) : Prop :=
  reduction_normal_form t /\ ~ value t.

Hint Unfold stuck : core.



(** ** Typing *)

(** _Type_ is either Bool or Nat. *)
Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(** We will use ∈: instead of ∈ because it is reserved by the stdpp package. *)
Reserved Notation "'⊢' t '∈:' T" (at level 40).
(** The typing relation is defined inductively as follows: *)
Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       ⊢ <{ true }> ∈: Bool
  | T_False :
       ⊢ <{ false }> ∈: Bool
  | T_If : forall t1 t2 t3 T,
       ⊢ t1 ∈: Bool ->
       ⊢ t2 ∈: T ->
       ⊢ t3 ∈: T ->
       ⊢ <{ if t1 then t2 else t3 }> ∈: T
  | T_0 :
       ⊢ <{ 0 }> ∈: Nat
  | T_Succ : forall t1,
       ⊢ t1 ∈: Nat ->
       ⊢ <{ succ t1 }> ∈: Nat
  | T_Pred : forall t1,
       ⊢ t1 ∈: Nat ->
       ⊢ <{ pred t1 }> ∈: Nat
  | T_Iszero : forall t1,
       ⊢ t1 ∈: Nat ->
       ⊢ <{ iszero t1 }> ∈: Bool
where "'⊢' t '∈:' T" := (has_type t T).
Hint Constructors has_type : core.



(** ** Canonical forms *)
Lemma bool_canonical : forall t,
  ⊢ t ∈: Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  ⊢ t ∈: Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.



(** ** Progress *)
Theorem progress : forall t T,
  ⊢ t ∈: T ->
  value t \/ exists t', t ↝ t'.
Proof.
  intros t T HT. induction HT; auto; first right.
  3,4: destruct IHHT; first apply (nat_canonical t1 HT) in H.
  all: try solve [destruct H; try right; eauto].
  - destruct IHHT1; first apply (bool_canonical t1 HT1) in H.
    all: destruct H; eauto.
  - destruct IHHT; first apply (nat_canonical t1 HT) in H.
    + left; right; auto.
    + destruct H as [t1' H1]; right; eauto.
Qed.



(** ** Preservation *)
Theorem preservation : forall t t' T,
  ⊢ t ∈: T ->
  t ↝ t' ->
  ⊢ t' ∈: T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT; intros t' HE; try solve_by_invert.
  all: inversion HE; subst; try done.
  - by inversion HT.
  - by apply T_Pred, IHHT.
Qed.



(** ** Soundness *)
Notation "t1 '↝*' t2" := (rtc reduction t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  ⊢ t ∈: T ->
  t ↝* t' ->
  reduction_normal_form t' ->
  value t'.
Proof.
  intros t t' T HT Hrtc Hnf. induction Hrtc.
  - apply progress in HT. by intuition.
  - apply IHHrtc; by try eapply preservation.
Qed.