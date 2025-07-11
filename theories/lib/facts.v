From stdpp Require Export relations.
From stdpp Require Import binders gmap.

Global Instance Proper_Is_true : Proper (eq ==> iff) Is_true.
Proof. by intros [] _ <-. Defined.

Lemma list_subseteq_cons {X} (A B : list X) x : A ⊆ B → x :: A ⊆ x :: B.
Proof. intros Hincl. intros y. rewrite !elem_of_cons. naive_solver. Qed.
Lemma list_subseteq_cons_binder A B x : A ⊆ B → x :b: A ⊆ x :b: B.
Proof. destruct x; [done|]. apply list_subseteq_cons. Qed.
Lemma list_subseteq_cons_l {X} (A B : list X) x : A ⊆ x :: B → x :: A ⊆ x :: B.
Proof. 
  intros Hincl. intros y. rewrite elem_of_cons. intros [-> | ?]. 
  - left.
  - apply Hincl. naive_solver. 
Qed.

Lemma list_subseteq_cons_elem {X} (A B : list X) x :
  x ∈ B → A ⊆ B → (x :: A) ⊆ B.
Proof.
  intros Hel Hincl.
  intros a [-> | ?]%elem_of_cons; [done|].
  by apply Hincl.
Qed.

Lemma elements_subseteq `{EqDecision A} `{Countable A} (X Y : gset A):
  X ⊆ Y → elements X ⊆ elements Y.
Proof.
  rewrite elem_of_subseteq.
  intros Ha a. rewrite !elem_of_elements.
  apply Ha.
Qed.
Lemma list_subseteq_cons_r {X} (A B : list X) x :
  A ⊆ B → A ⊆ (x :: B).
Proof.
  intros Hincl. trans B; [done|].
  intros b Hel. apply elem_of_cons; by right.
Qed.
