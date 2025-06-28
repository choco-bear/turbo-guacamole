From Formalizing.StlcMore Require Import small_step.
From Formalizing.StlcMore Require Export notation.
From Intro2TT Require Import Tactics.

(** ** Big-step operational semantics for the STLC language. *)
(** This file defines the big-step operational semantics for the STLC language. It
  * includes the rules for evaluating expressions, including base types, lambda
  * abstractions, applications, and operations on products and sums. *)

Implicit Types
  (n : Z)
  (b : bool)
  (s : string)
  (l : base_lit)
  (x : binder)
  (v : val)
  (e : expr).

Inductive big_step : expr → val → Prop :=
  | BSLit l : big_step #l #l
  | BSLam x e :
      big_step (λ: x, e) (λ: x, e)
  | BSApp e1 e2 x e v2 v :
      big_step e1 (λ: x, e) →
      big_step e2 v2 → 
      big_step (subst' x v2 e) v →
      big_step (App e1 e2) v
  | BSUnOp op e l l' :
      big_step e #l →
      un_eval op l = Some l' →
      big_step (UnOp op e) #l'
  | BSBinOp op e1 e2 l1 l2 l' :
      big_step e1 #l1 →
      big_step e2 #l2 →
      bin_eval op l1 l2 = Some l' →
      big_step (BinOp op e1 e2) #l'
  | BSIfTrue e0 e1 e2 v :
      big_step e0 #true →
      big_step e1 v →
      big_step (If e0 e1 e2) v
  | BSIfFalse e0 e1 e2 v :
      big_step e0 #false →
      big_step e2 v →
      big_step (If e0 e1 e2) v
  | BSPair e1 e2 v1 v2 :
      big_step e1 v1 →
      big_step e2 v2 →
      big_step (e1, e2) (v1, v2)
  | BSFst e v1 v2 :
      big_step e (v1, v2) →
      big_step (Fst e) v1
  | BSSnd e v1 v2 :
      big_step e (v1, v2) →
      big_step (Snd e) v2
  | BSInjL e v :
      big_step e v →
      big_step (InjL e) (InjLV v)
  | BSInjR e v :
      big_step e v →
      big_step (InjR e) (InjRV v)
  | BSCaseL e0 e1 e2 v x e v' :
      big_step e0 (InjLV v) →
      big_step e1 (λ: x, e) →
      big_step (subst' x v e) v' →
      big_step (Case e0 e1 e2) v'
  | BSCaseR e0 e1 e2 v x e v' :
      big_step e0 (InjRV v) →
      big_step e2 (λ: x, e) →
      big_step (subst' x v e) v' →
      big_step (Case e0 e1 e2) v'
.
#[export] Hint Constructors big_step : core.

(** ** Notations for the big-step semantics *)
Notation "e ↓ v" := (big_step e%E v%E) (at level 90).


(** ** Properties of the big-step semantics *)
Lemma big_step_of_val e v :
  e = of_val v →
  e ↓ v.
Proof. intro Heq; induction v in e, Heq |-*; subst; simpl; eauto. Qed.

Lemma big_step_val v v' :
  big_step v v' →
  v = v'.
Proof.
  remember (of_val v) as e; intro; revert Heqe.
  induction H in v |-*; intro Heq; subst; destruct v.
  all: inversion Heq; subst; naive_solver.
Qed.

Lemma small_step_big_step e e' v :
  small_step e e' →
  big_step e' v →
  big_step e v.
Proof.
  intro. revert v.
  induction H in |-*; intros; try solve_by_invert;
    simplify_val; eauto using big_step_of_val.
Qed.