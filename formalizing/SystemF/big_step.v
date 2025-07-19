Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.SystemF Require Import lang notation free_variables.
From Intro2TT Require Import Tactics.

(** ** Big Step of System F *)
(** This file defines the big step semantics of System F *)

Implicit Types
  (x : binder)
  (l : base_lit)
  (e : expr)
  (v : val).

Inductive big_step : expr -> val -> Prop :=
| BSLit l :
    big_step (Lit l) (LitV l)
| BSLam x e :
    big_step (Lam x e) (LamV x e)
| BSApp e1 e2 x e v2 v :
    big_step e1 (LamV x e) →
    big_step e2 v2 →
    big_step (subst' x (of_val v2) e) v →
    big_step (App e1 e2) v
| BSUnOp op e l l' :
    big_step e (LitV l) →
    un_op_eval op l = Some l' →
    big_step (UnOp op e) (LitV l')
| BSBinOp op e1 e2 l1 l2 l' :
    big_step e1 (LitV l1) →
    big_step e2 (LitV l2) →
    bin_op_eval op l1 l2 = Some l' →
    big_step (BinOp op e1 e2) (LitV l')
| BSIfTrue e e1 e2 v1 :
    big_step e (LitV (LitBool true)) →
    big_step e1 v1 →
    big_step (If e e1 e2) v1
| BSIfFalse e e1 e2 v2 :
    big_step e (LitV (LitBool false)) →
    big_step e2 v2 →
    big_step (If e e1 e2) v2
| BSTApp e e' v :
    big_step e (TLamV e') →
    big_step e' v →
    big_step (TApp e) v
| BSTLam e :
    big_step (TLam e) (TLamV e)
| BSPack e v :
    big_step e v →
    big_step (Pack e) (PackV v)
| BSUnpack x e1 e2 v v' :
    big_step e1 (PackV v) →
    big_step (subst' x v e2) v' →
    big_step (Unpack x e1 e2) v'
| BSPair e1 e2 v1 v2 :
    big_step e1 v1 →
    big_step e2 v2 →
    big_step (Pair e1 e2) (PairV v1 v2)
| BSFst e v1 v2 :
    big_step e (PairV v1 v2) →
    big_step (Fst e) v1
| BSSnd e v1 v2 :
    big_step e (PairV v1 v2) →
    big_step (Snd e) v2
| BSInjL e v :
    big_step e v →
    big_step (InjL e) (InjLV v)
| BSInjR e v :
    big_step e v →
    big_step (InjR e) (InjRV v)
| BSCaseL e e1 e2 x e' v v' : 
    big_step e (InjLV v) →
    big_step e1 (LamV x e') →
    big_step (subst' x v e') v' →
    big_step (Case e e1 e2) v'
| BSCaseR e e1 e2 x e' v v' :
    big_step e (InjRV v) →
    big_step e2 (LamV x e') →
    big_step (subst' x v e') v' →
    big_step (Case e e1 e2) v'
.
Notation "e ↓ v" := (big_step e v) (at level 90, no associativity).
#[export] Hint Constructors big_step : core.

(** ** Properties of Big Step Semantics *)
Lemma big_step_deterministic e v1 v2 :
  e ↓ v1 ->
  e ↓ v2 ->
  v1 = v2.
Proof.
  induction 1 in v2 |-*; inv 1;
  repeat match goal with
  | IH : ∀ v, big_step ?e v → _ = v, H : big_step ?e ?v |- _ =>
      apply IH in H
  | H : ?p = ?p |- _ => clear H
  | H : LitV _ = LitV _ |- _ => inv H
  | H : LamV _ _ = LamV _ _ |- _ => inv H
  | H : TLamV _ = TLamV _ |- _ => inv H
  | H : PackV _ = PackV _ |- _ => inv H
  | H : PairV _ _ = PairV _ _ |- _ => inv H
  | H : InjLV _ = InjLV _ |- _ => inv H
  | H : InjRV _ = InjRV _ |- _ => inv H
  end; by subst.
Qed.

Lemma big_step_contextual e v :
    e ↓ v → e ↝* v.
Proof.
  induction 1; simpl in *.
  Local Tactic Notation "exploit" uconstr(ctx) :=
    etrans; [eapply (fill_rtc_contextual_step ctx); eassumption|].
  Local Tactic Notation "step" :=
    econstructor; [apply base_contextual_step|].
  all: by repeat match goal with
  | |- context[fill _ _] => simpl
  | |- base_step _ _ => eauto
  | |- rtc contextual_step (App (Lam _ _) _) _ => step
  | |- rtc contextual_step (App _ (of_val _)) _ => 
      exploit (AppLCtx HoleCtx _)
  | |- rtc contextual_step (App _ _) _ =>
      exploit (AppRCtx _ HoleCtx)
  | |- rtc contextual_step (UnOp _ (Lit _)) _ =>
      econstructor; [apply base_contextual_step|]
  | |- rtc contextual_step (UnOp _ _) _ =>
      exploit (UnOpCtx _ HoleCtx)
  | |- rtc contextual_step (BinOp _ (Lit _) (Lit _)) _ => step
  | |- rtc contextual_step (BinOp _ _ (Lit _)) _ =>
      exploit (BinOpLCtx _ HoleCtx (LitV _))
  | |- rtc contextual_step (BinOp _ _ _) _ =>
      exploit (BinOpRCtx _ _ HoleCtx)
  | |- rtc contextual_step (If (Lit (LitBool true)) _ _) _ => step
  | |- rtc contextual_step (If (Lit (LitBool false)) _ _) _ => step
  | |- rtc contextual_step (If _ _ _) _ =>
      exploit (IfCtx HoleCtx _ _)
  | |- rtc contextual_step (TApp (TLam _)) _ =>
      econstructor; [apply base_contextual_step|]
  | |- rtc contextual_step (TApp _) _ =>
      exploit (TAppCtx HoleCtx)
  | |- rtc contextual_step (Pack _) _ =>
      exploit (PackCtx HoleCtx)
  | |- rtc contextual_step (Unpack _ (Pack _) _) _ => step
  | |- rtc contextual_step (Unpack _ _ _) _ =>
      exploit (UnpackCtx _ HoleCtx _)
  | |- rtc contextual_step (Pair _ (of_val _)) _ =>
      exploit (PairLCtx HoleCtx _)
  | |- rtc contextual_step (Pair _ _) _ =>
      exploit (PairRCtx _ HoleCtx)
  | |- rtc contextual_step (Fst (Pair _ _)) _ => step
  | |- rtc contextual_step (Fst _) _ =>
      exploit (FstCtx HoleCtx)
  | |- rtc contextual_step (Snd (Pair _ _)) _ => step
  | |- rtc contextual_step (Snd _) _ =>
      exploit (SndCtx HoleCtx)
  | |- rtc contextual_step (InjL _) _ =>
      exploit (InjLCtx HoleCtx)
  | |- rtc contextual_step (InjR _) _ =>
      exploit (InjRCtx HoleCtx)
  | |- rtc contextual_step (Case (InjL _) _ _) _ => step
  | |- rtc contextual_step (Case (InjR _) _ _) _ => step
  | |- rtc contextual_step (Case _ _ _) _ =>
      exploit (CaseCtx HoleCtx _ _)
  end.
Qed.

Lemma big_step_of_val e v :
  e = v →
  e ↓ v.
Proof. intros ->. induction v; simpl; eauto. Qed.

Lemma big_step_val v v' :
  v ↓ v' → v = v'.
Proof.
  enough (∀ e, big_step e v' → e = v → v = v') by naive_solver. intros e bs.
  induction bs in v |-*; intros Heq; destruct v; inversion Heq; subst; naive_solver.
Qed.

Lemma big_step_perserves_closed e v :
  is_closed [] e →
  e ↓ v →
  is_closed [] v.
Proof.
  intro Hcl. induction 1; try done; simpl in *.
  all:  repeat match goal with
        | H : Is_true (_ && _) |- _ => apply andb_True in H; destruct H
        end.
  all:  intuition; naive_solver (eauto using is_closed_subst').
Qed.
Corollary big_step_perserves_closed' e v :
  FV e = ∅ →
  e ↓ v →
  FV v = ∅.
Proof.
  rewrite !is_closed_nil_iff_FV_empty.
  apply big_step_perserves_closed.
Qed.