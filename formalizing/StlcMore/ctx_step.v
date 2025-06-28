From Formalizing.StlcMore Require Import small_step.
From Formalizing.StlcMore Require Export notation.

Declare Scope ectx_scope.
Delimit Scope ectx_scope with ctx.

(** ** Contextual semantics for the STLC language. *)
(** This file defines the contextual semantics for the STLC language.
  * It includes the rules for evaluating expressions in a context,
  * including variable binding and substitution. *)

Inductive base_step : expr → expr → Prop :=
  | BetaS x e v :
      is_val v →
      base_step (App (Lam x e) v) (subst' x v e)
  | UnOpS op l l' :
      un_eval op l = Some l' →
      base_step (UnOp op $ Lit l) (Lit l')
  | BinOpS op l1 l2 l' :
      bin_eval op l1 l2 = Some l' →
      base_step (BinOp op (Lit l1) (Lit l2)) (Lit l')
  | IfTrueS e1 e2 :
      base_step (If (Lit $ LitBool true) e1 e2) e1
  | IfFalseS e1 e2 :
      base_step (If (Lit $ LitBool false) e1 e2) e2
  | FstS v1 v2 :
      is_val v1 →
      is_val v2 →
      base_step (Fst (Pair v1 v2)) v1
  | SndS v1 v2 :
      is_val v1 →
      is_val v2 →
      base_step (Snd (Pair v1 v2)) v2
  | CaseLS e1 e2 v :
      is_val v →
      base_step (Case (InjL v) e1 e2) (App e1 v)
  | CaseRS e1 e2 v :
      is_val v →
      base_step (Case (InjR v) e1 e2) (App e2 v)
  .
Notation "e '↝b' e'" := (base_step e e')
  (at level 70, no associativity) : expr_scope.
#[export] Hint Constructors base_step : core.

(** Evaluation Contexts *)
Inductive ectx :=
  | HoleCtx : ectx
  | AppLCtx (K : ectx) (v : val) : ectx
  | AppRCtx (e : expr) (K : ectx) : ectx
  | UnOpCtx (op : un_op) (K : ectx) : ectx
  | BinOpLCtx (op : bin_op) (K : ectx) (v : val) : ectx
  | BinOpRCtx (op : bin_op) (e : expr) (K : ectx) : ectx
  | IfCtx (K : ectx) (e1 e2 : expr) : ectx
  | PairLCtx (K : ectx) (v : val) : ectx
  | PairRCtx (e : expr) (K : ectx) : ectx
  | FstCtx (K : ectx) : ectx
  | SndCtx (K : ectx) : ectx
  | InjLCtx (K : ectx) : ectx
  | InjRCtx (K : ectx) : ectx
  | CaseCtx (K : ectx) (e1 : expr) (e2 : expr) : ectx
  .

Bind Scope ectx_scope with ectx.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v => App (fill K e) (of_val v)
  | AppRCtx e' K => App e' (fill K e)
  | UnOpCtx op K => UnOp op (fill K e)
  | BinOpLCtx op K v => BinOp op (fill K e) (of_val v)
  | BinOpRCtx op e' K => BinOp op e' (fill K e)
  | IfCtx K e1 e2 => If (fill K e) e1 e2
  | PairLCtx K v => Pair (fill K e) (of_val v)
  | PairRCtx e' K => Pair e' (fill K e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  | InjLCtx K => InjL (fill K e)
  | InjRCtx K => InjR (fill K e)
  | CaseCtx K e1 e2 => Case (fill K e) e1 e2
  end.

Fixpoint ectx_comp (K K' : ectx) : ectx :=
  match K with
  | HoleCtx => K'
  | AppLCtx K v => AppLCtx (ectx_comp K K') v
  | AppRCtx e K => AppRCtx e (ectx_comp K K')
  | UnOpCtx op K => UnOpCtx op (ectx_comp K K')
  | BinOpLCtx op K v => BinOpLCtx op (ectx_comp K K') v
  | BinOpRCtx op e K => BinOpRCtx op e (ectx_comp K K')
  | IfCtx K e1 e2 => IfCtx (ectx_comp K K') e1 e2
  | PairLCtx K v => PairLCtx (ectx_comp K K') v
  | PairRCtx e K => PairRCtx e (ectx_comp K K')
  | FstCtx K => FstCtx (ectx_comp K K')
  | SndCtx K => SndCtx (ectx_comp K K')
  | InjLCtx K => InjLCtx (ectx_comp K K')
  | InjRCtx K => InjRCtx (ectx_comp K K')
  | CaseCtx K e1 e2 => CaseCtx (ectx_comp K K') e1 e2
  end.

Inductive contextual_step : expr → expr → Prop :=
  | Ectx_step K e e' :
      base_step e e' →
      contextual_step (fill K e) (fill K e').
Notation "e '↝' e'" := (contextual_step e e')
  (at level 90, no associativity).
Notation "e '↝*' e'" := (rtc contextual_step e e')
  (at level 90, no associativity).
#[export] Hint Constructors contextual_step : core.

Definition reducible (e : expr) : Prop :=
  ∃ e', contextual_step e e'.

Definition empty_ctx : ectx := HoleCtx.


(** Basic Properties of Evaluation Contexts *)
Lemma fill_empty e :
  fill empty_ctx e = e.
Proof. done. Qed.

Lemma fill_comp K K' e :
  fill (ectx_comp K K') e = fill K (fill K' e).
Proof. induction K; simpl; congruence. Qed.


(** Basic Properties of Contextual Steps *)
Lemma base_step_contextual_step e e' :
  base_step e e' → contextual_step e e'.
Proof. by intro; eapply Ectx_step in H; rewrite !fill_empty in *. Qed.
#[export] Hint Resolve base_step_contextual_step : core.

Lemma fill_contextual_step K e e' :
  contextual_step e e' → contextual_step (fill K e) (fill K e').
Proof. by intro; inversion H; rewrite <- !fill_comp. Qed.

Lemma fill_rtc_contextual_step K e e' :
  rtc contextual_step e e' →
  rtc contextual_step (fill K e) (fill K e').
Proof.
  induction 1; first naive_solver.
  etrans; eauto using rtc_once, fill_contextual_step.
Qed.


(** We derive lemmas lifting contextual steps akin to the structural semantics. *)
Lemma contextual_step_app_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (App e1 e2) (App e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (AppLCtx HoleCtx v)).
Qed.

Lemma contextual_step_app_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (App e1 e2) (App e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (AppRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_un_op o e e':
  contextual_step e e' →
  contextual_step (UnOp o e) (UnOp o e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (UnOpCtx o HoleCtx)).
Qed.

Lemma contextual_step_bin_op_l o e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (BinOp o e1 e2) (BinOp o e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (BinOpLCtx o HoleCtx v)).
Qed.

Lemma contextual_step_bin_op_r o e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (BinOp o e1 e2) (BinOp o e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (BinOpRCtx o e1 HoleCtx)).
Qed.

Lemma contextual_step_if e e' e1 e2:
  contextual_step e e' →
  contextual_step (If e e1 e2) (If e' e1 e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (IfCtx HoleCtx e1 e2)).
Qed.

Lemma contextual_step_pair_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (Pair e1 e2) (Pair e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (PairLCtx HoleCtx v)).
Qed.

Lemma contextual_step_pair_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (Pair e1 e2) (Pair e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PairRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_fst e e':
  contextual_step e e' →
  contextual_step (Fst e) (Fst e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (FstCtx HoleCtx)).
Qed.

Lemma contextual_step_snd e e':
  contextual_step e e' →
  contextual_step (Snd e) (Snd e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (SndCtx HoleCtx)).
Qed.

Lemma contextual_step_injl e e':
  contextual_step e e' →
  contextual_step (InjL e) (InjL e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (InjLCtx HoleCtx)).
Qed.

Lemma contextual_step_injr e e':
  contextual_step e e' →
  contextual_step (InjR e) (InjR e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (InjRCtx HoleCtx)).
Qed.

Lemma contextual_step_case e e' e1 e2:
  contextual_step e e' →
  contextual_step (Case e e1 e2) (Case e' e1 e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (CaseCtx HoleCtx e1 e2)).
Qed.

#[export] Hint Resolve
  base_step_contextual_step
  contextual_step_app_l
  contextual_step_app_r
  contextual_step_un_op
  contextual_step_bin_op_l
  contextual_step_bin_op_r
  contextual_step_if
  contextual_step_pair_l
  contextual_step_pair_r
  contextual_step_fst
  contextual_step_snd
  contextual_step_injl
  contextual_step_injr
  contextual_step_case : core.
