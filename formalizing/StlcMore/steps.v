From Formalizing.StlcMore Require Import small_step big_step.
From Formalizing.StlcMore Require Export ctx_step.
From Intro2TT Require Import Tactics.

Theorem contextual_step_iff_small_step e e' :
  e ↝ e' ↔ e ≻ e'.
Proof.
  split; induction 1 in |-*; subst; eauto; cycle 1.
  induction K in e, e', H |-*; simpl; eauto.
  inversion H; subst; simpl; eauto.
Qed.

Theorem rtc_ctx_step_iff_rtc_small_step e e' :
  e ↝* e' ↔ e ≻* e'.
Proof.
  by split; induction 1 in |-*; subst; try naive_solver;
  etrans; eauto; apply rtc_once, contextual_step_iff_small_step.
Qed.

Local Ltac step_with ECTX :=
  etrans; first eapply fill_rtc_contextual_step with (K := ECTX);
  eauto using rtc_once, base_step_contextual_step; subst; simpl.

Theorem big_step_iff_rtc_small_step e v :
  big_step e v ↔ rtc small_step e v.
Proof.
  split.
  - rewrite <-rtc_ctx_step_iff_rtc_small_step.
    remember (of_val v) as e'. induction 1 in e', Heqe' |-*;
    try solve [ naive_solver
              | step_with (UnOpCtx op HoleCtx);
                step_with HoleCtx; naive_solver
              | step_with (IfCtx HoleCtx e1 e2); 
                step_with HoleCtx; naive_solver 
              | step_with (FstCtx HoleCtx); eauto using rtc_once
              | step_with (SndCtx HoleCtx); eauto using rtc_once
              | step_with (InjLCtx HoleCtx); naive_solver
              | step_with (InjRCtx HoleCtx); naive_solver
              | step_with (CaseCtx HoleCtx e1 e2); step_with HoleCtx;
                step_with (AppLCtx HoleCtx v); step_with HoleCtx ].
    + step_with (AppRCtx e1 HoleCtx).
      step_with (AppLCtx HoleCtx v2).
      step_with HoleCtx; naive_solver.
    + step_with (BinOpRCtx op e1 HoleCtx).
      step_with (BinOpLCtx op HoleCtx #l2).
      step_with HoleCtx; naive_solver.
    + step_with (PairRCtx e1 HoleCtx).
      step_with (PairLCtx HoleCtx v2); naive_solver.
  - intro H. remember (of_val v) as e'.
    induction H; subst; simpl in *.
    + by apply big_step_of_val.
    + eapply small_step_big_step; eauto.
Qed.