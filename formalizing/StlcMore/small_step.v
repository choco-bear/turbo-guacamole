From Formalizing.StlcMore Require Export lang.
From Intro2TT Require Import Tactics.

(** ** Small-step operational semantics for the STLC language. *)
(** This file defines the small-step operational semantics for the STLC language.
  * It includes the rules for evaluating expressions, including base types,
  * lambda abstractions, applications, and operations on products and sums. *)
Implicit Types
  (n : Z)
  (b : bool)
  (s : string)
  (l : base_lit)
  (x : binder)
  (e v : expr).
Local Coercion Z.of_nat : nat >-> Z.
Definition un_eval uop l : option base_lit :=
  match uop, l with
  | NegOp, LitBool b => Some $ LitBool (negb b)
  | MinusUnOp, LitInt n => Some $ LitInt (-n)
  | LenOp, LitString s => Some $ LitInt (String.length s)
  | _, _ => None
  end.

Definition bin_eval bop l1 l2 : option base_lit :=
  match bop, l1, l2 with
  | PlusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 + n2)
  | MinusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 - n2)
  | MultOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 * n2)
  | LtOp, LitInt n1, LitInt n2 => Some $ LitBool (n1 <? n2)%Z
  | LeOp, LitInt n1, LitInt n2 => Some $ LitBool (n1 <=? n2)%Z
  | EqOp, LitInt n1, LitInt n2 => Some $ LitBool (n1 =? n2)%Z
  | AndOp, LitBool b1, LitBool b2 => Some $ LitBool (b1 && b2)
  | OrOp, LitBool b1, LitBool b2 => Some $ LitBool (b1 || b2)
  | ConcatOp, LitString s1, LitString s2 => Some $ LitString (s1 ++ s2)
  | StrEqOp, LitString s1, LitString s2 => Some $ LitBool (s1 =? s2)%string
  | PrefixOp, LitString s1, LitString s2 =>
      Some $ LitBool (String.prefix s1 s2)
  | _, _, _ => None
  end.

Inductive small_step : expr → expr → Prop :=
  (* Base Lambda Calculus *)
  | SSAppR e1 e2 e2' :
      small_step e2 e2' →
      small_step (App e1 e2) (App e1 e2')
  | SSAppL e1 e1' v :
      is_val v →
      small_step e1 e1' →
      small_step (App e1 v) (App e1' v)
  | SSAppBeta x e v :
      is_val v →
      small_step (App (Lam x e) v) (subst' x v e)
  | SSUnOp op e e' :
      small_step e e' →
      small_step (UnOp op e) (UnOp op e')
  | SSUnOpEval op v l l' :
      v = Lit l →
      un_eval op l = Some l' →
      small_step (UnOp op v) (Lit l')
  | SSBinOpR op e1 e2 e2' :
      small_step e2 e2' →
      small_step (BinOp op e1 e2) (BinOp op e1 e2')
  | SSBinOpL op e1 e1' v :
      is_val v →
      small_step e1 e1' →
      small_step (BinOp op e1 v) (BinOp op e1' v)
  | SSBinOpEval op v1 v2 l1 l2 l' :
      v1 = Lit l1 →
      v2 = Lit l2 →
      bin_eval op l1 l2 = Some l' →
      small_step (BinOp op v1 v2) (Lit l')
  | SSIf e e' e1 e2 :
      small_step e e' →
      small_step (If e e1 e2) (If e' e1 e2)
  | SSIfTrue e1 e2 :
      small_step (If (Lit $ LitBool true) e1 e2) e1
  | SSIfFalse e1 e2 :
      small_step (If (Lit $ LitBool false) e1 e2) e2
  | SSPairR e1 e2 e2' :
      small_step e2 e2' →
      small_step (Pair e1 e2) (Pair e1 e2')
  | SSPairL e1 e1' v2 :
      is_val v2 →
      small_step e1 e1' →
      small_step (Pair e1 v2) (Pair e1' v2)
  | SSFst e e' :
      small_step e e' →
      small_step (Fst e) (Fst e')
  | SSFstRed v1 v2 :
      is_val v1 →
      is_val v2 →
      small_step (Fst (Pair v1 v2)) v1
  | SSSnd e e' :
      small_step e e' →
      small_step (Snd e) (Snd e')
  | SSSndRed v1 v2:
      is_val v1 →
      is_val v2 →
      small_step (Snd (Pair v1 v2)) v2
  | SSInjL e e' :
      small_step e e' →
      small_step (InjL e) (InjL e')
  | SSInjR e e' :
      small_step e e' →
      small_step (InjR e) (InjR e')
  | SSCase e e' e1 e2 :
      small_step e e' →
      small_step (Case e e1 e2) (Case e' e1 e2)
  | SSCaseL v e1 e2 :
      is_val v →
      small_step (Case (InjL v) e1 e2) (App e1 v)
  | SSCaseR v e1 e2 :
      is_val v →
      small_step (Case (InjR v) e1 e2) (App e2 v)
  .
#[export] Hint Constructors small_step : core.

(** ** Notations for the small-step semantics *)
Notation "e1 ≻ e2" := (small_step e1%E e2%E) (at level 90).
Notation "e1 ≻* e2" := (rtc small_step e1%E e2%E) (at level 90).

(** Boring Lemmas *)
Lemma value_nf_small_step v :
  is_val v → nf small_step v.
Proof.
  intros Hv [e H].
  induction v in Hv, e, H |-*; try inversion Hv; solve_by_invert.
Qed.

Lemma var_nf_small_step (x : string) :
  nf small_step (Var x).
Proof. intros [e H]. inversion H. Qed.