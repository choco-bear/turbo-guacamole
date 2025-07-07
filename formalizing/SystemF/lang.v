Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From stdpp Require Export binders strings.
From stdpp Require Import option.
From Intro2TT Require Export lib.maps.

(** ** Language of System F *)
(** This file defines the language of System F *)

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** ** Expressions and Values *)
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitString (s : string) | LitUnit.
Inductive un_op : Set :=
  | NegOp (* Boolean Negation *)
  | MinusUnOp (* Integer Negation *)
  | LenOp (* String Length *)
  .
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp (* Integer Arithmetics *)
  | LtOp | LeOp | GtOp | GeOp (* Integer Comparisons *)
  | AndOp | OrOp | SubOp (* Logical Operators *)
  | ConcatOp (* String Concatenation *)
  | PrefixOp | SubstrOp (* String Prefix/Substring Relations *)
  | EqOp | NeqOp (* Literal Comparisons *)
  .


Inductive expr :=
  | Lit (l : base_lit)
  (* Base Lambda Calculus *)
  | Var (x : string)
  | Lam (x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Operations of Base Types *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Polymorphisms *)
  | TApp (e : expr)
  | TLam (e : expr)
  | Pack (e : expr)
  | Unpack (x : binder) (e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 e1 e2 : expr).

Bind Scope expr_scope with expr.

Inductive val :=
  | LitV (l : base_lit)
  | LamV (x : binder) (e : expr)
  | TLamV (e : expr)
  | PackV (v : val)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope val_scope with val.

(* Conversion from values to expressions *)
Fixpoint of_val (v : val) : expr :=
  match v with
  | LitV l => Lit l
  | LamV x e => Lam x e
  | TLamV e => TLam e
  | PackV v => Pack (of_val v)
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  end.

(* Conversion from expressions to values *)
(* Returns None if the expression is not a value *)
Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lit l => Some $ LitV l
  | Lam x e' => Some $ LamV x e'
  | TLam e' => Some $ TLamV e'
  | Pack e' => PackV <$> to_val e'
  | Pair e1 e2 =>
      to_val e1 ≫= (λ v1, to_val e2 ≫= (λ v2, Some $ PairV v1 v2))
  | InjL e' => InjLV <$> to_val e'
  | InjR e' => InjRV <$> to_val e'
  | _ => None
  end.

(** ** Properties of Conversion Functions *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by induction v; simplify_option_eq. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. revert v; induction e; intros; simplify_option_eq; auto with f_equal. Qed.

#[export] Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? H; apply (inj Some); rewrite <-!to_of_val, H. Qed.


(* Coq prop representing the given expression being a value *)
Fixpoint is_val (e : expr) : Prop :=
  match e with 
  | Lit _ | Lam _ _ | TLam _ => True
  | Pack e' | InjL e' | InjR e' => is_val e'
  | Pair e1 e2 => is_val e1 ∧ is_val e2
  | _ => False
  end.

Lemma is_val_spec e :
  is_val e ↔ ∃ v, to_val e = Some v.
Proof.
  split; intro H.
  - induction e; cycle 11; simpl; try by eauto.
    2-4: apply IHe in H as [v ->]; eauto.
    destruct H as [H1 H2].
    apply IHe1 in H1 as [v1 ->]; apply IHe2 in H2 as [v2 ->]; eauto.
  - destruct H as [v Hv]. rewrite <-(of_to_val e v); eauto.
    induction v in e |-*; simpl; eauto.
Qed.

Ltac simplify_val :=
  repeat match goal with
  | H: context[to_val (of_val ?v)] |- _ =>
      do !rewrite to_of_val in H
  | H: is_val ?e |- _ =>
      let v := fresh "v" in
      let Hv := fresh "H" v in
      destruct (proj1 (is_val_spec e) H) as [v Hv]; clear H
  | H: to_val ?e = Some ?v |- _ =>
      assert (e = of_val v) as -> by (apply of_to_val in H; auto); clear H
  | |- context[to_val (of_val ?v)] =>
      do !rewrite to_of_val
  end.

Tactic Notation "solve_val" "by" tactic(tac) :=
  solve [ simpl in *; intuition; eauto; repeat match goal with
          | |- context[is_val ?e] => do !rewrite is_val_spec
          end; simplify_val; by tac ].
Ltac solve_val := solve_val by eauto.

(* Misc *)
Lemma is_val_of_val v : is_val (of_val v).
Proof. solve_val. Qed.
#[export] Hint Resolve is_val_of_val : core.

(* Literals, operators, expressions, and values have decidable equality. *)
Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

(* Coq prop [is_val] is decidable. *)
Global Instance is_val_dec e : Decision (is_val e).
Proof.
  induction e;
  repeat match goal with
  | H: Decision (is_val ?e) |- _ => destruct H
  end; solve [left; solve_val | right; simpl in *; intuition].
Defined.

(** Substitution *)
(** [subst x es e] substitutes the expression [es] for the variable [x] in the
  * expression [e]. If [x] is a bound variable, it would not be substituted. *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Lit _ => e
  | Var y => if decide (x = y) then es else e
  | Lam y e' => if decide (BNamed x = y) then e else Lam y (subst x es e')
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | UnOp op e' => UnOp op (subst x es e')
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | If e0 e1 e2 => If (subst x es e0) (subst x es e1) (subst x es e2)
  | TApp e' => TApp (subst x es e')
  | TLam e' => TLam (subst x es e')
  | Pack e' => Pack (subst x es e')
  | Unpack y e1 e2 =>
      Unpack y (subst x es e1) (if decide (BNamed x = y) then e2 else subst x es e2)
  | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
  | Fst e' => Fst (subst x es e')
  | Snd e' => Snd (subst x es e')
  | InjL e' => InjL (subst x es e')
  | InjR e' => InjR (subst x es e')
  | Case e0 e1 e2 =>
      Case (subst x es e0) (subst x es e1) (subst x es e2)
  end.

Definition subst' (mx : binder) (es : expr) (e : expr) : expr :=
  match mx with BNamed x => subst x es e | BAnon => e end.


(** The stepping relation *)
Definition un_op_eval (op : un_op) (l : base_lit) : option base_lit :=
  match op, l with
  | NegOp, LitBool b => Some $ LitBool $ negb b
  | MinusUnOp, LitInt n => Some $ LitInt (-n)
  | LenOp, LitString s => Some $ LitInt $ Z.of_nat $ String.length s
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (l1 l2 : base_lit) : option base_lit :=
  match op, l1, l2 with
  | PlusOp, LitInt n1, LitInt n2 =>
      Some $ LitInt (n1 + n2)
  | MinusOp, LitInt n1, LitInt n2 =>
      Some $ LitInt (n1 - n2)
  | MultOp, LitInt n1, LitInt n2 =>
      Some $ LitInt (n1 * n2)
  | LtOp, LitInt n1, LitInt n2 =>
      Some $ LitBool $ bool_decide (n1 < n2)%Z
  | LeOp, LitInt n1, LitInt n2 =>
      Some $ LitBool $ bool_decide (n1 <= n2)%Z
  | GtOp, LitInt n1, LitInt n2 =>
      Some $ LitBool $ bool_decide (n1 > n2)%Z
  | GeOp, LitInt n1, LitInt n2 =>
      Some $ LitBool $ bool_decide (n1 >= n2)%Z
  | AndOp, LitBool b1, LitBool b2 =>
      Some $ LitBool (b1 && b2)
  | OrOp, LitBool b1, LitBool b2 =>
      Some $ LitBool (b1 || b2)
  | SubOp, LitBool b1, LitBool b2 =>
      Some $ LitBool $ bool_decide (b1 → b2)
  | ConcatOp, LitString s1, LitString s2 =>
      Some $ LitString (s1 ++ s2)
  | PrefixOp, LitString s1, LitString s2 =>
      Some $ LitBool $ String.prefix s1 s2
  | SubstrOp, LitString s1, LitString s2 =>
      Some $ LitBool $
        match String.index 0 s1 s2 with
        | Some _ => true
        | None => false
        end
  | EqOp, _, _ =>
      Some $ LitBool $ bool_decide (l1 = l2)
  | NeqOp, _, _ =>
      Some $ LitBool $ bool_decide (l1 ≠ l2)
  | _, _, _ => None
  end.

Inductive base_step : expr → expr → Prop :=
  | BetaS x e1 e2 e' :
      is_val e2 →
      e' = subst' x e2 e1 →
      base_step (App (Lam x e1) e2) e'
  | TBetaS e :
      base_step (TApp (TLam e)) e
  | UnpackS x e1 e2 e' :
      is_val e1 →
      e' = subst' x e1 e2 →
      base_step (Unpack x (Pack e1) e2) e'
  | UnOpS op l l' :
      un_op_eval op l = Some l' →
      base_step (UnOp op $ Lit l) (Lit l')
  | BinOpS op l1 l2 l' :
      bin_op_eval op l1 l2 = Some l' →
      base_step (BinOp op (Lit l1) (Lit l2)) (Lit l')
  | IfTrueS e1 e2 :
      base_step (If (Lit $ LitBool true) e1 e2) e1
  | IfFalseS e1 e2 :
      base_step (If (Lit $ LitBool false) e1 e2) e2
  | FstS e1 e2 :
      is_val e1 →
      is_val e2 →
      base_step (Fst (Pair e1 e2)) e1
  | SndS e1 e2 :
      is_val e1 →
      is_val e2 →
      base_step (Snd (Pair e1 e2)) e2
  | CaseLS e1 e2 e :
      is_val e →
      base_step (Case (InjL e) e1 e2) (App e1 e)
  | CaseRS e1 e2 e :
      is_val e →
      base_step (Case (InjR e) e1 e2) (App e2 e)
  .


(** We define evaluation contexts *)
Inductive ectx :=
  | HoleCtx
  | AppLCtx (K: ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K: ectx)
  | TAppCtx (K: ectx)
  | PackCtx (K: ectx)
  | UnpackCtx (x : binder) (K: ectx) (e2 : expr)
  | UnOpCtx (op : un_op) (K: ectx)
  | BinOpLCtx (op : bin_op) (K: ectx) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr) (K: ectx)
  | IfCtx (K: ectx) (e1 e2 : expr)
  | PairLCtx (K: ectx) (v2 : val)
  | PairRCtx (e1 : expr) (K: ectx)
  | FstCtx (K: ectx)
  | SndCtx (K: ectx)
  | InjLCtx (K: ectx)
  | InjRCtx (K: ectx)
  | CaseCtx (K: ectx) (e1 : expr) (e2 : expr) .

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | TAppCtx K => TApp (fill K e)
  | PackCtx K => Pack (fill K e)
  | UnpackCtx x K e2 => Unpack x (fill K e) e2
  | UnOpCtx op K => UnOp op (fill K e)
  | BinOpLCtx op K v2 => BinOp op (fill K e) (of_val v2)
  | BinOpRCtx op e1 K => BinOp op e1 (fill K e)
  | IfCtx K e1 e2 => If (fill K e) e1 e2
  | PairLCtx K v2 => Pair (fill K e) (of_val v2)
  | PairRCtx e1 K => Pair e1 (fill K e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  | InjLCtx K => InjL (fill K e)
  | InjRCtx K => InjR (fill K e)
  | CaseCtx K e1 e2 => Case (fill K e) e1 e2
  end.

Fixpoint comp_ectx (K: ectx) (K' : ectx) : ectx :=
  match K with
  | HoleCtx => K'
  | AppLCtx K v2 => AppLCtx (comp_ectx K K') v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K K')
  | TAppCtx K => TAppCtx (comp_ectx K K')
  | PackCtx K => PackCtx (comp_ectx K K')
  | UnpackCtx x K e2 => UnpackCtx x (comp_ectx K K') e2
  | UnOpCtx op K => UnOpCtx op (comp_ectx K K')
  | BinOpLCtx op K v2 => BinOpLCtx op (comp_ectx K K') v2
  | BinOpRCtx op e1 K => BinOpRCtx op e1 (comp_ectx K K')
  | IfCtx K e1 e2 => IfCtx (comp_ectx K K') e1 e2
  | PairLCtx K v2 => PairLCtx (comp_ectx K K') v2
  | PairRCtx e1 K => PairRCtx e1 (comp_ectx K K')
  | FstCtx K => FstCtx (comp_ectx K K')
  | SndCtx K => SndCtx (comp_ectx K K')
  | InjLCtx K => InjLCtx (comp_ectx K K')
  | InjRCtx K => InjRCtx (comp_ectx K K')
  | CaseCtx K e1 e2 => CaseCtx (comp_ectx K K') e1 e2
  end.

(** Contextual step *)
Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' →
    e2 = fill K e2' →
    base_step e1' e2' →
    contextual_step e1 e2.
Definition reducible (e : expr) := ∃ e', contextual_step e e'.

Definition empty_ectx := HoleCtx.

(** Basic properties about the evaluation contexts. *)
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.


(** Basic properties about the contextual step. *)
Lemma base_contextual_step e1 e2 :
  base_step e1 e2 → contextual_step e1 e2.
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 → contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

Lemma fill_rtc_contextual_step K e1 e2 :
  rtc contextual_step e1 e2 → rtc contextual_step (fill K e1) (fill K e2).
Proof.
  induction 1; try naive_solver.
  etrans; eauto using rtc_once, fill_contextual_step.
Qed.



Fixpoint is_closed (X : list string) (e : expr) : bool :=
   match e with
  | Var x => bool_decide (x ∈ X)
  | Lam x e => is_closed (x :b: X) e
  | Unpack x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | TApp e | TLam e | Pack e =>
      is_closed X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 =>
      is_closed X e1 && is_closed X e2
  |  If e0 e1 e2 | Case e0 e1 e2 =>
      is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

#[export] Instance is_closed_proof_irrel X e : ProofIrrel (is_closed X e).
Proof. apply _. Defined.
#[export] Instance is_closed_dec X e : Decision (is_closed X e).
Proof. apply _. Defined.

(** closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?; induction e in X |-*; simpl; intros ?; destruct_and?; split_and?; simplify_option_eq; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(** Substitution lemmas *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  induction e in X |-*; simpl; rewrite ?bool_decide_spec, ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.
Lemma subst'_is_closed_nil e x es : is_closed [] e → subst' x es e = e.
Proof. destruct x as [ | x]; eauto using subst_is_closed_nil. Qed.

Lemma is_closed_permutation X Y e :
  X ≡ₚ Y → is_closed X e = is_closed Y e.
Proof.
  intros HXY.
  induction e in X, Y, HXY |-*; simpl;
  repeat match goal with
  | HXY : ?X ≡ₚ ?Y, H : ∀ X Y, X ≡ₚ Y → is_closed X ?e = is_closed Y ?e |- _ =>
      rewrite (H X Y HXY)
  end; try done.
  - apply bool_decide_ext; by rewrite HXY.
  - destruct x as [|x]; eauto. apply IHe. by constructor.
  - destruct x as [|x]; simpl; erewrite IHe2; eauto.
Qed.

Global Instance is_closed_Permutation :
  Proper (Permutation ==> eq ==> eq) is_closed.
Proof.
  intros X Y HXY e _ <-.
  by apply is_closed_permutation.
Defined.