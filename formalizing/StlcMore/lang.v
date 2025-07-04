Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From stdpp Require Export binders strings.
From stdpp Require Import option.
From Intro2TT.lib Require Export maps.

(** ** Language of STLC with More Types *)
(** This file defines the language of STLC with more types, including integers,
    booleans, unit, and product/sum types. *)

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** ** Expressions and values. *)
(** [Z] is Coq's version of the integers.
    All the standard operations, like [+], are defined on it.

    The type [binder] is defined as [x ::= BNamed (s: string) | BAnon]
    where BAnon can be used if we don't want to use the variable in
    the function.
*)
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitString (s : string) | LitUnit.
Inductive un_op : Set :=
  | NegOp (* Boolean Negation *)
  | MinusUnOp (* Integer Negation *)
  | LenOp (* String Length *)
  .
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp (* Integer Arithmetics *)
  | LtOp | LeOp | EqOp (* Integer Comparisons *)
  | AndOp | OrOp (* Logical Operators *)
  | ConcatOp (* String Concatenation *)
  | StrEqOp | PrefixOp (* String Equality and Prefix *)
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
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope val_scope with val.

Fixpoint of_val (v : val) : expr :=
  match v with
  | LitV l => Lit l
  | LamV x e => Lam x e
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lit l => Some $ LitV l
  | Lam x e => Some $ LamV x e
  | Pair e1 e2 =>
      to_val e1 ≫= (λ v1, to_val e2 ≫= (λ v2, Some $ PairV v1 v2))
  | InjL e => to_val e ≫= (λ v, Some $ InjLV v)
  | InjR e => to_val e ≫= (λ v, Some $ InjRV v)
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

#[export] Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite <-!to_of_val, Hv. Qed.

Fixpoint is_val (e : expr) : Prop :=
  match e with
  | Lit l => True
  | Lam x e => True
  | Pair e1 e2 => is_val e1 ∧ is_val e2
  | InjL e => is_val e
  | InjR e => is_val e
  | _ => False
  end.
Lemma is_val_spec e :
  is_val e ↔ ∃ v, to_val e = Some v.
Proof.
  split; intros H.
  - induction e; try by eauto.
    2-3: apply IHe in H as [v Hv]; simpl; rewrite Hv; eauto.
    inversion H; intuition. destruct H2, H3. simpl. rewrite H2, H3. eauto.
  - destruct H as [v Hv]. by apply of_to_val in Hv; subst; induction v.
Qed.

Ltac simplify_val :=
  repeat match goal with
  | H: to_val (of_val ?v) = ?o |- _ => rewrite to_of_val in H
  | H: is_val ?e |- _ => destruct (proj1 (is_val_spec e) H) as (? & ?); clear H
  | H: to_val ?e = Some ?v |- _ =>
      assert (e = of_val v) as -> by (apply of_to_val in H; auto); clear H
  end.

(* Misc *)
Lemma is_val_of_val v : is_val (of_val v).
Proof. rewrite is_val_spec, to_of_val; eauto. Qed.
#[export] Hint Resolve is_val_of_val : core.

Lemma is_val_lit l : is_val $ Lit l.
Proof. done. Qed.
#[export] Hint Resolve is_val_lit : core.


(** Substitution *)
(** [subst x es e] substitutes the expression [es] for the variable [x] in the
  * expression [e]. If [x] is a bound variable, it would not be substituted. *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Lit _ => e
  | Var y => if decide (x = y) then es else Var y
  | Lam y e =>
      Lam y $ if decide (BNamed x = y) then e else subst x es e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | UnOp o e => UnOp o (subst x es e)
  | BinOp o e1 e2 => BinOp o (subst x es e1) (subst x es e2)
  | If e0 e1 e2 => If (subst x es e0) (subst x es e1) (subst x es e2)
  | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
  | Fst e => Fst (subst x es e)
  | Snd e => Snd (subst x es e)
  | InjL e => InjL (subst x es e)
  | InjR e => InjR (subst x es e)
  | Case e0 e1 e2 => Case (subst x es e0) (subst x es e1) (subst x es e2)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with
  | BNamed x => subst x es
  | BAnon => id (* No substitution for anonymous binders *)
  end.


(** Closed Terms *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ => true
  | Var x => bool_decide (x ∈ X)
  | Lam x e => is_closed (x :b: X) e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 => is_closed X e1 && is_closed X e2
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e => is_closed X e
  | If e0 e1 e2 | Case e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

(** [closed] states closedness as a Coq proposition *)
Definition closed (X : list string) (e : expr) : Prop := Is_true (is_closed X e).
#[export] Instance closed_proof_irrel X e : ProofIrrel (closed X e).
Proof. unfold closed. apply _. Qed.
#[export] Instance closed_dec X e : Decision (closed X e).
Proof. unfold closed. apply _. Defined.

(** closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?.
  induction e in X |-*; simpl; intros ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
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
Proof. intros. destruct x as [ | x]. { done. } by apply subst_is_closed_nil. Qed.

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
Qed.

Global Instance is_closed_Permutation :
  Proper (Permutation ==> eq ==> eq) is_closed.
Proof.
  intros X Y HXY e _ <-.
  by apply is_closed_permutation.
Defined.