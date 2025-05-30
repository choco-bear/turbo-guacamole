Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Coq.Strings.String.
From stdpp Require Import relations base sets gmap.
Require Import Intro2TT.Tactics.
Set Default Goal Selector "!".
Open Scope string_scope.

(** ** Simply Typed Lambda Calculus *)
(** This file is part of the "Introduction to Type Theory."
  * It provides a simply typed lambda calculus with constants, lambda 
  * abstractions, and applications. The language is designed to be a minimalistic 
  * example for demonstrating type systems and operational semantics.
  *
  * The main goals of this file are:
  * - To define the syntax of a simply typed lambda calculus
  * - To provide an operational semantics for the language
  * - To define a type system for the language
  * - To prove soundness of the type system
  *)
Module STLC.



(** ** Syntax *)
(** This section defines the syntax of the language, including expressions,
  * values, and constants. The syntax is defined inductively to capture the
  * structure of the language. *)
Section Syntax.

  (** Expressions *)
  (** Expressions are defined inductively with variables, lambda abstractions,
    * applications, and constants. Each constant has a name and a type. *)
  Inductive expr : Type :=
    | Var : string → expr
    | Lam : string → expr → expr
    | App : expr → expr → expr
    | Const : string → string → expr.

  Inductive value : expr → Prop :=
    | ConstV (c T : string) : value (Const c T)
    | LamV (x : string) (e : expr) : value (Lam x e).

End Syntax.
Hint Constructors value : core.

(** The below are just for human-readable notation. *)
Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.
Notation "λ: x , e" := (Lam x e%E)
  (at level 200, x at level 1, e at level 200,
  format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x (Lam y .. (Lam z e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
  format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.
Notation "'const' c 'of' 'type' T" := (Const c T)
  (at level 200, c at level 1, T at level 1,
  format "'[' 'const' '/  ' c '/  ' 'of' '/ ' 'type' '/  ' T ']'") : expr_scope.

Local Open Scope expr_scope.



(** ** Semantics *)
(** This section defines the semantics of the language, including substitution,
  * reduction relations, and stuckness. The semantics is defined inductively
  * to capture the operational behavior of the language. *)
Section Semantics.

  (** Substitution *)
  (** Substitution replaces a variable in an expression with another expression.
    * This is used in the beta-reduction step of the operational semantics.
    * The substitution function takes a variable name [x], an expression [e1] to
    * substitute, and an expression [e2] in which to perform the substitution. *)
  Fixpoint subst (x : string) (e1 e2 : expr) : expr :=
    match e2 with
    | Var y =>
        if String.eqb x y then e1 else Var y
    | λ: y, e =>
        if String.eqb x y then Lam y e else Lam y (subst x e1 e)
    | App e e' =>
        (subst x e1 e) (subst x e1 e')
    | Const _ _ => e2
    end.

  (** Reduction relation *)
  (** The reduction relation is defined inductively.
    * It captures the operational semantics of the language, including
    * application and beta-reduction. *)
  Inductive reduction : expr → expr → Prop :=
    | Red_App1 (e1 e1' v : expr) :
        reduction e1 e1' →
        value v →
        reduction (e1 v) (e1' v)
    | Red_App2 (e1 e2 e2' : expr) :
        reduction e2 e2' →
        reduction (e1 e2) (e1 e2')
    | Red_Beta (x : string) (e v : expr) :
        value v →
        reduction ((λ: x, e) v) (subst x v e).

  (** Stuckness *)
  (** An expression is stuck if it is not a value and cannot be reduced further.
    * This means it is in normal form but not a value. *)
  Definition stuck (e : expr) : Prop := ¬ value e ∧ nf reduction e.

End Semantics.
Hint Constructors reduction : core.
Notation "e '↝' e'" := (reduction e e') (at level 40).


(** ** Type System *)
Section TypeSystem.

  (** Types *)
  (** Types are defined as an inductive type with base types and function types. *)
  Inductive type : Type :=
    | TyBase : string → type
    | TyArrow : type → type → type.

  (** Context *)
  (** A context is a mapping from variable names to types. We use an association
    * list to represent this mapping. *)
  Definition ctx := gmap string type.

  (** Typing Rules *)
  (** Typing judgments are of the form [Γ ⊢ e : τ], meaning that in context [Γ],
    * expression [e] has type [τ]. *)
  Inductive has_type : ctx → expr → type → Prop :=
    | T_App : forall Γ e1 e2 τ1 τ2,
        has_type Γ e1 (TyArrow τ1 τ2) →
        has_type Γ e2 τ1 →
        has_type Γ (e1 e2) τ2
    | T_Lam : forall Γ x e τ1 τ2,
        has_type (<[x := τ1]> Γ) e τ2 →
        has_type Γ (λ: x, e) (TyArrow τ1 τ2)
    | T_Var : forall Γ (x : string) τ,
        Γ !! x = Some τ →
        has_type Γ x τ
    | T_Const : forall Γ c T,
        has_type Γ (const c of type T) (TyBase T)
    .

End TypeSystem.
Hint Constructors has_type : core.

(** The below are just for human-readable notation. *)
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Coercion TyBase : string >-> type.
Notation "A → B" := (TyArrow A%ty B%ty) : ty_scope.

(** The below are just for human readable notation. *)
Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
Notation "∅" := (∅ : gmap string type) : ctx_scope.
Notation "x : τ ; Γ" := (<[x:=τ%ty]>Γ%ctx)
  (at level 60, τ at level 99, Γ at level 99, right associativity) : ctx_scope.

Notation "Γ '⊢' e ':' τ" := (has_type Γ%ctx e%E τ%ty)
  (at level 70, e at level 40, τ at level 40).


(** ** Lemmas *)
(** These lemmas are used to reason about the properties of the language,
  * including substitution, contexts, stuckness, and canonical forms. *)
Section Lemmas.

  (** Context *)
  (** These lemmas are used to manipulate contexts, particularly for
    * looking up variables and ensuring that the context behaves as expected. *)
  Lemma ctx_empty x :
    ∅%ctx !! x = None.
  Proof. done. Qed.

  Lemma ctx_eq x τ (Γ : ctx) :
    (x : τ; Γ)%ctx !! x = Some τ.
  Proof.
    apply lookup_insert.
  Qed.

  Lemma ctx_eq_inv x τ σ (Γ : ctx) :
    (x : τ; Γ)%ctx !! x = Some σ →
    τ = σ.
  Proof.
    rewrite ctx_eq; intro; solve_by_invert.
  Qed.

  Lemma ctx_neq x y τ (Γ : ctx) :
    x ≠ y → (y : τ; Γ)%ctx !! x = Γ !! x.
  Proof.
    by intro; apply lookup_insert_ne.
  Qed.

  Lemma ctx_shadow x τ τ' (Γ : ctx) :
    (x : τ; x : τ'; Γ)%ctx = (x : τ; Γ)%ctx.
  Proof.
    apply insert_insert.
  Qed.

  Lemma ctx_permute x y τ σ (Γ : ctx) :
    x ≠ y → (x : τ; y : σ; Γ)%ctx = (y : σ; x : τ; Γ)%ctx.
  Proof.
    apply insert_commute.
  Qed.

  (** Stuckness *)
  (** These lemmas are used to reason about stuck expressions and values. *)
  Lemma value_nf v :
    value v → nf reduction v.
  Proof. inversion 1; intro; solve_by_inverts 2. Qed.

  Lemma var_stuck (x : string) :
    stuck x.
  Proof. split; intro; solve_by_inverts 2. Qed.

  (** Canonical Forms *)
  (** These lemmas are used to extract canonical forms from values and types. *)
  Lemma base_canonical v (T : string) Γ :
    value v →
    Γ ⊢ v : T →
    ∃ c, v = const c of type T.
  Proof. do 2 inversion 1; eauto. Qed.

  Lemma arrow_canonical v τ1 τ2 Γ :
    value v →
    Γ ⊢ v : (τ1 → τ2) →
    ∃ x e, v = λ: x, e.
  Proof. do 2 inversion 1; eauto. Qed.

  (** Weakening *)
  (** These lemmas are used to weaken the context in which typing judgments hold. *)
  Lemma weakening e τ Γ Γ' :
    Γ ⊆ Γ' →
    Γ ⊢ e : τ →
    Γ' ⊢ e : τ.
  Proof.
    intros ? Hty; generalize dependent Γ'.
    induction Hty; eauto; intros; constructor.
    - by apply IHHty, insert_mono.
    - by eapply lookup_weaken.
  Qed.

  Lemma weakening_empty e τ Γ :
    ∅ ⊢ e : τ →
    Γ ⊢ e : τ.
  Proof. apply weakening, map_empty_subseteq. Qed.

  (** Substitution Lemma *)
  (** This lemma states that substituting a value for a variable in an expression
    * preserves the typing of that expression. *)
  Lemma substitution_preserves_typing x e v σ τ Γ :
    (x : σ; Γ) ⊢ e : τ →
    ∅ ⊢ v : σ →
    Γ ⊢ subst x v e : τ.
  Proof.
    revert x v σ τ Γ.
    induction e; inversion 1; subst; intros;
      try solve [simpl; eauto]; bdestruct (s =? x); subst; simpl.
    - apply ctx_eq_inv in H2; subst. rewrite String.eqb_refl.
      by apply weakening_empty.
    - rewrite (proj2 (eqb_neq _ _)); eauto.
      rewrite ctx_neq in H2; eauto.
    - rewrite String.eqb_refl.
      rewrite ctx_shadow in H4; eauto.
    - rewrite (proj2 (eqb_neq _ _)); eauto.
      constructor. eapply IHe; eauto.
      eapply weakening; eauto. by rewrite ctx_permute.
  Qed.

End Lemmas.



(** ** Soundness *)
(** This section contains the main theorems of the language, including progress,
  * preservation, and soundness. These theorems ensure that the type system is
  * consistent and that well-typed expressions can be reduced to values. *)
Section Soundness.

  (** Progress Theorem *)
  (** The progress theorem states that if an expression is well-typed, it is either
    * a value or can take a step in the reduction relation. *)
  Theorem progress e τ :
    ∅ ⊢ e : τ →
    value e ∨ (exists e', e ↝ e').
  Proof.
    remember ∅ as Γ. induction 1; intuition;
      [ destruct (arrow_canonical _ _ _ _ H2 H) as (x & e & ->)
      | destruct H3
      | destruct H2
      | destruct H3
      | by subst ]; eauto.
  Qed.

  (** Preservation Theorem *)
  (** The preservation theorem states that if an expression is well-typed and
    * can take a step in the reduction relation, then the resulting expression
    * is also well-typed with the same type. This ensures that the type system
    * is preserved under reduction. *)
  Theorem preservation e e' τ :
    ∅ ⊢ e : τ →
    e ↝ e' →
    ∅ ⊢ e' : τ.
  Proof.
    remember ∅ as Γ. intro H. revert e'. induction H; intuition.
    - inversion H3; subst; eauto.
      eapply substitution_preserves_typing; eauto; by inversion H.
    - exfalso. eapply value_nf; eauto.
    - exfalso. eapply var_stuck. eauto.
    - exfalso. eapply (value_nf (const c of type T)); eauto.
  Qed.

  (** Soundness Theorem *)
  (** The soundness theorem states that if an expression is well-typed and can
    * take multiple steps in the reduction relation, then it cannot be stuck. *)
  Notation "t1 '↝*' t2" := (rtc reduction t1 t2) (at level 40).

  Corollary soundness e e' τ :
    ∅ ⊢ e : τ →
    e ↝* e' →
    ¬ stuck e'.
  Proof.
    intros Hty Hrtc. induction Hrtc as [e | e e' e'' Hred Hrtc IH].
    - apply progress in Hty as [Hv|[e' Hred]]; intros []; by eauto.
    - eauto using preservation.
  Qed.

End Soundness.


(** ** Context Invariance *)
(** This section contains theorems and lemmas related to the invariance of typing
  * under changes to the context. Context invariance is a crucial property of
  * typed lambda calculi, as it ensures that the typing judgments remain valid
  * even when the context is modified, as long as the free variables are
  * appropriately accounted for. *)
Section ContextInvariance.

  (** Free Variables *)
  (** The free variables of an expression are defined as those variables that
    * appear in the expression but are not bound by a lambda abstraction. *)
  Fixpoint free_vars (e : expr) : gset string :=
    match e with
    | Var x => {[x]}
    | Lam x e' => (free_vars e') ∖ {[x]}
    | App e1 e2 => (free_vars e1) ∪ (free_vars e2)
    | Const _ _ => ∅%stdpp
    end.
  Notation "'FV' e" := (free_vars e) (at level 60).

  (** Closed Expressions *)
  (** An expression is closed if it has no free variables, meaning all variables
    * are bound by lambda abstractions. This is important for ensuring that
    * expressions can be evaluated without needing to reference external variables. *)
  Definition closed (e : expr) : Prop :=
    forall x, x ∉ FV e.

  (** Free Variables in Context *)
  (** This theorem states that if a variable [x] is free in an expression [e]
    * and [e] is well-typed in context [Γ], then there exists a type [τ'] such
    * that [x] is bound to [τ'] in the context [Γ]. This is crucial for ensuring
    * that the type system can account for all free variables in expressions. *)
  Theorem free_in_ctx x e τ Γ :
    x ∈ FV e →
    Γ ⊢ e : τ →
    ∃ τ', Γ !! x = Some τ'.
  Proof.
    intros. revert H. induction H0; intros; simpl in *; set_unfold; intuition.
    - destruct H. exists x1.
      by rewrite ctx_neq in H.
    - set_solver.
  Qed.

  Corollary has_type_closed e τ :
    ∅ ⊢ e : τ →
    closed e.
  Proof.
    do 3 intro. rename H into Hty. rename H0 into H.
    by destruct (free_in_ctx x _ _ _ H Hty).
  Qed.

  (** Context Invariance Theorem *)
  (** This theorem states that if an expression is well-typed in one context, it
    * remains well-typed in another context that has the same variable bindings for
    * the free variables of the expression. This is crucial for ensuring that the
    * type system is invariant under changes to the context. Furthermore, this
    * theorem can be considered as a generalization of the weakening lemma. *)
  Theorem ctx_invariance e τ Γ Γ' :
    Γ ⊢ e : τ →
    (∀ x, x ∈ FV e → Γ !! x = Γ' !! x) →
    Γ' ⊢ e : τ.
  Proof.
    intro; revert Γ'; induction H; intros; auto.
    - econstructor; [ apply IHhas_type1
                    | apply IHhas_type2]; intros; apply H1; set_solver.
    - constructor. apply IHhas_type. intros.
      bdestruct (x =? x0); subst; rewrite ?ctx_eq, ?ctx_neq; eauto.
      apply H0. set_solver.
    - rewrite (H0 x) in H; by first [constructor | set_solver].
  Qed.

  Corollary closed_strengthen e τ Γ :
    closed e →
    Γ ⊢ e : τ →
    ∅ ⊢ e : τ.
  Proof.
    intros Hcl Hty. apply ctx_invariance with Γ; auto.
    intros x contra. exfalso. by eapply Hcl.
  Qed.

End ContextInvariance.



(** ** Further Explorations *)
(** This section contains additional explorations and properties of the language. *)
Section Further.

  (** Type Size *)
  (** This function computes the size of a type, which is useful for reasoning
    * about the complexity of types in the language. It counts the number of
    * base types and function types in the type. *)
  Fixpoint type_size (τ : type) : nat :=
    match τ with
    | TyBase _ => 1
    | TyArrow τ1 τ2 => type_size τ1 + type_size τ2
    end.

  Lemma type_size_not_0 τ :
    type_size τ ≠ 0.
  Proof. induction τ; simpl; lia. Qed.

  (** Value Not Well-Typed *)
  (** This proposition states that the expression [λ: "x", "x" "x"] cannot have
    * any type. This is a common example of a counterexample of the converse of
    * the soundness theorem *)
  Proposition ω_has_no_type τ :
    ¬ ∅ ⊢ (λ: "x", "x" "x") : τ.
  Proof.
    intro. inversion H; subst.
    assert (∃ τ, τ = (τ → τ2)%ty) as [τ H0].
    { inversion H4; inversion H3; inversion H9; 
      inversion H6; inversion H2; inversion H14; subst; eauto. }
    assert (type_size τ = type_size (τ → τ2)%ty) by by rewrite <-H0.
    apply (type_size_not_0 τ2). simpl in *. lia.
  Qed.

  (** Identity Function *)
  (** This proposition states that the identity function [λ: "x", "x"] is well-typed
    * for any type of the form [τ → τ]. This is a fundamental property of the
    * identity function in typed lambda calculus. Moreover, it illustrates the
    * principle of polymorphism, where a function can be applied to arguments of
    * different types while maintaining its type correctness. *)
  Proposition id_well_typed τ :
    ∅ ⊢ (λ: "x", "x") : (τ → τ).
  Proof. by apply T_Lam, T_Var. Qed.

End Further.

End STLC.