Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Coq.Strings.String.
From stdpp Require Import relations base sets gmap.
Require Import Intro2TT.Tactics.
Set Default Goal Selector "!".
Open Scope string_scope.

(** ** Simply Typed Lambda Calculus with Arithmetic *)
(** This file defines a simply typed lambda calculus with arithmetic operations, 
  * including integer arithmetic, boolean logic, and product/sum types. It includes
  * syntax definitions, reduction semantics, a basic type system, and the soundness
  * proof.
  *
  * The main goal is to establish the soundness of the type system with respect to
  * the operational semantics. *)
Module STLCArith.



(** ** Syntax *)
(** This section defines the syntax of the language, including operators, literals,
  * expressions, and values. The syntax is defined inductively to capture the
  * structure of the language. *)
Section Syntax.

  (** Operators *)
  (** The language includes binary operators for arithmetic, comparison, and logic,
    * as well as unary operators for negation and boolean negation. *)
  Inductive bop : Type := 
    (* Integer Arithmetics *)
    | Plus | Minus | Mult | Div
    (* Integer Comparison *)
    | IEq | Lt
    (* Logic Operations *)
    | BEq | And | Or
    .
  Inductive uop : Type :=
    (* Unary Minus *)
    | UMinus
    (* Boolean Negation *)
    | Neg
    .
  
  (** Literals *)
  (** The language supports integer literals, boolean literals, and unit literals.
    * These are used to represent basic values in the language. *)
  Inductive lit : Type :=
    | LitInt : Z → lit
    | LitBool : bool → lit
    | LitUnit : unit → lit
    .
  
  (** Expressions *)
  (** The expressions of the language include variables, lambda abstractions, 
    * applications, literals, operators, conditionals, let-bindings, sequences,
    * pairs, and either types. The syntax is designed to be extensible for future
    * additions. *)
  Inductive expr : Type :=
    (* STLC *)
    | Var : string → expr
    | Lam : string → expr → expr
    | App : expr → expr → expr
    (* Literal *)
    | Lit : lit → expr
    (* Operators *)
    | Bop : bop → expr → expr → expr
    | Uop : uop → expr → expr
    (* If then else *)
    | ITE : expr → expr → expr → expr
    (* Let *)
    | Let : string → expr → expr → expr
    (* Seq *)
    | Seq : expr → expr → expr
    (* Pair *)
    | Pair : expr → expr → expr
    | Fst : expr → expr
    | Snd : expr → expr
    (* Either *)
    | InjL : expr → expr
    | InjR : expr → expr
    | Match : expr → string → expr → string → expr → expr
    .
  
  (** Value *)
  (** Values in the language are defined as expressions that cannot be reduced 
    * further. This includes literals, pairs, and either types. The value definition
    * is used to determine if an expression is a value in the context of reduction
    * semantics. *)
  Inductive value : expr → Prop :=
    | LitV lit :
        value (Lit lit)
    | LamV x e :
        value (Lam x e)
    | PairV v1 v2 :
        value v1 →
        value v2 →
        value (Pair v1 v2)
    | InjLV v :
        value v →
        value (InjL v)
    | InjRV v :
        value v →
        value (InjR v)
    .
  (** The [value] inductive is used to define the set of values in the language.
    * It captures the structure of values, including literals, lambda abstractions,
    * fixpoints, pairs, and either types. The [value] predicate is used in the
    * reduction semantics to determine if an expression is a value. *)

End Syntax.
Hint Constructors value : core.

(** The below are just for human-readable notations. *)
Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Coercion Var : string >-> expr.
Notation "λ: x , e" := (Lam x e%E)
  (at level 200, x at level 1, e at level 200,
  format "'[' 'λ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Lam x (Lam y .. (Lam z e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
  format "'[' 'λ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.
Coercion App : expr >-> Funclass.

Notation "'#' l" := (Lit l) (at level 0) : expr_scope.
Coercion LitInt : Z >-> lit.
Coercion LitBool : bool >-> lit.
Coercion LitUnit : unit >-> lit.

Infix "+" := (Bop Plus) : expr_scope.
Infix "-" := (Bop Minus) : expr_scope.
Infix "*" := (Bop Mult) : expr_scope.
Infix "/" := (Bop Div) : expr_scope.
Infix "=?" := (Bop IEq) : expr_scope.
Infix "<?" := (Bop Lt) : expr_scope.
Infix "=?" := (Bop BEq) : expr_scope.
Infix "&&" := (Bop And) : expr_scope.
Infix "||" := (Bop Or) : expr_scope.

Notation "'-' e" := (Uop UMinus e%E) : expr_scope.
Notation "'¬' e" := (Uop Neg e%E) : expr_scope.

Notation "'if:' e1 'then' e2 'else' e3" := (ITE e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

Notation "'let:' x ':=' e1 'in' e2" := (Let x e1%E e2%E)
  (at level 200, x at level 1, e1, e2 at level 200) : expr_scope.

Notation "e1 ';;' e2" := (Seq e1%E e2%E) (at level 100, e2 at level 200) : expr_scope.

Notation "'fix:' f" := (Fix f%E) (at level 200, f at level 200) : expr_scope.

Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_scope.
Notation "'fst'" := Fst : expr_scope.
Notation "'snd'" := Snd : expr_scope.

Notation "'inl' e" := (InjL e%E) (at level 200, e at level 200) : expr_scope.
Notation "'inr' e" := (InjR e%E) (at level 200, e at level 200): expr_scope.
Notation "'match:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Match e0%E x1 e1%E x2 e2%E)
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.
Notation "'match:' e0 'with' 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
  (Match e0%E x2 e2%E x1 e1%E)
  (e0, x1, e1, x2, e2 at level 200, only parsing) : expr_scope.



(** Semantics *)
(** This section defines the operational semantics of the language, including
  * substitution, evaluation, and reduction relations. *)
Section Semantics.

  (** Subtitution *)
  (** The substitution function replaces occurrences of a variable in an expression
    * with another expression. It is defined recursively over the structure of the
    * expression, ensuring that variable bindings are respected. *)
  Fixpoint subst (x : string) (e1 e2 : expr) : expr :=
    match e2 with
    | Var y =>
        if String.eqb x y then e1 else e2
    | (λ: y, e)%E =>
        if String.eqb x y then e2 else (λ: y, subst x e1 e)%E
    | App e e' =>
        App (subst x e1 e) (subst x e1 e')
    | Lit _ => e2
    | Bop bop e e' =>
        Bop bop (subst x e1 e) (subst x e1 e')
    | Uop uop e =>
        Uop uop (subst x e1 e)
    | (if: cond then et else ef)%E =>
        (if: subst x e1 cond then subst x e1 et else subst x e1 ef)%E
    | (let: y := e in e')%E =>
        (let: y := subst x e1 e in (if String.eqb x y then e' else subst x e1 e'))%E
    | (e ;; e')%E =>
        (subst x e1 e ;; subst x e1 e')%E
    | (e, e')%E =>
        (subst x e1 e, subst x e1 e')%E
    | (fst e)%E =>
        (fst (subst x e1 e))%E
    | (snd e)%E =>
        (snd (subst x e1 e))%E
    | (inl e)%E =>
        (inl (subst x e1 e))%E
    | (inr e)%E =>
        (inr (subst x e1 e))%E
    | Match e' x1 e1' x2 e2' =>
        Match (subst x e1 e')
              x1 (if String.eqb x x1 then e1' else subst x e1 e1')
              x2 (if String.eqb x x2 then e2' else subst x e1 e2')
    end.
  
  (** Evaluation of binary and unary operators *)
  (** The evaluation functions for binary and unary operators take an operator and
    * two literals (for binary operators) or one literal (for unary operators) and
    * return an option type indicating the result of the operation. If the operation
    * is valid, it returns Some result; otherwise, it returns None. *)
  Definition bop_eval : bop → lit → lit → option lit :=
    λ bop l1 l2, 
      match (l1, l2) with
      | (LitInt n1, LitInt n2) => (
          match bop with
          | Plus => Some (LitInt (n1 + n2))
          | Minus => Some (LitInt (n1 - n2))
          | Mult => Some (LitInt (n1 * n2))
          | Div => Some (LitInt (n1 / n2))
          | IEq => Some (LitBool (n1 =? n2)%Z)
          | Lt => Some (LitBool (n1 <? n2)%Z)
          | _ => None
          end)
      | (LitBool b1, LitBool b2) => (
          match bop with
          | BEq => Some (LitBool (eqb b1 b2))
          | And => Some (LitBool (andb b1 b2))
          | Or => Some (LitBool (orb b1 b2))
          | _ => None
          end)
      | _ => None
      end.
  Definition uop_eval : uop → lit → option lit :=
    λ uop l,
      match (uop, l) with
      | (UMinus, LitInt n) => Some (LitInt (-n))
      | (Neg, LitBool b) => Some (LitBool (negb b))
      | _ => None
      end.

  (** Reduction Relation *)
  (** The reduction relation defines how expressions can be reduced to simpler forms.
    * It captures the operational semantics of the language, allowing expressions to
    * be evaluated step by step. *)
  Inductive reduction : expr → expr → Prop :=
    | RedApp1 e1 e1' v :
        reduction e1 e1' →
        value v →
        reduction (e1 v) (e1' v)
    | RedApp2 e1 e2 e2' :
        reduction e2 e2' →
        reduction (App e1 e2) (App e1 e2')
    | RedBeta x e v :
        value v →
        reduction ((λ: x, e) v)%E (subst x v e)
    | RedBop1 bop e1 e1' v :
        reduction e1 e1' →
        value v →
        reduction (Bop bop e1 v) (Bop bop e1' v)
    | RedBop2 bop e1 e2 e2' :
        reduction e2 e2' →
        reduction (Bop bop e1 e2) (Bop bop e1 e2')
    | RedBop bop l1 l2 l :
        bop_eval bop l1 l2 = Some l →
        reduction (Bop bop (Lit l1) (Lit l2)) (Lit l)
    | RedUopStep uop e1 e1' :
        reduction e1 e1' →
        reduction (Uop uop e1) (Uop uop e1')
    | RedUop uop l l' :
        uop_eval uop l = Some l' →
        reduction (Uop uop (Lit l)) (Lit l')
    | RedIf e e' et ef :
        reduction e e' →
        reduction (ITE e et ef) (ITE e' et ef)
    | RedIfTrue et ef :
        reduction (if: #true then et else ef)%E et
    | RedIfFalse et ef :
        reduction (if: #false then et else ef)%E ef
    | RedLetStep x e1 e1' e2 :
        reduction e1 e1' →
        reduction (let: x := e1 in e2)%E (let: x := e1' in e2)%E
    | RedLet x v e :
        value v →
        reduction (let: x := v in e)%E (subst x v e)
    | RedSeqStep e1 e1' e2 :
        reduction e1 e1' →
        reduction (e1 ;; e2)%E (e1' ;; e2)%E
    | RedSeqSkip v e :
        value v →
        reduction (v ;; e)%E e
    | RedPair1 e e' v :
        reduction e e' →
        value v →
        reduction (e, v)%E (e', v)%E
    | RedPair2 e1 e2 e2' :
        reduction e2 e2' →
        reduction (e1, e2)%E (e1, e2')%E
    | RedFstStep e e' :
        reduction e e' →
        reduction (fst e)%E (fst e')%E
    | RedFstProj v1 v2 :
        value v1 →
        value v2 →
        reduction (fst (v1, v2))%E v1
    | RedSndStep e e' :
        reduction e e' →
        reduction (snd e)%E (snd e')%E
    | RedSndProj v1 v2 :
        value v1 →
        value v2 →
        reduction (snd (v1, v2))%E v2
    | RedInjL e e' :
        reduction e e' →
        reduction (inl e)%E (inl e')%E
    | RedInjR e e' :
        reduction e e' →
        reduction (inr e)%E (inr e')%E
    | RedMatchStep e e' x1 e1 x2 e2 :
        reduction e e' →
        reduction (Match e x1 e1 x2 e2) (Match e' x1 e1 x2 e2)
    | RedMatchInjL v x1 e1 x2 e2 :
        reduction (Match (inl v)%E x1 e1 x2 e2) (subst x1 v e1)
    | RedMatchInlR v x1 e1 x2 e2 :
        reduction (Match (inr v)%E x1 e1 x2 e2) (subst x2 v e2)
    .

    Definition stuck (e : expr) : Prop := ¬ value e ∧ nf reduction e.

End Semantics.
Hint Constructors reduction : core.
Notation "e '↝' e'" := (reduction e e') (at level 40).



(** ** Type System *)
(** This section defines the type system for the language, including types and
  * typing rules. The type system is designed to ensure that well-typed expressions
  * can be reduced to values without encountering runtime errors. *)
Section TypeSystem.

  (** Types *)
  (** The types of the language include basic types such as integers, booleans,
    * unit, function types, product types, and sum types. These types are used to
    * classify expressions and ensure type safety in the language. *)
  Inductive type : Type :=
    | TyUnit : type
    | TyInt : type
    | TyBool : type
    | TyArrow : type → type → type
    | TyProd : type → type → type
    | TySum : type → type → type
    .

  (** Typing Context *)
  (** The typing context is a mapping from variable names to their types. It is used
    * to keep track of the types of variables in the language and is essential for
    * the typing rules. The typing context is defined as a map from strings
    * (variable names) to types. It is used to store the types of variables in the
    * language, allowing for type checking and inference during the typing process. *)
  Definition ctx := gmap string type.

  (** Typing Relation *)
  (** The typing relation defines how expressions can be assigned types based on
    * their structure and the typing context. It captures the rules of the type
    * system and ensures that well-typed expressions can be reduced safely. *)
  Definition bop_type : bop → type → type → option type :=
    λ bop τ1 τ2,
      match (bop, τ1, τ2) with
      (* Integer Arithmetics *)
      | (Plus, TyInt, TyInt) => Some TyInt
      | (Minus, TyInt, TyInt) => Some TyInt
      | (Mult, TyInt, TyInt) => Some TyInt
      | (Div, TyInt, TyInt) => Some TyInt
      (* Integer Comparison *)
      | (IEq, TyInt, TyInt) => Some TyBool
      | (Lt, TyInt, TyInt) => Some TyBool
      (* Logic Operations *)
      | (BEq, TyBool, TyBool) => Some TyBool
      | (And, TyBool, TyBool) => Some TyBool
      | (Or, TyBool, TyBool) => Some TyBool
      (* Other cases are invalid *)
      | _ => None
      end.
  Definition uop_type : uop → type → option type :=
    λ uop τ,
      match (uop, τ) with
      (* Integer Negation *)
      | (UMinus, TyInt) => Some TyInt
      (* Boolean Negation *)
      | (Neg, TyBool) => Some TyBool
      (* Other cases are invalid *)
      | _ => None
      end.

  (** Typing Rules *)
  (** The typing rules define how expressions can be assigned types based on their
    * structure and the typing context. These rules ensure that well-typed expressions
    * can be reduced safely without encountering runtime errors. *)
  Inductive has_type : ctx → expr → type → Prop :=
    (* Variables *)
    | TyVar Γ x τ :
        Γ !! x = Some τ →
        has_type Γ (Var x) τ
    (* Lambda Abstraction *)
    | TyLam Γ x e τ1 τ2 :
        has_type (<[ x := τ1 ]> Γ) e τ2 →
        has_type Γ (λ: x, e)%E (TyArrow τ1 τ2)
    (* Application *)
    | TyApp Γ e1 e2 τ1 τ2 :
        has_type Γ e1 (TyArrow τ1 τ2) →
        has_type Γ e2 τ1 →
        has_type Γ (App e1 e2) τ2
    (* Literals *)
    | TyLitInt Γ (n : Z) :
        has_type Γ (# n)%E TyInt
    | TyLitBool Γ (b : bool) :
        has_type Γ (# b)%E TyBool
    | TyLitUnit Γ :
        has_type Γ (# ())%E TyUnit
    (* Binary Operators *)
    | TyBop Γ bop e1 e2 τ1 τ2 τ :
        has_type Γ e1 τ1 →
        has_type Γ e2 τ2 →
        bop_type bop τ1 τ2 = Some τ →
        has_type Γ (Bop bop e1 e2) τ
    (* Unary Operators *)
    | TyUop Γ uop e τ τ' :
        has_type Γ e τ →
        uop_type uop τ = Some τ' →
        has_type Γ (Uop uop e) τ'
    (* If-Then-Else *)
    | TyIf Γ e1 e2 e3 τ :
        has_type Γ e1 TyBool →
        has_type Γ e2 τ →
        has_type Γ e3 τ →
        has_type Γ (ITE e1 e2 e3) τ
    (* Let Bindings *)
    | TyLet Γ x e1 e2 τ1 τ2 :
        has_type Γ e1 τ1 →
        has_type (<[ x := τ1 ]> Γ) e2 τ2 →
        has_type Γ (Let x e1 e2) τ2
    (* Sequences *)
    | TySeq Γ e1 e2 τ σ :
        has_type Γ e1 σ →
        has_type Γ e2 τ →
        has_type Γ (Seq e1 e2) τ
    (* Pairs *)
    | TyPair Γ e1 e2 τ1 τ2 :
        has_type Γ e1 τ1 →
        has_type Γ e2 τ2 →
        has_type Γ (Pair e1 e2) (TyProd τ1 τ2)
    (* Projections *)
    | TyFst Γ e τ1 τ2 :
        has_type Γ e (TyProd τ1 τ2) →
        has_type Γ (Fst e) τ1
    | TySnd Γ e τ1 τ2 :
        has_type Γ e (TyProd τ1 τ2) →
        has_type Γ (Snd e) τ2
    (* Either Types *)
    | TyInjL Γ e τ1 τ2 :
        has_type Γ e τ1 →
        has_type Γ (InjL e) (TySum τ1 τ2)
    | TyInjR Γ e τ1 τ2 :
        has_type Γ e τ2 →
        has_type Γ (InjR e) (TySum τ1 τ2)
    (* Match *)
    | TyMatch Γ e x1 e1 x2 e2 τ1 τ2 τ :
        has_type Γ e (TySum τ1 τ2) →
        has_type (<[ x1 := τ1 ]> Γ) e1 τ →
        has_type (<[ x2 := τ2 ]> Γ) e2 τ →
        has_type Γ (Match e x1 e1 x2 e2) τ
    .

End TypeSystem.
Hint Constructors has_type : core.

(** The below are just for human-readable notations. *)
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Notation "'()'" := TyUnit : ty_scope.
Notation "'Int'" := TyInt : ty_scope.
Notation "'Bool'" := TyBool : ty_scope.
Notation "τ1 '→' τ2" := (TyArrow τ1 τ2) : ty_scope.
Notation "τ1 '×' τ2" := (TyProd τ1 τ2)
  (at level 40, left associativity) : ty_scope.
Notation "τ1 '+' τ2" := (TySum τ1 τ2)
  (at level 50, left associativity) : ty_scope.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
Notation "∅" := (∅ : gmap string type) : ctx_scope.
Notation "x : τ ; Γ" := (<[x%string := τ%ty]> Γ%ctx)
  (at level 70, τ at level 99, Γ at level 99, right associativity) : ctx_scope.

Notation "Γ '⊢' e ':' τ" := (has_type Γ%ctx e%E τ%ty)
  (at level 70, e at level 55, τ at level 60).



(** ** Lemmas *)
(** This section contains various lemmas that are useful for reasoning about the
  * language, its syntax, and its semantics. These lemmas are used to prove
  * properties of the language, such as preservation and progress, which are
  * essential for establishing the soundness of the type system. *)
Section Lemmas.

  (** Context *)
  (** This section defines properties of the typing context, including lookup
    * operations, equality, and shadowing. These properties are essential for
    * reasoning about the types of variables in the language and ensuring that
    * the typing rules are sound. *)
  Section Context.
    Local Open Scope ctx_scope.
    Implicit Type 
      (x y : string)
      (τ : type)
      (Γ : ctx).

    Lemma ctx_empty x :
      ∅ !! x = None.
    Proof. done. Qed.
    
    Lemma ctx_eq x τ Γ :
      (x : τ ; Γ) !! x = Some τ.
    Proof. apply lookup_insert. Qed.
    
    Lemma ctx_eq_inv x τ τ' Γ :
      (x : τ ; Γ) !! x = Some τ' →
      τ = τ'.
    Proof. by rewrite ctx_eq; inversion 1. Qed.
    
    Lemma ctx_neq x y τ Γ :
      x ≠ y → (y : τ ; Γ) !! x = Γ !! x.
    Proof. intro; by apply lookup_insert_ne. Qed.
    
    Lemma ctx_shadow x τ τ' Γ :
      (x : τ ; x : τ' ; Γ) = (x : τ ; Γ).
    Proof. apply insert_insert. Qed.
    
    Lemma ctx_permute x y τ τ' Γ :
      x ≠ y → (x : τ ; y : τ' ; Γ) = (y : τ' ; x : τ ; Γ).
    Proof. intro; by apply insert_commute. Qed. 
  End Context.

  (** Stuckness *)
  Section Stuckness.
    Lemma value_nf v :
      value v → nf reduction v.
    Proof. induction 1; intro; solve_by_inverts 2. Qed.

    Lemma var_stuck x :
      stuck (Var x).
    Proof. split; intro; solve_by_inverts 2. Qed.
  End Stuckness.

  (** Canonical Forms *)
  Section Canonical.
    Local Open Scope expr_scope.
    Implicit Type
      (e v : expr)
      (τ : type)
      (Γ : ctx)
      (n : Z)
      (b : bool).
  
    Lemma int_canonical v Γ :
      value v →
      Γ ⊢ v : Int →
      ∃ n, v = #n.
    Proof. intros; inversion H; solve_by_inverts 2. Qed.
    
    Lemma bool_canonical v Γ :
      value v →
      Γ ⊢ v : Bool →
      ∃ b, v = #b.
    Proof. intros; inversion H; solve_by_inverts 2. Qed.

    Lemma unit_canonical v Γ :
      value v →
      Γ ⊢ v : () →
      v = #().
    Proof. intros; solve_by_inverts 2. Qed.

    Lemma arrow_canonical v τ1 τ2 Γ :
      value v →
      Γ ⊢ v : (τ1 → τ2) →
      ∃ x e, v = λ: x, e.
    Proof. intros; solve_by_inverts 2. Qed.
    
    Lemma prod_canonical v τ1 τ2 Γ :
      value v →
      Γ ⊢ v : τ1 × τ2 →
      ∃ v1 v2, value v1 ∧ value v2 ∧ v = (v1, v2) ∧
               Γ ⊢ v1 : τ1 ∧ Γ ⊢ v2 : τ2.
    Proof.
      intros; inversion H; cycle 2.
      2-5: solve_by_inverts 2.
      inversion H0; subst; try solve_by_invert.
      inversion H7; subst. by exists v1, v2.
    Qed.
    
    Lemma sum_canonical v τ1 τ2 Γ :
      value v →
      Γ ⊢ v : τ1 + τ2 →
      ∃ v', value v' ∧ (v = (inl v') ∧ Γ ⊢ v' : τ1 ∨
                        v = (inr v') ∧ Γ ⊢ v' : τ2).
    Proof. intros; inversion H; inversion H0; subst; solve_by_invert. Qed.
  End Canonical.

  Section ContextInvariance.
    Implicit Types
      (e : expr)
      (x y : string)
      (τ : type)
      (Γ : ctx).

    Fixpoint free_vars e : gset string :=
      match e with
      | Var x => {[x]}
      | Lam x e' => (free_vars e') ∖ {[x]}
      | App e1 e2 | Bop _ e1 e2 | Seq e1 e2 | Pair e1 e2
          => (free_vars e1) ∪ (free_vars e2)
      | Uop _ e' | Fst e' | Snd e' | InjL e' | InjR e'
          => free_vars e'
      | ITE e1 e2 e3 => (free_vars e1) ∪ (free_vars e2) ∪ (free_vars e3)
      | Let x e1 e2 => (free_vars e1) ∪ ((free_vars e2) ∖ {[x]})
      | Match e' x1 e1 x2 e2
          => (free_vars e') ∪ ((free_vars e1) ∖ {[x1]}) ∪ ((free_vars e2) ∖ {[x2]})
      | _ => ∅
      end.
    Notation "'FV' e" := (free_vars e%E) (at level 60).

    Definition closed e : Prop := ∀ x, x ∉ FV e.

    Lemma free_in_ctx x e τ Γ :
      x ∈ FV e →
      Γ ⊢ e : τ →
      ∃ τ', Γ !! x = Some τ'.
    Proof.
      intros. revert H.
      induction H0; intros; cbn in *; try set_solver; set_unfold; intuition;
      first [by rewrite ctx_neq in H | by rewrite ctx_neq in H0].
    Qed.
    
    Corollary has_type_closed e τ :
      ∅ ⊢ e : τ →
      closed e.
    Proof. by do 3 intro; pose proof (free_in_ctx _ _ _ _ H0 H) as [τ' contra]. Qed.
    
    Lemma context_invariance e τ Γ Γ' :
      Γ ⊢ e : τ →
      (∀ x, x ∈ FV e → Γ !! x = Γ' !! x) →
      Γ' ⊢ e : τ.
    Proof.
      intro; revert Γ'; induction H; intros; eauto; econstructor;
      try match goal with 
          | H : _ |- _ => apply H 
          end; intros; subst;
      try solve [ apply H1; set_solver
                | apply H2; set_solver
                | rewrite <-H0; set_solver ];
      [ | | rename x1 into x0 | rename x2 into x0 ];
      bdestruct (x =? x0); subst; rewrite ?ctx_eq, ?ctx_neq; eauto;
      match goal with
      | H : _ |- _ => apply H
      end; set_solver.
    Qed.
    
    Corollary closed_strengthen e τ Γ :
      closed e →
      Γ ⊢ e : τ →
      ∅ ⊢ e : τ.
    Proof.
      intros. apply context_invariance with Γ; eauto.
      intros. by apply H in H1.
    Qed.

    Lemma weakening e τ Γ Γ' :
      Γ ⊆ Γ' →
      Γ ⊢ e : τ →
      Γ' ⊢ e : τ.
    Proof.
      intros. eapply context_invariance in H0; eauto.
      intros. pose proof (free_in_ctx _ _ _ _ H1 H0) as [τ' eqτ'].
      rewrite eqτ'. by pose proof (lookup_weaken _ _ _ _ eqτ' H).
    Qed.
    
    Corollary weakening_empty e τ Γ :
      ∅ ⊢ e : τ →
      Γ ⊢ e : τ.
    Proof. intro; eapply weakening; by try apply map_empty_subseteq. Qed.

    Corollary closed_empty e τ Γ :
      closed e →
      ∅ ⊢ e : τ ↔
      Γ ⊢ e : τ.
    Proof. split; [apply weakening_empty | by apply closed_strengthen]. Qed.
  End ContextInvariance.

  Section Subst.
    Lemma substitution_preserves_typing x v e τ σ Γ :
      (x : σ ; Γ) ⊢ e : τ →
      ∅ ⊢ v : σ →
      Γ ⊢ subst x v e : τ.
    Proof.
      revert x v σ τ Γ. induction e; inversion 1; subst; intros;
        try solve [simpl; eauto]; simpl; bdestruct (x =? s); subst;
        try solve [ rewrite ctx_neq in *; eauto
                  | rewrite ctx_shadow in *; eauto
                  | rewrite ctx_permute in *; eauto ].
      - apply ctx_eq_inv in H2; subst.
        by apply weakening_empty.
      - bdestruct (s =? s0); subst.
        + rewrite ctx_shadow in *; eauto.
        + rewrite ctx_shadow, ctx_permute in *; eauto.
      - bdestruct (x =? s0); subst.
        + rewrite ctx_shadow, ctx_permute in *; eauto.
        + rewrite ctx_permute in *; eauto.
    Qed.
  End Subst.

End Lemmas.



(** ** Soundness *)
Section Soundness.
  
  (** Progress Theorem *)
  Theorem progress e τ :
    ∅ ⊢ e : τ →
    value e ∨ (∃ e', e ↝ e').
  Proof.
    remember ∅ as Γ. induction 1; eauto; intuition; try naive_solver;
      try solve [ apply bool_canonical in H as [[] ->]; naive_solver
                | apply prod_canonical in H; naive_solver
                | apply sum_canonical in H; naive_solver ].
    - right; intuition; try naive_solver.
      apply arrow_canonical in H as (x & e & ->); eauto.
    - destruct bop0, τ1, τ2; cbn in *; try naive_solver;
      first [ apply int_canonical in H, H0
            | apply bool_canonical in H, H0 ]; naive_solver.
    - destruct uop0, τ; cbn in *; try naive_solver; 
      first [ apply int_canonical in H
            | apply bool_canonical in H ]; naive_solver.
  Qed.
  
  (** Preservation Theorem *)
  Theorem preservation e e' τ :
    ∅ ⊢ e : τ →
    e ↝ e' →
    ∅ ⊢ e' : τ.
  Proof.
    remember ∅ as Γ. intro H. revert e'.
    induction H; intuition; try solve_by_inverts 2.
    - inversion H3; subst; eauto.
      eapply substitution_preserves_typing; solve_by_invert.
    - inversion H4; subst; eauto.
      destruct bop0, τ1, τ2; cbn in *; 
      first [ apply int_canonical in H, H0
            | apply bool_canonical in H, H0
            | idtac ]; naive_solver.
    - inversion H2; subst; eauto.
      destruct uop0, τ; cbn in *;
      first [ apply int_canonical in H
            | apply bool_canonical in H
            | idtac ]; naive_solver.
    - inversion H2; subst; eauto.
      eapply substitution_preserves_typing; solve_by_invert.
    - inversion H3; subst; eauto;
      eapply substitution_preserves_typing; solve_by_invert.
  Qed.
  
  Notation "e1 '↝*' e2" := (rtc reduction e1%E e2%E) (at level 40).
  
  Corollary soundness e e' τ :
    ∅ ⊢ e : τ →
    e ↝* e' →
    ¬ stuck e'.
  Proof.
    intros Hty Hrtc. induction Hrtc as [e|e e' e'' Hred Hrtc IH].
    - apply progress in Hty as [Hv|[e' Hred]]; intros []; eauto.
    - eauto using preservation.
  Qed.
End Soundness.

End STLCArith.