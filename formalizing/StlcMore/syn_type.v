From Formalizing.StlcMore Require Import steps.
From Intro2TT Require Import Tactics.

(** ** Type system for the STLC language. *)
(** This file defines the type system for the STLC language, including the rules for
  * typing expressions, lambda abstractions, applications, and operations on products
  * and sums. *)

Inductive ty : Type :=
  | TInt : ty
  | TBool : ty
  | TString : ty
  | TUnit : ty
  | TFun : ty → ty → ty
  | TProd : ty → ty → ty
  | TSum : ty → ty → ty
  .

Definition typing_context := gmap string ty.
Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr).

Declare Scope typing_scope.
Delimit Scope typing_scope with T.
Bind Scope typing_scope with ty.
Infix "→" := TFun : typing_scope.
Notation "(→)" := TFun (only parsing) : typing_scope.
Infix "×" := TProd (at level 70) : typing_scope.
Notation "(×)" := TProd (only parsing) : typing_scope.
Infix "+" := TSum : typing_scope.
Notation "(+)" := TSum (only parsing) : typing_scope.

Reserved Notation "Γ ⊢ e : A" (at level 74, e, A at next level).

Definition type_of_lit (l : base_lit) : ty :=
  match l with
  | LitBool b => TBool
  | LitInt n => TInt
  | LitString s => TString
  | LitUnit => TUnit
  end.
Definition un_op_type (op : un_op) (A : ty) : option ty :=
  match op, A with
  | NegOp, TBool => Some TBool
  | MinusUnOp, TInt => Some TInt
  | LenOp, TString => Some TInt
  | _,_ => None
  end.
Definition bin_op_type (op : bin_op) (A B : ty) : option ty :=
  match op, A, B with
  | PlusOp, TInt, TInt => Some TInt
  | MinusOp, TInt, TInt => Some TInt
  | MultOp, TInt, TInt => Some TInt
  | LtOp, TInt, TInt => Some TBool
  | LeOp, TInt, TInt => Some TBool
  | EqOp, TInt, TInt => Some TBool
  | AndOp, TBool, TBool => Some TBool
  | OrOp, TBool, TBool => Some TBool
  | ConcatOp, TString, TString => Some TString
  | StrEqOp, TString, TString => Some TBool
  | PrefixOp, TString, TString => Some TBool
  | _, _, _ => None
  end.
(* Typing rules for the STLC language *)
Inductive syn_typed : typing_context → expr → ty → Prop :=
  | typed_lit Γ l :
      Γ ⊢ Lit l : type_of_lit l
  | typed_var Γ x A :
      Γ !! x = Some A →
      Γ ⊢ Var x : A
  | typed_lam Γ x e A B :
      (<[x := A]> Γ) ⊢ e : B →
      Γ ⊢ Lam (BNamed x) e : (A → B)
  | typed_lam_anon Γ e A B :
      Γ ⊢ e : B →
      Γ ⊢ Lam BAnon e : (A → B)
  | typed_app Γ e1 e2 A B :
      Γ ⊢ e1 : (A → B) →
      Γ ⊢ e2 : A →
      Γ ⊢ App e1 e2 : B
  | typed_unop Γ op e A B :
      Γ ⊢ e : A →
      un_op_type op A = Some B →
      Γ ⊢ UnOp op e : B
  | typed_binop Γ op e1 e2 A B C :
      Γ ⊢ e1 : A →
      Γ ⊢ e2 : B →
      bin_op_type op A B = Some C →
      Γ ⊢ BinOp op e1 e2 : C
  | typed_if Γ e0 e1 e2 A :
      Γ ⊢ e0 : TBool →
      Γ ⊢ e1 : A →
      Γ ⊢ e2 : A →
      Γ ⊢ If e0 e1 e2 : A
  | typed_pair Γ e1 e2 A B :
      Γ ⊢ e1 : A →
      Γ ⊢ e2 : B →
      Γ ⊢ (e1, e2) : (A × B)
  | typed_fst Γ e A B :
      Γ ⊢ e : (A × B) →
      Γ ⊢ Fst e : A
  | typed_snd Γ e A B :
      Γ ⊢ e : (A × B) →
      Γ ⊢ Snd e : B
  | typed_injl Γ e A B :
      Γ ⊢ e : A →
      Γ ⊢ InjL e : (A + B)
  | typed_injr Γ e A B :
      Γ ⊢ e : B →
      Γ ⊢ InjR e : (A + B)
  | typed_case Γ e0 e1 e2 A B C :
      Γ ⊢ e0 : (A + B) →
      Γ ⊢ e1 : (A → C) →
      Γ ⊢ e2 : (B → C) →
      Γ ⊢ Case e0 e1 e2 : C
  where "Γ ⊢ e : A" := (syn_typed Γ e%E A%T).
#[export] Hint Constructors syn_typed : core.

Notation Int := TInt.
Notation Bool := TBool.
Notation String := TString.
Notation Unit := TUnit.

(** Examples *)
Goal ∅ ⊢ (λ: "x", "x")%E : (Int → Int).
Proof. eauto. Qed.

Goal ∅ ⊢ (λ: "x", Lit (LitInt 42))%E : (Int → Int).
Proof. eauto. Qed.


(** Lemmas representing typing properties *)
Lemma syn_typed_closed Γ e A X :
  Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  induction 1 in X |-*; simpl; intro Hx; try done.
  { by apply bool_decide_pack, Hx, elem_of_dom. }
  { apply IHsyn_typed. intros y Hlookup%elem_of_dom%lookup_insert_is_Some.
    destruct Hlookup as [->|[? Hy]]; apply elem_of_cons; eauto. right.
    by apply Hx, elem_of_dom. }
  { naive_solver. }
  all: repeat match goal with | |- Is_true (_ && _) => apply andb_True; split end.
  all: try naive_solver.
Qed.

Lemma typed_weakening Γ Δ e A:
  Γ ⊢ e : A →
  Γ ⊆ Δ →
  Δ ⊢ e : A.
Proof.
  induction 1 in Δ |-*; simpl; intros HΓΔ; eauto.
  - econstructor. by eapply lookup_weaken.
  - econstructor. eapply IHsyn_typed. by apply insert_mono.
Qed.

#[export] Hint Resolve syn_typed_closed typed_weakening : core.

(** Typing inversion lemmas *)
Lemma lit_inversion Γ l A: Γ ⊢ Lit l : A → A = type_of_lit l.
Proof. inversion 1; subst; auto. Qed.

Lemma var_inversion Γ (x: string) A: Γ ⊢ x : A → Γ !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Γ (x: string) e C:
  Γ ⊢ (λ: x, e) : C →
  ∃ A B, C = (A → B)%T ∧ <[x:=A]> Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lam_anon_inversion Γ e C:
  Γ ⊢ (λ: <>, e) : C →
  ∃ A B, C = (A → B)%T ∧ Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma app_inversion Γ e1 e2 B:
  Γ ⊢ e1 e2 : B →
  ∃ A, Γ ⊢ e1 : (A → B) ∧ Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma un_op_inversion Γ op e T:
  Γ ⊢ UnOp op e : T →
  match op with
  | NegOp => T = Bool ∧ Γ ⊢ e : Bool
  | MinusUnOp => T = TInt ∧ Γ ⊢ e : TInt
  | LenOp => T = TInt ∧ Γ ⊢ e : String
  end.
Proof.
  inversion 1; subst. destruct op, A; simpl in *; simplify_option_eq; eauto.
Qed.

Lemma bin_op_inversion Γ op e1 e2 T:
  Γ ⊢ (BinOp op e1 e2) : T →
  match op with
  | PlusOp | MinusOp | MultOp => T = Int ∧ 
                                  Γ ⊢ e1 : Int ∧ Γ ⊢ e2 : Int
  | LtOp | LeOp | EqOp => T = Bool ∧ 
                                  Γ ⊢ e1 : Int ∧ Γ ⊢ e2 : Int
  | AndOp | OrOp => T = Bool ∧ 
                                  Γ ⊢ e1 : Bool ∧ Γ ⊢ e2 : Bool
  | ConcatOp => T = String ∧ 
                                  Γ ⊢ e1 : String ∧ Γ ⊢ e2 : String
  | StrEqOp | PrefixOp => T = Bool ∧ 
                                  Γ ⊢ e1 : String ∧ Γ ⊢ e2 : String
  end.
Proof.
  inversion 1; subst. destruct op, A, B; simpl in *; simplify_option_eq; eauto.
Qed.

Lemma if_inversion Γ e0 e1 e2 A:
  Γ ⊢ If e0 e1 e2 : A →
  Γ ⊢ e0 : Bool ∧ Γ ⊢ e1 : A ∧ Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma pair_inversion Γ e1 e2 C:
  Γ ⊢ (e1, e2) : C →
  ∃ A B, C = (A × B)%T ∧ Γ ⊢ e1 : A ∧ Γ ⊢ e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma fst_inversion Γ e A:
  Γ ⊢ Fst e : A →
  ∃ B, Γ ⊢ e : (A × B)%T.
Proof. inversion 1; subst; eauto. Qed.

Lemma snd_inversion Γ e B:
  Γ ⊢ Snd e : B →
  ∃ A, Γ ⊢ e : (A × B)%T.
Proof. inversion 1; subst; eauto. Qed.

Lemma injL_inversion Γ e C:
  Γ ⊢ InjL e : C →
  ∃ A B, C = (A + B)%T ∧ Γ ⊢ e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma injR_inversion Γ e C:
  Γ ⊢ InjR e : C →
  ∃ A B, C = (A + B)%T ∧ Γ ⊢ e : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma case_inversion Γ e0 e1 e2 A:
  Γ ⊢ Case e0 e1 e2 : A →
  ∃ B C, Γ ⊢ e0 : (B + C)%T ∧ Γ ⊢ e1 : (B → A)%T ∧ Γ ⊢ e2 : (C → A)%T.
Proof. inversion 1; subst; eauto. Qed.

(** Canonical values *)
Lemma canonical_values_arr Γ e A B:
  Γ ⊢ e : (A → B) →
  is_val e →
  ∃ x e', e = (λ: x, e')%E.
Proof.
  inversion 1; simpl in *; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.

Lemma canonical_values_int Γ e:
  Γ ⊢ e : Int →
  is_val e →
  ∃ n: Z, e = (#n)%E.
Proof.
  inversion 1; simpl in *; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.

Lemma canonical_values_bool Γ e:
  Γ ⊢ e : Bool →
  is_val e →
  ∃ b: bool, e = (Lit (LitBool b))%E.
Proof.
  inversion 1; simpl in *; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.

Lemma canonical_values_string Γ e:
  Γ ⊢ e : String →
  is_val e →
  ∃ s: string, e = (Lit (LitString s))%E.
Proof.
  inversion 1; simpl in *; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.

Lemma canonical_values_unit Γ e:
  Γ ⊢ e : Unit →
  is_val e →
  e = (Lit LitUnit)%E.
Proof.
  inversion 1; simpl in *; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.

Lemma canonical_values_prod Γ e A B:
  Γ ⊢ e : (A × B) →
  is_val e →
  ∃ e1 e2, e = (e1, e2)%E ∧ is_val e1 ∧ is_val e2.
Proof.
  inversion 1; simpl; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.

Lemma canonical_values_sum Γ e A B:
  Γ ⊢ e : (A + B) →
  is_val e →
  ∃ e', (e = InjL e' ∨ e = InjR e') ∧ is_val e'.
Proof.
  inversion 1; simpl; try naive_solver.
  destruct l; simpl in *; naive_solver.
Qed.