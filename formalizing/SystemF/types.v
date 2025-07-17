Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Formalizing.SystemF Require Import lang notation free_variables tactics.
From Intro2TT Require Import Tactics lib.maps.
From Autosubst Require Export Autosubst.
From stdpp Require Import options.

(** ** Type system for the System F. *)
(** This file defines the type system for the System F language. *)

Inductive ty : Type :=
  (** [var] is the type of variables of Autosubst -- it unfolds to [nat] *)
  | TVar : var → ty
  (** Base types *)
  | Int : ty
  | Bool : ty
  | String : ty
  | Unit : ty
  (** Function, product, and sum types *)
  | Fun : ty → ty → ty
  | Prod : ty → ty → ty
  | Sum : ty → ty → ty
  (** Type constructors for polymorphic types *)
  (** The [{bind 1 of ty}] tells Autosubst to put a De Bruijn binder here *)
  | TForall : {bind 1 of ty} → ty
  | TExists : {bind 1 of ty} → ty
  .

(** Autosubst instances. *)
(** This lets Autosubst do its magic and derive all the substitution functions, etc. *)
#[export] Instance Ids_ty : Ids ty. derive. Defined.
#[export] Instance Rename_ty : Rename ty. derive. Defined.
#[export] Instance Subst_ty : Subst ty. derive. Defined.
#[export] Instance SubstLemmas_typer : SubstLemmas ty. derive. Qed.

Definition typing_context := gmap string ty.
Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr).

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with ty.
Notation "# x" := (TVar x) : FType_scope.
Infix "→" := Fun : FType_scope.
Notation "(→)" := Fun (only parsing) : FType_scope.
Infix "×" := Prod (at level 70) : FType_scope.
Notation "(×)" := Prod (only parsing) : FType_scope.
Infix "+" := Sum : FType_scope.
Notation "(+)" := Sum (only parsing) : FType_scope.
Notation "∀: τ" :=
  (TForall τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%ty)
  (at level 100, τ at level 200) : FType_scope.

(** Shift all the indices in the context by one, used when inserting a new type
  * interpretation in Δ. [<$>] is notation for the [fmap] operation that maps the
  * substitution over the whole map. [ren] is Autosubst's renaming operation -- it
  * renames all type variables according to the given function, in this case [(+1)] to
  * shift the variables up by 1. *)
Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)) <$> Γ) (at level 10, format "⤉ Γ").

Reserved Notation "'TY' n ; Γ ⊢ e : A" (at level 74, e, A at next level).

(** [type_wf n A] states that a type [A] has only free variables up to < [n].
  * (in other words, all variables occurring free are strictly bounded by [n]). *)
Inductive type_wf : nat → ty → Prop :=
  | type_wf_TVar m n:
      m < n →
      type_wf n (TVar m)
  | type_wf_Int n: type_wf n Int
  | type_wf_Bool n : type_wf n Bool
  | type_wf_Unit n : type_wf n Unit
  | type_wf_String n : type_wf n String
  | type_wf_TForall n A :
      type_wf (S n) A →
      type_wf n (TForall A)
  | type_wf_TExists n A :
      type_wf (S n) A →
      type_wf n (TExists A)
  | type_wf_Fun n A B:
      type_wf n A →
      type_wf n B →
      type_wf n (Fun A B)
  | type_wf_Prod n A B :
      type_wf n A →
      type_wf n B →
      type_wf n (Prod A B)
  | type_wf_Sum n A B :
      type_wf n A →
      type_wf n B →
      type_wf n (Sum A B)
.
#[export] Hint Constructors type_wf : core.

Inductive bin_op_typed : bin_op → ty → ty → ty → Prop :=
  | plus_op_typed : 
      bin_op_typed PlusOp Int Int Int
  | minus_op_typed :
      bin_op_typed MinusOp Int Int Int
  | mult_op_typed :
      bin_op_typed MultOp Int Int Int
  | lt_op_typed :
      bin_op_typed LtOp Int Int Bool
  | le_op_typed :
      bin_op_typed LeOp Int Int Bool
  | gt_op_typed :
      bin_op_typed GtOp Int Int Bool
  | ge_op_typed :
      bin_op_typed GeOp Int Int Bool
  | and_op_typed :
      bin_op_typed AndOp Bool Bool Bool
  | or_op_typed :
      bin_op_typed OrOp Bool Bool Bool
  | sub_op_typed :
      bin_op_typed SubOp String String String
  | concat_op_typed :
      bin_op_typed ConcatOp String String String
  | prefix_op_typed :
      bin_op_typed PrefixOp String String Bool
  | substr_op_typed :
      bin_op_typed SubstrOp String String Bool
  | int_eq_op_typed :
      bin_op_typed EqOp Int Int Bool
  | bool_eq_op_typed :
      bin_op_typed EqOp Bool Bool Bool
  | string_eq_op_typed :
      bin_op_typed EqOp String String Bool
  | unit_eq_op_typed :
      bin_op_typed EqOp Unit Unit Bool
  | int_neq_op_typed :
      bin_op_typed NeqOp Int Int Bool
  | bool_neq_op_typed :
      bin_op_typed NeqOp Bool Bool Bool
  | string_neq_op_typed :
      bin_op_typed NeqOp String String Bool
  | unit_neq_op_typed :
      bin_op_typed NeqOp Unit Unit Bool
  .
#[export] Hint Constructors bin_op_typed : core.

Inductive un_op_typed : un_op → ty → ty → Prop :=
  | neg_op_typed :
      un_op_typed NegOp Bool Bool
  | minus_un_op_typed :
      un_op_typed MinusUnOp Int Int
  | len_op_typed :
      un_op_typed LenOp String Int
  .
#[export] Hint Constructors un_op_typed : core.

Inductive has_type : nat → typing_context → expr → ty → Prop :=
  | typed_int n Γ (z : Z) :
      TY n; Γ ⊢ (#z) : Int
  | typed_bool n Γ (b : bool) :
      TY n; Γ ⊢ (#b) : Bool
  | typed_string n Γ (s : string) :
      TY n; Γ ⊢ (#s) : String
  | typed_unit n Γ :
      TY n; Γ ⊢ (#()) : Unit
  | typed_var n Γ x A :
      Γ !! x = Some A →
      TY n; Γ ⊢ (Var x) : A
  | typed_lam n Γ (x : string) e A B :
      TY n; (<[x := A]> Γ) ⊢ e : B →
      type_wf n A →
      TY n; Γ ⊢ (λ: x, e) : (A → B)
  | typed_lam_anon n Γ e A B :
      TY n; Γ ⊢ e : B →
      type_wf n A →
      TY n; Γ ⊢ (λ: <>, e) : (A → B)
  | typed_app n Γ e1 e2 A B :
      TY n; Γ ⊢ e1 : (A → B) →
      TY n; Γ ⊢ e2 : A →
      TY n; Γ ⊢ (e1 e2) : B
  | typed_un_op n Γ op e A B :
      un_op_typed op A B →
      TY n; Γ ⊢ e : A →
      TY n; Γ ⊢ (UnOp op e) : B
  | typed_bin_op n Γ op e1 e2 A B C :
      bin_op_typed op A B C →
      TY n; Γ ⊢ e1 : A →
      TY n; Γ ⊢ e2 : B →
      TY n; Γ ⊢ (BinOp op e1 e2) : C
  | typed_if n Γ e e1 e2 A :
      TY n; Γ ⊢ e : Bool →
      TY n; Γ ⊢ e1 : A →
      TY n; Γ ⊢ e2 : A →
      TY n; Γ ⊢ (If e e1 e2) : A
  | typed_tapp n Γ e A B :
      TY n; Γ ⊢ e : (∀: A) →
      type_wf n B →
      (* A.[B/] is the notation for Autosubst's substitution operation replacing
         variable 0 by [B] *)
      TY n; Γ ⊢ (e <>) : (A.[B/])
  | typed_tlam n Γ e A :
      (* we need to shift the context up as we descend under a binder *)
      TY (S n); (⤉ Γ) ⊢ e : A →
      TY n; Γ ⊢ (Λ, e) : (∀: A)
  | typed_pack n Γ e A B :
      type_wf n B →
      type_wf (S n) A →
      TY n; Γ ⊢ e : (A.[B/]) →
      TY n; Γ ⊢ (Pack e) : (∃: A)
  | typed_unpack n Γ (x : string) e e' A B :
      type_wf n B →
      TY n; Γ ⊢ e : (∃: A) →
      TY (S n); (<[x := A]> (⤉ Γ)) ⊢ e' : (B.[ren (+1)]) →
      TY n; Γ ⊢ (unpack e as x in e') : B
  | typed_unpack_anon n Γ e e' A B :
      type_wf n B →
      TY n; Γ ⊢ e : (∃: A) →
      TY (S n); (⤉ Γ) ⊢ e' : (B.[ren (+1)]) →
      TY n; Γ ⊢ (unpack e as <> in e') : B 
  | typed_pair n Γ e1 e2 A B :
      TY n; Γ ⊢ e1 : A →
      TY n; Γ ⊢ e2 : B →
      TY n; Γ ⊢ (e1, e2) : (A × B)
  | typed_fst n Γ e A B :
      TY n; Γ ⊢ e : (A × B) →
      TY n; Γ ⊢ (Fst e) : A
  | typed_snd n Γ e A B :
      TY n; Γ ⊢ e : (A × B) →
      TY n; Γ ⊢ (Snd e) : B
  | typed_injL n Γ e A B :
      type_wf n B →
      TY n; Γ ⊢ e : A →
      TY n; Γ ⊢ (InjL e) : (A + B)
  | typed_injR n Γ e A B :
      type_wf n A →
      TY n; Γ ⊢ e : B →
      TY n; Γ ⊢ (InjR e) : (A + B)
  | typed_case n Γ e e1 e2 A B C :
      TY n; Γ ⊢ e : (B + C) →
      TY n; Γ ⊢ e1 : (B → A) →
      TY n; Γ ⊢ e2 : (C → A) →
      TY n; Γ ⊢ (Case e e1 e2) : A
  where "'TY' n ; Γ ⊢ e : A" := (has_type n Γ e%E A%ty).
#[export] Hint Constructors has_type : core.

(** Examples *)
Goal TY 0; ∅ ⊢ (λ: "x", #1 + "x")%E : (Int → Int).
Proof. eauto. Qed.
(** [∀: #0 → #0] corresponds to [∀ α. α → α] with named binders. *)
Goal TY 0; ∅ ⊢ (Λ, λ: "x", "x")%E : (∀: #0 → #0).
Proof. eauto 6. Qed.
(** [∃: (#0 → #0) × #0] corresponds to [∃ α. (α → α) × α] with named binders. *)
Goal TY 0; ∅ ⊢ (pack ((λ: "x", "x"), #42)) : ∃: (#0 → #0) × #0.
Proof.
  apply (typed_pack _ _ _ _ Int).
  - eauto.
  - repeat econstructor.
  - (* [asimpl] is Autosubst's tactic for simplifying goals involving type
       substitutions. *)
    asimpl. eauto.
Qed.
Goal TY 0; ∅ ⊢ (unpack (pack ((λ: "x", "x"), #42)) as "y" in (λ: "x", #1337) ((Fst "y") (Snd "y"))) : Int.
Proof.
  (* if we want to typecheck stuff with existentials, we need a bit more explicit
     proofs. Letting eauto try to instantiate the evars becomes too expensive. *)
  apply (typed_unpack _ _ _ _ _ ((#0 → #0) × #0)%ty).
  - done.
  - apply (typed_pack _ _ _ _ Int); asimpl; auto.
  - eapply (typed_app _ _ _ _ (#0)%ty); eauto 6.
Qed.

(** fails: we are not allowed to leak the existential *)
Goal TY 0; ∅ ⊢ (unpack (pack ((λ: "x", "x"), #42)) as "y" in (Fst "y") (Snd "y")) : #0.
Proof.
  apply (typed_unpack _ _ _ _ _ ((#0 → #0) × #0)%ty).
Abort.

(** derived typing rules *)
Lemma typed_match n Γ e e1 e2 x1 x2 A B C :
  type_wf n B →
  type_wf n C →
  TY n; Γ ⊢ e : B + C →
  TY n; <[x1 := B]> Γ ⊢ e1 : A →
  TY n; <[x2 := C]> Γ ⊢ e2 : A →
  TY n; Γ ⊢ match: e with InjL (BNamed x1) => e1 | InjR (BNamed x2) => e2 end : A.
Proof. eauto. Qed.

Lemma typed_tapp' n Γ e A B C :
  TY n; Γ ⊢ e : (∀: A) →
  type_wf n B →
  C = A.[B/] →
  TY n; Γ ⊢ (e <>) : C.
Proof. intros ?? ->. eauto. Qed.

(** If an expression has a type, then it would be a closed one. *)
Lemma has_type_closed n Γ e A X :
  TY n; Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  induction 1 in X |-*; simplify_closed; eauto;
    first [ apply H0, elem_of_dom
          | apply IHhas_type
          | apply IHhas_type2 ]; set_solver.
Qed.
Lemma has_type_free_variables n Γ e A :
  TY n; Γ ⊢ e : A →
  FV e ⊆ dom Γ.
Proof.
  induction 1 in |-*; simpl in *; try set_solver; simplify_sets.
  - done. 
  - apply IHhas_type in H1. simplify_sets.
  - destruct H2 as [H2|[H2 H3]]; [ apply IHhas_type1 in H2
                                 | apply IHhas_type2 in H2 ]; simplify_sets.
Qed.

(** Lemmas about [type_wf] *)
Lemma type_wf_mono n m A :
  type_wf n A → n ≤ m → type_wf m A.
Proof. induction 1 in m |-*; eauto with lia. Qed.

Lemma type_wf_rename n A δ :
  type_wf n A →
  (∀ i j, i < j → δ i < δ j) →
  type_wf (δ n) (rename δ A).
Proof.
  induction 1 in δ |-*; intro MONO; simpl; eauto.
  all: econstructor; eapply type_wf_mono; first eapply IHtype_wf; last done.
  all: intros [|i] [|j] Hlt; simpl; try lia.
  all: specialize MONO with i j; lia.
Qed.
Lemma type_wf_up n A :
  type_wf n A →
  type_wf (S n) A.[ren (+1)].
Proof.
  i. apply type_wf_rename with (δ := S) in H; last lia. by asimpl in H.
Qed.

(** [A.[δ]], i.e. [A] with the substitution [δ] applied to it, is well-formed under
  * [m] if [A] is well-formed under [n] and all the things we substitute up to [n] are
  * well-formed under [m]. *)
Lemma type_wf_subst n m A δ :
  type_wf n A →
  (∀ x, x < n → type_wf m (δ x)) →
  type_wf m A.[δ].
Proof.
  induction 1 in m, δ |-*; ii; try solve [asimpl; eauto].
  all: econstructor; apply IHtype_wf; ii.
  all: destruct x; first (asimpl; eauto with lia).
  all: apply type_wf_rename; simpl; eauto with lia.
Qed.

Lemma type_wf_single_subst n A B :
  type_wf n B →
  type_wf (S n) A →
  type_wf n A.[B/].
Proof.
  intros. eapply type_wf_subst; eauto.
  intros [|x] Hlt; asimpl; eauto with lia.
Qed.


(** We lift [type_wf] to well-formedness of typing contexts *)
Definition ctx_wf n Γ : Prop := ∀ x A, Γ !! x = Some A → type_wf n A.

Lemma ctx_wf_empty n : ctx_wf n ∅.
Proof. by ii. Qed.

Lemma ctx_wf_insert n x Γ A :
  ctx_wf n Γ →
  type_wf n A →
  ctx_wf n (<[x := A]> Γ).
Proof.
  ii. destruct (decide (x = x0)) as [->|ne].
  - by rewrite (lookup_insert Γ) in H1; simplify_option_eq.
  - rewrite (lookup_insert_ne Γ) in H1; eauto.
Qed.

Lemma ctx_wf_up n Γ :
  ctx_wf n Γ → ctx_wf (S n) (⤉ Γ).
Proof.
  ii. erewrite (lookup_fmap (subst _) Γ) in H0.
  apply fmap_Some in H0 as (B & HB & ->).
  apply H in HB. by apply type_wf_up.
Qed.

#[global]
Hint Resolve ctx_wf_empty ctx_wf_insert ctx_wf_up : core.


Lemma has_type_wf n Γ e A :
  ctx_wf n Γ →
  TY n; Γ ⊢ e : A →
  type_wf n A.
Proof.
  induction 2; eauto; intuition; try solve_by_invert.
  apply type_wf_single_subst; eauto.
  eapply type_wf_mono; solve_by_invert.
Qed.

Lemma typed_weakening n m Γ Δ e A :
  TY n; Γ ⊢ e : A →
  Γ ⊆ Δ →
  n ≤ m →
  TY m; Γ ⊢ e : A.
Proof.
  induction 1 in m, Δ |-*; ii; eauto; econstructor;
  try solve [ by eapply type_wf_mono
            | eapply type_wf_mono; eauto with lia
            | eapply IHhas_type; eauto with lia
            | eapply IHhas_type1; eauto with lia
            | eapply IHhas_type2; eauto with lia ].
  by eapply type_wf_mono.
Qed.

Lemma type_subst_eq n A δ τ :
  type_wf n A →
  (∀ m, m < n → δ m = τ m) →
  A.[δ] = A.[τ].
Proof.
  induction 1 in δ, τ |-*; ii; eauto; asimpl; f_equal; eauto;
  apply IHtype_wf; ii; destruct m as [|m]; asimpl; f_equal; apply H0; lia.
Qed.

Lemma type_wf_closed A δ :
  type_wf 0 A →
  A.[δ] = A.
Proof.
  intros. pose proof (type_subst_eq 0 A δ ids).
  asimpl in *. eauto with lia.
Qed.


(** Typing inversion lemmas *)
Lemma int_inversion n Γ l :
  TY n; Γ ⊢ (#l) : Int →
  ∃ z, l = LitInt z.
Proof. i; solve_by_invert. Qed.

Lemma bool_inversion n Γ l :
  TY n; Γ ⊢ (#l) : Bool →
  ∃ b, l = LitBool b.
Proof. i; solve_by_invert. Qed.

Lemma string_inversion n Γ l :
  TY n; Γ ⊢ (#l) : String →
  ∃ s, l = LitString s.
Proof. i; solve_by_invert. Qed.

Lemma unit_inversion n Γ l :
  TY n; Γ ⊢ (#l) : Unit →
  l = LitUnit.
Proof. i; solve_by_invert. Qed.

Lemma lit_inversion n Γ l A :
  TY n; Γ ⊢ (#l) : A →
  (A = Int ∧ ∃ z, l = LitInt z) ∨
  (A = Bool ∧ ∃ b, l = LitBool b) ∨
  (A = String ∧ ∃ s, l = LitString s) ∨
  (A = Unit ∧ l = LitUnit).
Proof. inversion 1; eauto 6. Qed.

Lemma var_inversion n Γ x A :
  TY n; Γ ⊢ (Var x) : A →
  Γ !! x = Some A.
Proof. i; solve_by_invert. Qed.

Lemma lam_inversion n Γ (x : string) e C :
  TY n; Γ ⊢ (λ: x, e) : C →
  ∃ A B, C = (A → B)%ty ∧ type_wf n A ∧
         TY n; (<[x := A]> Γ) ⊢ e : B.
Proof. i; solve_by_invert. Qed.

Lemma lam_anon_inversion n Γ e C :
  TY n; Γ ⊢ (λ: <>, e) : C →
  ∃ A B, C = (A → B)%ty ∧ type_wf n A ∧
         TY n; Γ ⊢ e : B.
Proof. i; solve_by_invert. Qed.

Lemma app_inversion n Γ e1 e2 B :
  TY n; Γ ⊢ (e1 e2) : B →
  ∃ A, TY n; Γ ⊢ e1 : (A → B) ∧
       TY n; Γ ⊢ e2 : A.
Proof. i; solve_by_invert. Qed.

Lemma un_op_inversion n Γ op e B :
  TY n; Γ ⊢ (UnOp op e) : B →
  ∃ A, un_op_typed op A B ∧
       TY n; Γ ⊢ e : A.
Proof. i; solve_by_invert. Qed.

Lemma bin_op_inversion n Γ op e1 e2 C :
  TY n; Γ ⊢ (BinOp op e1 e2) : C →
  ∃ A B, bin_op_typed op A B C ∧
         TY n; Γ ⊢ e1 : A ∧
         TY n; Γ ⊢ e2 : B.
Proof. i; solve_by_invert. Qed.

Lemma if_inversion n Γ e e1 e2 A :
  TY n; Γ ⊢ (If e e1 e2) : A →
  TY n; Γ ⊢ e : Bool ∧
  TY n; Γ ⊢ e1 : A ∧
  TY n; Γ ⊢ e2 : A.
Proof. i; solve_by_invert. Qed.

Lemma tapp_inversion n Γ e B :
  TY n; Γ ⊢ (e <>) : B →
  ∃ A C, B = A.[C/] ∧
         TY n; Γ ⊢ e : (∀: A) ∧
         type_wf n C.
Proof. i; solve_by_invert. Qed.

Lemma tlam_inversion n Γ e B :
  TY n; Γ ⊢ (Λ, e) : B →
  ∃ A, B = (∀: A)%ty ∧
       TY (S n); (⤉ Γ) ⊢ e : A.
Proof. i; solve_by_invert. Qed.

Lemma pack_inversion n Γ e B :
  TY n; Γ ⊢ (pack e) : B →
  ∃ A C, B = (∃: A)%ty ∧
         TY n; Γ ⊢ e : (A.[C/]) ∧
         type_wf n C ∧
         type_wf (S n) A.
Proof. inversion 1; eauto 6. Qed.

Lemma unpack_inversion n Γ (x : string) e e' B :
  TY n; Γ ⊢ (unpack e as x in e') : B →
  ∃ A, type_wf n B ∧
       TY n; Γ ⊢ e : (∃: A) ∧
       TY (S n); (<[x := A]> (⤉ Γ)) ⊢ e' : (B.[ren (+1)]).
Proof. i; solve_by_invert. Qed.

Lemma unpack_anon_inversion n Γ e e' B :
  TY n; Γ ⊢ (unpack e as <> in e') : B →
  ∃ A, type_wf n B ∧
       TY n; Γ ⊢ e : (∃: A) ∧
       TY (S n); (⤉ Γ) ⊢ e' : (B.[ren (+1)]).
Proof. i; solve_by_invert. Qed.

Lemma pair_inversion n Γ e1 e2 C :
  TY n; Γ ⊢ (e1, e2) : C →
  ∃ A B, C = (A × B)%ty ∧
         TY n; Γ ⊢ e1 : A ∧
         TY n; Γ ⊢ e2 : B.
Proof. i; solve_by_invert. Qed.

Lemma fst_inversion n Γ e A :
  TY n; Γ ⊢ (Fst e) : A →
  ∃ B, TY n; Γ ⊢ e : (A × B).
Proof. i; solve_by_invert. Qed.

Lemma snd_inversion n Γ e B :
  TY n; Γ ⊢ (Snd e) : B →
  ∃ A, TY n; Γ ⊢ e : (A × B).
Proof. i; solve_by_invert. Qed.

Lemma injL_inversion n Γ e C :
  TY n; Γ ⊢ (InjL e) : C →
  ∃ A B, C = (A + B)%ty ∧
         type_wf n B ∧
         TY n; Γ ⊢ e : A.
Proof. i; solve_by_invert. Qed.

Lemma injR_inversion n Γ e C :
  TY n; Γ ⊢ (InjR e) : C →
  ∃ A B, C = (A + B)%ty ∧
         type_wf n A ∧
         TY n; Γ ⊢ e : B.
Proof. i; solve_by_invert. Qed.

Lemma case_inversion n Γ e e1 e2 A :
  TY n; Γ ⊢ (Case e e1 e2) : A →
  ∃ B C, TY n; Γ ⊢ e : (B + C) ∧
         TY n; Γ ⊢ e1 : (B → A) ∧
         TY n; Γ ⊢ e2 : (C → A).
Proof. i; solve_by_invert. Qed.

(** Canonical value lemmas *)
Lemma canonical_value_int n Γ e :
  TY n; Γ ⊢ e : Int →
  is_val e →
  ∃ z : Z, e = (#z)%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_bool n Γ e :
  TY n; Γ ⊢ e : Bool →
  is_val e →
  ∃ b : bool, e = (#b)%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_string n Γ e :
  TY n; Γ ⊢ e : String →
  is_val e →
  ∃ s : string, e = (#s)%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_unit n Γ e :
  TY n; Γ ⊢ e : Unit →
  is_val e →
  e = (#())%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_arr n Γ e A B :
  TY n; Γ ⊢ e : (A → B) →
  is_val e →
  ∃ x e', e = (λ: x, e')%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_forall n Γ e A :
  TY n; Γ ⊢ e : (∀: A) →
  is_val e →
  ∃ e', e = (Λ, e')%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_exists n Γ e A :
  TY n; Γ ⊢ e : (∃: A) →
  is_val e →
  ∃ e', e = (pack e')%E.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_prod n Γ e A B :
  TY n; Γ ⊢ e : (A × B) →
  is_val e →
  ∃ e1 e2, e = (e1, e2)%E ∧ is_val e1 ∧ is_val e2.
Proof. inversion 1; naive_solver. Qed.

Lemma canonical_value_sum n Γ e A B :
  TY n; Γ ⊢ e : (A + B) →
  is_val e →
  ∃ e', (e = InjL e' ∨ e = InjR e') ∧ is_val e'.
Proof. inversion 1; naive_solver. Qed.