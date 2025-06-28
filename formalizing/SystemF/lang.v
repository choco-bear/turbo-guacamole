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
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit.
Inductive un_op : Set :=
  | NegOp (* Boolean Negation *)
  | MinusUnOp (* Integer Negation *)
  .
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | DivOp | ModOp (* Integer Arithmetics *)
  | LtOp | LeOp | EqOp (* Integer Comparisons *)
  | AndOp | OrOp (* Logical Operators *)
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

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lit l => Some $ LitV l
  | Lam x e' => Some $ LamV x e'
  | TLam e' => Some $ TLamV e'
  | Pack e' => to_val e' ≫= (λ v, Some $ PackV v)
  | Pair e1 e2 =>
      to_val e1 ≫= (λ v1, to_val e2 ≫= (λ v2, Some $ PairV v1 v2))
  | InjL e' => to_val e' ≫= (λ v, Some $ InjLV v)
  | InjR e' => to_val e' ≫= (λ v, Some $ InjRV v)
  | _ => None
  end.