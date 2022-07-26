From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf Require Import lang notation types tactics.

(** Exercise 3 (LN Exercise 22): Universal Fun *)

Definition fun_comp : val :=
  #0 (* FIXME *).
Definition fun_comp_type : type :=
  Int (* FIXME *).
Lemma fun_comp_typed :
  TY 0; ∅ ⊢ fun_comp : fun_comp_type.
Proof. solve_typing. Qed.

Definition swap_args : val :=
  #0 (* FIXME *).
Definition swap_args_type : type :=
  Int (* FIXME *).
Lemma swap_args_typed :
  TY 0; ∅ ⊢ swap_args : swap_args_type.
Proof. solve_typing. Qed.

Definition lift_prod : val :=
  #0 (* FIXME *).
Definition lift_prod_type : type :=
  Int (* FIXME *).
Lemma lift_prod_typed :
  TY 0; ∅ ⊢ lift_prod : lift_prod_type.
Proof. solve_typing. Qed.

Definition lift_sum : val :=
  #0 (* FIXME *).
Definition lift_sum_type : type :=
  Int (* FIXME *).
Lemma lift_sum_typed :
  TY 0; ∅ ⊢ lift_sum : lift_sum_type.
Proof. solve_typing. Qed.

(** Exercise 5 (LN Exercise 18): Named to De Bruijn *)
Inductive ptype : Type :=
  | PTVar : string → ptype
  | PInt
  | PBool
  | PTForall : string → ptype → ptype
  | PTExists : string → ptype → ptype
  | PFun (A B : ptype).

Declare Scope PType_scope.
Delimit Scope PType_scope with pty.
Bind Scope PType_scope with ptype.
Coercion PTVar: string >-> ptype.
Infix "→" := PFun : PType_scope.
Notation "∀:  x , τ" :=
    (PTForall x τ%pty)
    (at level 100, τ at level 200) : PType_scope.
Notation "∃:  x , τ" :=
    (PTExists x τ%pty)
    (at level 100, τ at level 200) : PType_scope.

Fixpoint debruijn (m: gmap string nat) (A: ptype) : option type :=
  None (* FIXME *).

(* Example *)
Goal debruijn ∅ (∀: "x", ∀: "y", "x" → "y")%pty = Some (∀: ∀: #1 → #0)%ty.
Proof.
  (*reflexivity.*)
(*Qed.*)
Admitted.

Goal debruijn ∅ (∀: "x", "x" → ∀: "y", "y")%pty = Some (∀: #0 → ∀: #0)%ty.
Proof.
  (*reflexivity.*)
(*Qed.*)
Admitted.

Goal debruijn ∅ (∀: "x", "x" → ∀: "y", "x")%pty = Some (∀: #0 → ∀: #1)%ty.
Proof.
  (*reflexivity.*)
(*Qed.*)
Admitted.

(** Exercise 7 (LN Exercise 19): De Bruijn Terms *)
Module dbterm.
  (** Your type of expressions only needs to encompass the operations of our base lambda calculus. *)
  Inductive expr :=
    | Lit (l : base_lit)
    | Var (n : nat)
    | Lam (e : expr)
    | Plus (e1 e2 : expr)
    | App (e1 e2 : expr)
  .

  (** Formalize substitutions and renamings as functions. *)
  Definition subt := nat → expr.
  Definition rent := nat → nat.

  Implicit Types
    (σ : subt)
    (δ : rent)
    (n x : nat)
    (e : expr).

  Fixpoint subst σ e :=
    (* FIXME *) e.

  Compute (subst
    (λ n, match n with
          | 0 => Lit (LitInt 42)
          | 1 => Var 0
          | _ => Var n
          end)
    (Lam (Plus (Plus (Var 2) (Var 1)) (Var 0)))).
  (*FIXME: should produce [Lam (Plus (Plus (Var 1) (Lit 42%Z)) (Var 0))] *)

End dbterm.
