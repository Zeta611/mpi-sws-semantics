From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export debruijn.
From semantics.systemf Require Import lang notation types bigstep tactics.

(** * Church encodings *)
Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
  (e : expr)
  (A : type).

Definition empty_type : type := ∀: #0.

(** *** Unit *)
Definition unit_type : type := ∀: #0 → #0.
Definition unit_inh : val := Λ, λ: "x", "x".

Lemma unit_wf n : type_wf n unit_type.
Proof. solve_typing. Qed.
Lemma unit_inh_typed n Γ : TY n; Γ ⊢ unit_inh : unit_type.
Proof. solve_typing. Qed.

(** *** Bool *)
Definition bool_type : type := ∀: #0 → #0 → #0.
Definition bool_true : val := Λ, λ: "t" "f", "t".
Definition bool_false : val := Λ, λ: "t" "f", "f".
Definition bool_if e e1 e2 : expr := (e <> (λ: <>, e1)%E (λ: <>, e2)%E) unit_inh.

Lemma bool_true_typed n Γ : TY n; Γ ⊢ bool_true : bool_type.
Proof. solve_typing. Qed.
Lemma bool_false_typed n Γ: TY n; Γ ⊢ bool_false : bool_type.
Proof. solve_typing. Qed.

Lemma bool_if_typed n Γ e e1 e2 A :
  type_wf n A →
  TY n; Γ ⊢ e1 : A →
  TY n; Γ ⊢ e2 : A →
  TY n; Γ ⊢ e : bool_type →
  TY n; Γ ⊢ bool_if e e1 e2 : A.
Proof.
  intros. solve_typing.
  apply unit_wf.
  all: solve_typing.
Qed.

Lemma bool_if_true_red e1 e2 v :
  is_closed [] e1 →
  big_step e1 v →
  big_step (bool_if bool_true e1 e2)%E v.
Proof.
  intros. bs_step_det.
Qed.

Lemma bool_if_false_red e1 e2 v :
  is_closed [] e2 →
  big_step e2 v →
  big_step (bool_if bool_false e1 e2)%E v.
Proof.
  intros. bs_step_det.
Qed.

(** *** Product types *)
(* Using De Bruijn indices, we need to be a bit careful:
   The binder introduced by [∀:] should not be visible in [A] and [B].
   Therefore, we need to shift [A] and [B] up by one, using the renaming substitution [ren].
 *)
Definition product_type (A B : type) : type := ∀: (A.[ren (+1)] → B.[ren (+1)] → #0) → #0.
Definition pair_val (v1 v2 : val) : val := Λ, λ: "p", "p" v1 v2.
Definition pair_expr (e1 e2 : expr) : expr :=
  let: "x2" := e2 in
  let: "x1" := e1 in
  Λ, λ: "p", "p" "x1" "x2".
Definition proj1_expr (e : expr) : expr := e <> (λ: "x" "y", "x")%E.
Definition proj2_expr (e : expr) : expr := e <> (λ: "x" "y", "y")%E.

Lemma proj1_red v1 v2 :
  is_closed [] v1 →
  is_closed [] v2 →
  big_step (proj1_expr (pair_val v1 v2)) v1.
Proof.
  intros. bs_step_det.
  rewrite subst_is_closed_nil; last done.
  bs_step_det.
Qed.
Lemma proj2_red v1 v2 :
  is_closed [] v1 →
  is_closed [] v2 →
  big_step (proj2_expr (pair_val v1 v2)) v2.
Proof.
  intros. bs_steps_det.
Qed.

Lemma pair_red e1 e2 v1 v2 :
  is_closed [] v2 →
  is_closed [] e1 →
  big_step e1 v1 →
  big_step e2 v2 →
  big_step (pair_expr e1 e2) (pair_val v1 v2).
Proof.
  intros. bs_steps_det.
Qed.

Lemma proj1_typed n Γ e A B :
  type_wf n A →
  type_wf n B →
  TY n; Γ ⊢ e : product_type A B →
  TY n; Γ ⊢ proj1_expr e : A.
Proof.
  intros. solve_typing.
Qed.

Lemma proj2_typed n Γ e A B :
  type_wf n A →
  type_wf n B →
  TY n; Γ ⊢ e : product_type A B →
  TY n; Γ ⊢ proj2_expr e : B.
Proof.
  intros. solve_typing.
Qed.

(** We need to assume that x2 is not bound by Γ.
  This is a bit annoying, as it puts a restriction on the context in which this typing rule
  can be used.
  Alternatively, we could parameterize the encoding of [pair_expr] by a name to use,
    so that we can always choose a name for it that does not conflict with Γ.
*)
Lemma pair_expr_typed n Γ e1 e2 A B :
  Γ !! "x2" = None →
  type_wf n A →
  type_wf n B →
  TY n; Γ ⊢ e1 : A →
  TY n; Γ ⊢ e2 : B →
  TY n; Γ ⊢ pair_expr e1 e2 : product_type A B.
Proof.
  intros.
  solve_typing.
  eapply typed_weakening; [done | | lia]. apply insert_subseteq. done.
Qed.


(** *** Church numerals *)
Definition nat_type : type := ∀: #0 → (#0 → #0) → #0.
Definition zero_val : val := Λ, λ: "z" "s", "z".
Definition num_val (n : nat) : val := Λ, λ: "z" "s", Nat.iter n (App "s") "z".
Definition succ_val : val := λ: "n", Λ, λ: "z" "s", "s" ("n" <> "z" "s").
Definition iter_val : val := λ: "n" "z" "s", "n" <> "z" "s".

Lemma zero_typed Γ n : TY n; Γ ⊢ zero_val : nat_type.
Proof. solve_typing. Qed.

Lemma num_typed Γ n m : TY n; Γ ⊢ num_val m : nat_type.
Proof.
  solve_typing.
  induction m as [ | m IH]; simpl.
  - solve_typing.
  - solve_typing.
Qed.

Lemma succ_typed Γ n :
  TY n; Γ ⊢ succ_val : (nat_type → nat_type).
Proof.
  solve_typing.
Qed.

Lemma iter_typed n Γ C :
  type_wf n C →
  TY n; Γ ⊢ iter_val : (nat_type → C → (C → C) → C).
Proof.
  intros. solve_typing.
Qed.
