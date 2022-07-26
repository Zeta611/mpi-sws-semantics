From iris Require Import prelude.
From semantics.ts.systemf_mu_state Require Import lang notation parallel_subst tactics execution.

(** * Exercise Sheet 7 *)

(** Exercise 1: Stack (LN Exercise 45) *)
(* We use lists to model our stack *)
Section lists.
  Context (A : type).
  Definition list_type : type :=
    μ: Unit + (A.[ren (+1)] × #0).

  Definition nil_val : val :=
    RollV (InjLV (LitV LitUnit)).
  Definition cons_val (v : val) (xs : val) : val :=
    RollV (InjRV (v, xs)).
  Definition cons_expr (v : expr) (xs : expr) : expr :=
    roll (InjR (v, xs)).

  Definition list_case : val :=
    Λ, λ: "l" "n" "hf", match: unroll "l" with InjL <> => "n" | InjR "h" => "hf" (Fst "h") (Snd "h") end.

  Lemma nil_val_typed Σ n Γ :
    type_wf n A →
    TY Σ; n; Γ ⊢ nil_val : list_type.
  Proof.
    intros. solve_typing.
  Qed.

  Lemma cons_val_typed Σ n Γ (v xs : val) :
    type_wf n A →
    TY Σ; n; Γ ⊢ v : A →
    TY Σ; n; Γ ⊢ xs : list_type →
    TY Σ; n; Γ ⊢ cons_val v xs : list_type.
  Proof.
    intros. simpl. solve_typing.
  Qed.

  Lemma cons_expr_typed Σ n Γ (x xs : expr) :
    type_wf n A →
    TY Σ; n; Γ ⊢ x : A →
    TY Σ; n; Γ ⊢ xs : list_type →
    TY Σ; n; Γ ⊢ cons_expr x xs : list_type.
  Proof.
    intros. simpl. solve_typing.
  Qed.

  Lemma list_case_typed Σ n Γ :
    type_wf n A →
    TY Σ; n; Γ ⊢ list_case : (∀: list_type.[ren (+1)] → #0 → (A.[ren(+1)] → list_type.[ren (+1)] → #0) → #0).
  Proof.
    intros. simpl. solve_typing.
  Qed.
End lists.

(* The stack interface *)
Definition stack_t A : type :=
  ∃: ((Unit → #0)       (* new *)
    × (#0 → A.[ren (+1)] → Unit)   (* push *)
    × (#0 → Unit + A.[ren (+1)]))  (* pop *)
  .

(** We assume an abstract implementation of lists (an example implementation is provided above) *)
Definition list_t (A : type) : type :=
  ∃: (#0 (* mynil *)
    × (A.[ren (+1)] → #0 → #0) (* mycons *)
    × (∀: #1 → #0 → (A.[ren (+2)] → #1 → #0) → #0)) (* mylistcase *)
  .

Definition mystack : val :=
  (* define your stack implementation, assuming "lc" is a list implementation *)
  λ: "lc",
  #0 (* FIXME *).

Definition make_mystack : val :=
  Λ, λ: "lc",
    unpack "lc" as "lc" in
    #0 (* FIXME *).

Lemma make_mystack_typed Σ n Γ :
  TY Σ; n; Γ ⊢ make_mystack : (∀: list_t #0 → stack_t #0).
Proof.
  repeat solve_typing_fast.
  (* FIXME *)
Admitted.
(*Qed.*)


(** Exercise 2 (LN Exercise 46): Obfuscated code *)
Definition obf_expr : expr :=
  let: "x" := new (λ: "x", "x" + "x") in
  let: "f" := (λ: "g", let: "f" := !"x" in "x" <- "g";; "f" #11) in
  "f" (λ: "x", "f" (λ: <>, "x")) + "f" (λ: "x", "x" + #9).

(* The following contextual lifting lemma will be helpful *)
Lemma rtc_contextual_step_fill K e e' h h' :
  rtc contextual_step (e, h) (e', h') →
  rtc contextual_step (fill K e, h) (fill K e', h').
Proof.
  remember (e, h) as a eqn:Heqa. remember (e', h') as b eqn:Heqb.
  induction 1 as [ | ? c ? Hstep ? IH] in e', h', e, h, Heqa, Heqb |-*; subst.
  - simplify_eq. done.
  - destruct c as (e1, h1).
    econstructor 2.
    + apply fill_contextual_step. apply Hstep.
    + apply IH; done.
Qed.

(* You may use the [new_fresh] and [init_heap_singleton] lemmas to allocate locations *)

Lemma obf_expr_eval :
  ∃ h', rtc contextual_step (obf_expr, ∅) (of_val #0 (* FIXME: what is the result? *), h').
Proof.
  eexists. unfold obf_expr.
  (*FIXME *)
Admitted.
(*Qed.*)

(** Exercise 3 (LN Exercise 47): Diverging term *)

Definition diverge : val :=
  #0. (* FIXME *)
Lemma diverge_typed Σ n Γ :
  TY Σ; n; Γ ⊢ diverge : (Int → Int).
Proof.
  repeat solve_typing_fast.
  (* FIXME *)
Admitted.
(*Qed.*)


(** Exercise 4 (LN Exercise 48): Fibonacci *)
Definition fibonacci : val :=
  #0 (* FIXME *)
.
Lemma fibonacci_typed Σ n Γ :
  TY Σ; n; Γ ⊢ fibonacci : (Int → Int).
Proof.
  repeat solve_typing_fast.
  (*FIXME *)
Admitted.
(*Qed.*)


(** Exercise 5 (LN Exercise 49): Counter with Reset *)

Definition make_counter : val :=
  #0 (* FIXME *)
.

Lemma make_counter_typed Σ n Γ :
  TY Σ; n; Γ ⊢ make_counter : (Unit → (Unit → Int) × (Unit → Unit)).
Proof.
  repeat solve_typing_fast.
  (* FIXME *)
Admitted.
(*Qed.*)
