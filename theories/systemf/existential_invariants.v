From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export debruijn.
From semantics.systemf Require Import lang notation parallel_subst types bigstep tactics.
From semantics.systemf Require logrel binary_logrel.
From Equations Require Import Equations.

(** * Existential types and invariants *)
Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
  (e : expr)
  (A : type).

(** Here, we take the approach of encoding [assert],
  instead of adding it as a primitive to the language.
  This saves us from adding it to all of the existing proofs.
  But clearly it has the same reduction behavior.
 *)

Definition assert (e : expr) : expr :=
  if: e then #LitUnit else (#0 #0).
Lemma assert_true : rtc contextual_step (assert #true) #().
Proof.
  econstructor.
  { eapply base_contextual_step. constructor. }
  constructor.
Qed.
Lemma assert_false : rtc contextual_step (assert #false) (#0 #0).
Proof.
  econstructor. { eapply base_contextual_step. econstructor. }
  constructor.
Qed.

Definition Or (e1 e2 : expr) : expr :=
  if: e1 then #true else e2.
Definition And (e1 e2 : expr) : expr :=
  if: e1 then e2 else #false.
Notation "e1 '||' e2" := (Or e1 e2) : expr_scope.
Notation "e1 '&&' e2" := (And e1 e2) : expr_scope.

(** *** BIT *)
(* ∃ α, { bit : α, flip : α → α, get : α → bool } *)
Definition BIT : type := ∃: (#0 × (#0 → #0)) × (#0 → Bool).

Definition MyBit : val :=
  pack (#0,                  (* bit *)
        λ: "x", #1 - "x",    (* flip *)
        λ: "x", #0 < "x").   (* get *)

Lemma MyBit_typed n Γ :
  TY n; Γ ⊢ MyBit : BIT.
Proof. eapply (typed_pack _ _ _ Int); solve_typing. Qed.

Definition MyBit_instrumented : val :=
  pack (#0,                                                     (* bit *)
        λ: "x", assert (("x" = #0) || ("x" = #1));; #1 - "x",   (* flip *)
        λ: "x", assert (("x" = #0) || ("x" = #1));; #0 < "x").  (* get *)

Definition MyBoolBit : val :=
  pack (#false,                  (* bit *)
        λ: "x", UnOp NegOp "x",    (* flip *)
        λ: "x", "x").   (* get *)

Lemma MyBoolBit_typed n Γ :
  TY n; Γ ⊢ MyBoolBit : BIT.
Proof.
  eapply (typed_pack _ _ _ Bool); solve_typing.
  simpl. econstructor.
Qed.



Section unary_mybit.
  Import logrel.

  Lemma MyBit_instrumented_sem_typed δ :
    𝒱 BIT δ MyBit_instrumented.
  Proof.
    unfold BIT. simp type_interp.
    eexists. split; first done.
    pose_sem_type (λ x, x = #0 ∨ x = #1) as τ.
    { intros v [-> | ->]; done. }
    exists τ.
    simp type_interp.
    eexists _, _. split; first done.
    split.
    - simp type_interp. eexists _, _. split; first done. split.
      + simp type_interp. simpl. by left.
      + simp type_interp. eexists _, _. split; first done. split; first done.
        intros v'. simp type_interp; simpl.
        (* Note: this part of the proof is a bit different from the paper version, as we directly do a case split. *)
        intros [-> | ->].
        * exists #1. split; last simp type_interp; simpl; eauto.
          bs_steps_det. eapply bs_if_true; bs_steps_det.
          eapply bs_if_true; bs_steps_det.
        * exists #0. split; last simp type_interp; simpl; eauto.
          bs_steps_det. eapply bs_if_true; bs_steps_det.
          eapply bs_if_false; bs_steps_det.
    - simp type_interp. eexists _, _. split; first done. split; first done.
      intros v'. simp type_interp; simpl. intros [-> | ->].
      * exists #false. split; last simp type_interp; simpl; eauto.
        bs_steps_det. eapply bs_if_true; bs_steps_det. eapply bs_if_true; bs_steps_det.
      * exists #true. split; last simp type_interp; simpl; eauto.
        bs_steps_det. eapply bs_if_true; bs_steps_det. eapply bs_if_false; bs_steps_det.
  Qed.

End unary_mybit.


Section binary_mybit.
  Import binary_logrel.

  Lemma MyBit_MyBoolBit_sem_typed δ :
    𝒱 BIT δ MyBit MyBoolBit.
  Proof.
    unfold BIT. simp type_interp.
    eexists _, _. split_and!; try done.
    pose_sem_type (λ v w, (v = #0 ∧ w = #false) ∨ (v = #1 ∧ w = #true)) as τ.
    { intros v w [[-> ->] | [-> ->]]; done. }
    exists τ.
    simp type_interp.
    eexists _, _, _, _. split_and!; try done.
    simp type_interp.
    eexists _, _, _, _. split_and!; try done.
    - simp type_interp. simpl. naive_solver.
    - simp type_interp. eexists _, _, _, _. split_and!; try done.
      intros v w. simp type_interp. simpl.
      intros [[-> ->]|[-> ->]]; simpl; eexists _, _; split_and!; eauto; simpl.
      all: simp type_interp; simpl; naive_solver.
    - simp type_interp. eexists _, _, _, _. split_and!; try done.
      intros v w. simp type_interp. simpl.
      intros [[-> ->]|[-> ->]]; simpl.
      all: eexists _, _; split_and!; eauto; simpl.
      all: simp type_interp; eauto.
  Qed.

End binary_mybit.