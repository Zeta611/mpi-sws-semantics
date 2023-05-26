From stdpp Require Import gmap base relations tactics.
From iris Require Import prelude.
From semantics.ts.systemf_mu Require Import lang notation types pure tactics.
From Autosubst Require Import Autosubst.

(** * Encoding of the untyped lambda calculus *)

Definition D := (μ: #0 → #0)%ty.

Definition lame (x : string) (e : expr) : val := RollV (λ: x, e).
Definition appe (e1 e2 : expr) : expr := (unroll e1) e2.

Lemma lame_typed n Γ x e :
  TY n; (<[x := D]> Γ) ⊢ e : D →
  TY n; Γ ⊢ lame x e : D.
Proof. solve_typing. Qed.

Lemma app_typed n Γ e1 e2 :
  TY n; Γ ⊢ e1 : D →
  TY n; Γ ⊢ e2 : D →
  TY n; Γ ⊢ appe e1 e2 : D.
Proof.
  solve_typing.
Qed.

Lemma appe_step_l e1 e1' (v : val) :
  contextual_step e1 e1' →
  contextual_step (appe e1 v) (appe e1' v).
Proof.
  intros Hstep. unfold appe.
  by eapply (fill_contextual_step [UnrollCtx; AppLCtx _]).
Qed.

Lemma appe_step_r e1 e2 e2' :
  contextual_step e2 e2' →
  contextual_step (appe e1 e2) (appe e1 e2').
Proof.
  intros Hstep. unfold appe.
  by eapply (fill_contextual_step [AppRCtx _]).
Qed.

Lemma lame_step_beta x e (v : val) :
  rtc contextual_step (appe (lame x e) v) (lang.subst x v e).
Proof.
  unfold appe, lame.
  econstructor 2.
  { eapply (fill_contextual_step [AppLCtx _]).
    eapply base_contextual_step. by econstructor.
  }
  econstructor 2.
  { eapply base_contextual_step. econstructor; eauto. }
  reflexivity.
Qed.

(* Divergence *)
Definition ω : expr :=
  roll (λ: "x", (unroll "x") "x").

Definition Ω := ((unroll ω) ω)%E.

Lemma Ω_loops:
  tc contextual_step Ω Ω.
Proof.
  econstructor 2; [|econstructor 1].
  - rewrite /Ω /ω. eauto.
  - rewrite /Ω. eauto.
Qed.

Lemma ω_typed :
  TY 0; ∅ ⊢ ω : D.
Proof.
  solve_typing.
Qed.

Lemma Ω_typed : TY 0; ∅ ⊢ Ω : D.
Proof.
  rewrite /Ω. econstructor.
  - eapply typed_unroll'; eauto using ω_typed.
  - eapply ω_typed.
Qed.
