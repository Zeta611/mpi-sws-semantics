From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export debruijn.
From semantics.ts.systemf Require Import lang notation parallel_subst types bigstep tactics logrel.
From Equations Require Import Equations.

(** * Free Theorems *)
Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
  (e : expr)
  (A : type).

Lemma not_every_type_inhabited : ¬ ∃ e, TY 0; ∅ ⊢ e : (∀: #0).
Proof.
  intros (e & Hty%sem_soundness).
  specialize (Hty ∅ δ_any). simp type_interp in Hty.
  destruct Hty as (v & Hb & Hv).
  { constructor. }
  simp type_interp in Hv. destruct Hv as (e' & -> & Hcl & Ha).
  (* [specialize_sem_type] defines a semantic type, spawning a subgoal for the closedness sidecondition *)
  specialize_sem_type Ha with (λ _, False) as τ; first done.
  simp type_interp in Ha. destruct Ha as (v' & He' & Hv').
  simp type_interp in Hv'. simpl in Hv'.
  done.
Qed.

Lemma all_identity :
  ∀ e,
  TY 0; ∅ ⊢ e : (∀: #0 → #0) →
  ∀ v, is_closed [] v → big_step (e <> (of_val v)) v.
Proof.
  intros e Hty%sem_soundness v0 Hcl_v0.
  specialize (Hty ∅ δ_any). simp type_interp in Hty.
  destruct Hty as (v & Hb & Hv).
  { constructor. }

  simp type_interp in Hv. destruct Hv as (e' & -> & Hcl & Hv).
  specialize_sem_type Hv with (λ v, v = v0) as τ.
  { intros v ->; done. }
  simp type_interp in Hv.

  destruct Hv as (v & He & Hv).
  simp type_interp in Hv.
  destruct Hv as (x & e'' & -> & Hcl' & Hv).
  specialize (Hv v0 ltac:(done)).

  simp type_interp in Hv. destruct Hv as (v & Hb' & Hv).
  simp type_interp in Hv; simpl in Hv. subst v.

  rewrite subst_map_empty in Hb.
  eauto using big_step_of_val.
Qed.
