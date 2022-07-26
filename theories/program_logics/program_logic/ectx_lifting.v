(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export ectx_language.
From semantics.pl.program_logic Require Export sequential_wp lifting.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant e := reducible_not_val e inhabitant.
Local Hint Resolve reducible_not_val_inhabitant : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma wp_lift_head_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (|={E1, ∅}=> ∀ σ1, state_interp σ1 ={∅,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 κ efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅}=>
      state_interp σ2 ∗ ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗
      WP e2 @ s; ∅; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//. iMod "H". iIntros "!>" (σ1) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 κ efs ?).
  iApply (step_fupd_wand with "(H []) []"); first eauto.
  iIntros "($ & $ & $)".
Qed.

Lemma wp_lift_head_step {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (|={E1, ∅}=> ∀ σ1, state_interp σ1 ={∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 κ efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅}=∗
      state_interp σ2 ∗ ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗ WP e2 @ s; ∅; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_head_step_fupd; [done|]. iMod "H".
  iIntros "!>" (?) "?".
  iMod ("H" with "[$]") as "[$ H]". iIntros "!>" (e2 σ2 κ efs ?) "!> !>". by iApply "H".
Qed.

Lemma wp_lift_head_step_fupd_nomask {s E1 E2 E3 Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 κ efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E1}[E3]▷=∗
      state_interp σ2 ∗ ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗
      WP e2 @ s; E1; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd_nomask; [done|].
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iIntros (e2 σ2 κ efs Hstep).
  iApply (step_fupd_wand with "(H []) []"); first by eauto.
  iIntros "($ & $)".
Qed.

Lemma wp_lift_pure_det_head_step {s E1 E2 E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E1}[E']▷=> WP e2 @ s; E1; E2 {{ Φ }}) ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step' {s E1 E2 Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ WP e2 @ s; E1; E2 {{ Φ }} ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ s; _ {{ _ }})%I]wp_lift_pure_det_head_step //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
