(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From semantics.axiomatic.program_logic Require Export sequential_wp.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma wp_lift_step_fupd s E1 E2 Φ e1 :
  to_val e1 = None →
  (|={E1, ∅}=> ∀ σ1, state_interp σ1 ={∅}=∗ 
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 κ efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
      ={∅}▷=∗ ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗ state_interp σ2 ∗ WP e2 @ s; ∅; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof. 
  rewrite /wp swp_eq /swp_def wp'_unfold /wp_pre=>->. 
  iIntros ">Hs !>" (σ1). iIntros "Hstate". 
  iDestruct ("Hs" with "Hstate") as ">($ & Hs)". 
  iIntros "!>" (e2 σ2 κ efs Hstep). iApply (step_fupd_wand with "(Hs [//]) []").
  iIntros "(-> & -> & $ & >Hwp)". eauto.
Qed.

(* 
Lemma wp_lift_stuck E1 E2 Φ e :
  to_val e = None →
  (∀ σ, state_interp σ ={E1,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E1; E2 ?{{ Φ }}.
Proof.
  rewrite /wp swp_eq /swp_def wp'_unfold /wp_pre=>->. iIntros "H" (σ1). "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.
 *)

(** Derived lifting lemmas. *)
Lemma wp_lift_step s E1 E2 Φ e1 :
  to_val e1 = None →
  (|={E1, ∅}=> ∀ σ1, state_interp σ1 ={∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 κ efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅}=∗
      ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗ state_interp σ2 ∗
      WP e2 @ s; ∅; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. 
  iMod "H" as "H". iIntros "!>" (σ1) "Hσ". iMod ("H" with "Hσ") as "($ & Hstep)".
  iIntros "!> * % !> !>". by iApply "Hstep".
Qed.

Lemma wp_lift_pure_step `{!Inhabited (state Λ)} s E1 E2 E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E1}[E']▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WP e2 @ s; E1; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iMod "H" as "H". 
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". 
  iIntros (σ1) "Hσ !>". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 κ efs ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iFrame "Hσ". iSplitR; first done. iSplitR; first done.
  iModIntro. 
  iMod "Hclose". iMod "H". by iApply "H".
Qed.

(*
Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.
*)

Lemma wp_lift_step_fupd_nomask {s E1 E2 E3 Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 κ efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1}[E3]▷=∗
      state_interp σ2 ∗ ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗
      WP e2 @ s; E1; E2 {{ Φ }})
  ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ _ e1)=>//. 
  iApply fupd_mask_intro; first set_solver. iIntros "Hcl".
  iIntros (σ1) "Hσ1". iMod "Hcl" as "_".
  iMod ("H" with "Hσ1") as "($ & H)".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 κ efs ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 κ efs with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & $ & $ & ?)".
  iApply fupd_mask_intro; first set_solver. iIntros "Hcl".
  iMod "Hcl" as "_". done.
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {s E1 E2 E' Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E1}[E']▷=> WP e2 @ s; E1; E2 {{ Φ }}) ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step s E1 E2 E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E1 E2 E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E1}[E']▷=>^n WP e2 @ s; E1; E2 {{ Φ }}) ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E1 E2 e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E1; E2 {{ Φ }} ⊢ WP e1 @ s; E1; E2 {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
