From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
From semantics.pl.program_logic Require Export notation.
From iris.prelude Require Import options.
Import uPred.

Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS Σ;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [state Λ] is the global state. *)
  state_interp : state Λ → iProp Σ;
}.
Global Opaque iris_invGS.

Definition wp_pre `{!irisGS Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1,
     state_interp σ1 ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 κ efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
         ={∅}▷=∗ |={∅,E}=>
         ⌜efs = []⌝ ∗ ⌜κ = []⌝ ∗ state_interp σ2 ∗ wp E e2 Φ
  end%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 22 (f_contractive || f_equiv).
  apply Hwp.
Qed.

Definition wp_def `{!irisGS Λ Σ} := λ (s : stuckness), fixpoint (wp_pre s).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Lemma wp_eq `{!irisGS Λ Σ} : wp' = @wp_def Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

(* sequential version that allows opening invariants *)
Definition swp_def `{!irisGS Λ Σ} : Swp (iProp Σ) (expr Λ) (val Λ) stuckness := λ s E1 E2 e Φ, (|={E1, ∅}=> wp' s ∅ e (λ v, |={∅, E2}=> Φ v))%I.
Definition swp_aux : seal (@swp_def). Proof. by eexists. Qed.
Definition swp := swp_aux.(unseal).
Global Arguments swp {Λ Σ _}.
Global Existing Instance swp.
Lemma swp_eq `{!irisGS Λ Σ} : swp = @swp_def Λ Σ _.
Proof. rewrite -swp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp'_unfold s E e Φ :
  wp' s E e Φ ⊣⊢ wp_pre s (wp' s) E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp'_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp' s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp'_unfold /wp_pre /=.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 22 (f_contractive || f_equiv).
  rewrite IH; [done | lia | ]. intros v. eapply dist_S, HΦ.
Qed.
Global Instance wp'_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp' s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp'_ne=>v; apply equiv_dist.
Qed.
Global Instance wp'_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp' s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp'_unfold /wp_pre He /=.
  do 23 (f_contractive || f_equiv).
  by do 4 f_equiv.
Qed.

Lemma wp'_value_fupd' s E Φ v : wp' s E (of_val v) Φ ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp'_unfold /wp_pre to_of_val. auto. Qed.

Lemma wp'_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  wp' s1 E1 e Φ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ wp' s2 E2 e Ψ.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp'_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 κ efs Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H". iModIntro.
  iMod "H" as "($ & $ & $ & H)".
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[//] H HΦ").
Qed.

Lemma fupd_wp' s E e Φ : (|={E}=> wp' s E e Φ) ⊢ wp' s E e Φ.
Proof.
  rewrite wp'_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp'_fupd s E e Φ : wp' s E e (λ v, |={E}=> Φ v) ⊢ wp' s E e Φ.
Proof. iIntros "H". iApply (wp'_strong_mono s s E with "H"); auto. Qed.

Lemma wp'_bind K `{!LanguageCtx K} s E e Φ :
  wp' s E e (λ v, wp' s E (K (of_val v)) Φ) ⊢ wp' s E (K e) Φ.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp'_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp'. }
  rewrite wp'_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 κ efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 κ efs with "[//]") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iMod "H" as "($ & $ & $ & H)". iModIntro. by iApply "IH".
Qed.

Lemma wp'_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ wp' s E2 e (λ v, P ={E1}=∗ Φ v) -∗ wp' s E1 e Φ.
Proof.
  iIntros (?%TCEq_eq ?) "HR H".
  rewrite !wp'_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. done. }
  iIntros (σ1) "Hσ".
  iMod "HR".
  iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto. }
  iIntros (e2 σ2 κ efs Hstep).
  iMod ("H" $! _ _ _ with "[//]") as "H". iIntros "!>!>!>".
  iMod "H". iMod "H" as "($ & $ & $ & H)". iMod "HR". iModIntro.
  iApply (wp'_strong_mono with "H [HR]"); [done | done | ].
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End wp.

Section swp.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Global Instance wp_ne s E1 E2 e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E1 E2 e).
Proof.
  intros ???.
  rewrite /wp swp_eq /swp_def /=.
  do 2 f_equiv. intros ?. f_equiv. done.
Qed.
Global Instance wp_proper s E1 E2 e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp s E1 E2 e).
Proof.
  intros ???. rewrite /wp swp_eq /swp_def /=.
  do 2 f_equiv. intros ?. f_equiv. done.
Qed.

Lemma wp_value_fupd' s E1 E2 Φ v : wp s E1 E2 (of_val v) Φ ⊣⊢ |={E1, E2}=> Φ v.
Proof.
  rewrite /wp swp_eq /swp_def wp'_value_fupd'.
  iSplit.
  - iIntros "H". iMod "H". iMod "H". iMod "H". done.
  - iIntros "H". iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
    iModIntro. iModIntro. iMod "Hcl" as "_". done.
Qed.

Lemma wp_strong_mono s1 s2 E1 E2 E3 e Φ Ψ :
  s1 ⊑ s2 →
  wp s1 E1 E2 e Φ -∗ (∀ v, Φ v ={E2, E3}=∗ Ψ v) -∗ wp s2 E1 E3 e Ψ.
Proof.
  iIntros (?) "H HΦ".
  rewrite /wp swp_eq /swp_def.
  iMod "H". iModIntro.
  iApply (wp'_strong_mono _ _ ∅ ∅ with "H [HΦ]"); [done | done | ].
  iIntros (v) "H". iModIntro. iMod "H". by iApply "HΦ".
Qed.

Lemma fupd_wp s E1 E2 E3 e Φ : (|={E1, E2}=> wp s E2 E3 e Φ) ⊢ wp s E1 E3 e Φ.
Proof.
  rewrite /wp swp_eq /swp_def. iIntros "H". iApply fupd_wp'.
  iMod "H". iMod "H". iModIntro. iModIntro. done.
Qed.
Lemma wp_fupd' s E1 E2 e Φ : wp s E1 E1 e (λ v, |={E1, E2}=> Φ v) ⊢ wp s E1 E2 e Φ.
Proof. iIntros "H". iApply (wp_strong_mono s s E1 E1 with "H"); auto. Qed.
Lemma wp_fupd s E1 E2 e Φ : wp s E1 E2 e (λ v, |={E2}=> Φ v) ⊢ wp s E1 E2 e Φ.
Proof. iIntros "H". iApply (wp_strong_mono s s E1 E2 with "H"); auto. Qed.

Lemma wp_bind K `{!LanguageCtx K} s E1 E2 E3 e Φ :
  wp s E1 E2 e (λ v, wp s E2 E3 (K (of_val v)) Φ) ⊢ wp s E1 E3 (K e) Φ.
Proof.
  iIntros "H".
  rewrite /wp swp_eq /swp_def. iMod "H". iApply wp'_bind.
  iModIntro. iApply (wp'_strong_mono with "H"); [done | done | ].
  iIntros (v) "H". iMod "H". iMod "H". done.
Qed.

Lemma wp_step_fupd s E1 E2 E3 e P Φ :
  TCEq (to_val e) None →
  (|={E1}[E2]▷=> P) -∗ wp s E2 E2 e (λ v, P ={E1, E3}=∗ Φ v) -∗ wp s E1 E3 e Φ.
Proof.
  iIntros (?) "HR H".
  rewrite /wp swp_eq /swp_def.
  iMod "HR". iMod "H". iModIntro.
  iApply (wp'_step_fupd _ ∅ ∅ _ (|={E2, E1}=> P) with "[HR] [H]"); [done |  | ].
  { iApply (step_fupd_intro ∅ ∅); done. }
  iApply (wp'_strong_mono with "H"); [done | done | ].
  iIntros (v) "H1 !> H2 !>".
  iMod "H1". iMod "H2". by iMod ("H1" with "H2").
Qed.

(** * Derived rules *)
Lemma wp_mono s E1 E2 e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E1; E2 {{ Φ }} ⊢ WP e @ s; E1; E2 {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E1 E2 e Φ :
  s1 ⊑ s2 → WP e @ s1; E1; E2 {{ Φ }} ⊢ WP e @ s2; E1; E2 {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E1 E2 e Φ :
  WP e @ s; E1; E2 {{ Φ }} ⊢ WP e @ E1; E2 ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Global Instance wp_mono' s E1 E2 e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E1 E2 e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E1 E2 e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E1 E2 e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s E1 E2 Φ e v : IntoVal e v → WP e @ s; E1; E2 {{ Φ }} ⊣⊢ |={E1, E2}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s E1 E2 e Φ R : R ∗ WP e @ s; E1; E2 {{ Φ }} ⊢ WP e @ s; E1; E2 {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E1 E2 e Φ R : WP e @ s; E1; E2 {{ Φ }} ∗ R ⊢ WP e @ s; E1; E2 {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.


Lemma wp_frame_step_l s E1 E2 E3 e Φ R :
  TCEq (to_val e) None →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2; E2 {{ v, |={E1, E3}=> Φ v }} ⊢ WP e @ s; E1; E3 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). iIntros (?) "Hf $". iApply "Hf".
Qed.
Lemma wp_frame_step_r s E1 E2 E3 e Φ R :
  TCEq (to_val e) None →
  WP e @ s; E2; E2 {{ v, |={E1, E3}=> Φ v }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1; E3 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E1 E2 e Φ R :
  TCEq (to_val e) None → E1 ⊆ E2 → ▷ R ∗ WP e @ s; E1; E2 {{ Φ }} ⊢ WP e @ s; E1; E2 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[??]". iApply (wp_frame_step_l s E1 E1 E2).
  iFrame. iSplitR; first eauto. iApply (wp_strong_mono with "[$]"); first done.
  iIntros (v) "?". iMod (fupd_mask_subseteq E1) as "Hcl"; first done. iModIntro. iMod "Hcl". eauto.
Qed.
Lemma wp_frame_step_r' s E1 E2 e Φ R :
  TCEq (to_val e) None → E1 ⊆ E2 → WP e @ s; E1; E2 {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E1; E2 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l'.
Qed.

Lemma wp_wand s E1 E2 e Φ Ψ :
  WP e @ s; E1; E2 {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E1; E2 {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E1 E2 e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E1; E2 {{ Φ }} ⊢ WP e @ s; E1; E2 {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E1 E2 e Φ Ψ :
  WP e @ s; E1; E2 {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E1; E2 {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E1 E2 e Φ R :
  R -∗ WP e @ s; E1; E2 {{ v, R -∗ Φ v }} -∗ WP e @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma wp_bind' K `{!LanguageCtx K} s E1 E2 e Φ :
  wp s E1 E1 e (λ v, wp s E1 E2 (K (of_val v)) Φ) ⊢ wp s E1 E2 (K e) Φ.
Proof. iApply wp_bind. Qed.
End swp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E1 E2 e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E1; E2 {{ Φ }}) (WP e @ s; E1; E2 {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E1 E2 e Φ : IsExcept0 (WP e @ s; E1; E2 {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}(fupd_wp _ E1 E1) -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E1 E2 e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E1; E2 {{ Φ }}) (WP e @ s; E1; E2 {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E1 E2 e P Φ :
    ElimModal True p false (|={E1}=> P) P (WP e @ s; E1; E2 {{ Φ }}) (WP e @ s; E1; E2 {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_ne p s E1 E2 E3 e P Φ :
    ElimModal True p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1; E3 {{ Φ }}) (WP e @ s; E2; E3 {{ Φ }})%I | 100.
  Proof.
    intros ?. rewrite intuitionistically_if_elim fupd_frame_r wand_elim_r.
    rewrite fupd_wp //.
  Qed.

  Global Instance add_modal_fupd_wp s E1 E2 e P Φ :
    AddModal (|={E1}=> P) P (WP e @ s; E1; E2 {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_nonatomic {X} E0 E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E1 E0) (fupd E2 E2)
            α β γ (WP e @ s; E1; E2 {{ Φ }})
            (λ x, WP e @ s; E0; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
