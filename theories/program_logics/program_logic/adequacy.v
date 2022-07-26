From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From semantics.pl.program_logic Require Export sequential_wp.
From iris.prelude Require Import options.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)

Section adequacy.
Context `{!irisGS Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, wp' s ∅ e Φ)%I.

Lemma wp'_step s e1 σ1 e2 σ2 E κs efs Φ :
  prim_step e1 σ1 κs e2 σ2 efs →
  state_interp σ1 -∗ wp' s E e1 Φ
    ={E,∅}=∗ |={∅}▷=> |={∅, E}=>
    state_interp σ2 ∗ wp' s E e2 Φ ∗ ⌜efs = []⌝ ∗ ⌜κs = []⌝.
Proof.
  rewrite wp'_unfold /wp_pre.
  iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κs e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)". iSpecialize ("H" with "[//]").
  iModIntro. iApply (step_fupd_wand with "[H]"); first by iApply "H".
  iIntros ">(-> & -> & Hσ & H)". eauto with iFrame.
Qed.

Lemma wptp_step s es1 es2 κ σ1 σ2 Φs :
  step (es1,σ1) κ (es2, σ2) →
  state_interp σ1 -∗ wptp s es1 Φs -∗
  |={∅,∅}=> |={∅}▷=> |={∅,∅}=>
  state_interp σ2 ∗
  wptp s es2 Φs ∗
  ⌜κ= []⌝ ∗
  ⌜length es1 = length es2⌝.
Proof.
  iIntros (Hstep) "Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iMod (wp'_step with "Hσ Ht") as "H"; first done. iModIntro.
  iApply (step_fupd_wand with "H"). iIntros ">($ & He2 & -> & ->) !>".
  rewrite !app_nil_r; iFrame.
  iPureIntro; split; first done.
  rewrite !app_length; simpl; lia.
Qed.

Lemma wptp_steps s n es1 es2 κs σ1 σ2 Φs :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 -∗ wptp s es1 Φs
  ={∅,∅}=∗ |={∅}▷=>^n |={∅,∅}=>
    state_interp σ2 ∗
    wptp s es2 Φs ∗
    ⌜κs= []⌝ ∗
    ⌜length es1 = length es2⌝.
Proof.
  revert es1 es2 κs σ1 σ2 Φs.
  induction n as [|n IH]=> es1 es2 κs σ1 σ2 Φs /=.
  { inversion_clear 1; iIntros "? ?". iFrame. done. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  iDestruct (wptp_step with "Hσ He") as ">H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupd_fupd. iApply (step_fupd_wand with "H").
  iIntros ">(Hσ & He & -> & %)". iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as "(? & ? & -> & %)".
  iFrame. iPureIntro. split; first done. lia.
Qed.

Lemma wp_not_stuck `{!HasNoLc Σ} e σ E Φ :
  state_interp σ -∗ wp' NotStuck E e Φ ={E}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp'_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy `{!HasNoLc Σ} Φs s n es1 es2 κs σ1 σ2 :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 -∗ wptp s es1 Φs
  ={∅,∅}=∗ |={∅}▷=>^n |={∅,∅}=>
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 ∗
    ([∗ list] e;Φ ∈ es2;Φs, from_option Φ True (to_val e)) ∗
    ⌜length es1 = length es2⌝ ∗
    ⌜κs = []⌝.
Proof.
  iIntros (Hstep) "Hσ He". iMod (wptp_steps with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as "(Hσ & Ht & $ & $)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ∅
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 ∗
     wptp s es2 (Φs))%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (e' -> He').
    move: He' => /(elem_of_list_split _ _)[?[?->]].
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl. iApply wp'_value_fupd'. done.
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ Λ `{!invGpreS Σ} e σ1 n κs t2 σ2 φ :
  (∀ `{Hinv : !invGS Σ} `{!HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → iProp Σ)
         (Φ : (val Λ → iProp Σ)),
       let _ : irisGS Λ Σ := IrisG _ _ Hinv stateI
       in
       stateI σ1 ∗
       (WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ e',
         (* there will only be a single thread *)
         ⌜ t2 = [e'] ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then the thread is not stuck *)
         ⌜ s = NotStuck → not_stuck e' σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 -∗
         (* If the thread is done, the post-condition [Φ] holds.
            Additionally, we can establish that all invariants will hold in this case.
          *)
         (from_option (λ v, |={∅,⊤}=> Φ v) True (to_val e')) -∗
         (* Under all these assumptions, we can conclude [φ] in the logic.
            In the case that the thread is done, we can use the last assumption to
            establish that all invariants hold.
            After opening all required invariants, one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={∅,∅}=> ⌜ φ ⌝)) →
  nsteps n ([e], σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  apply (step_fupdN_soundness_no_lc _ n)=> Hinv Hlc.
  iMod Hwp as (s stateI Φ) "(Hσ & Hwp & Hφ)".
  rewrite /wp swp_eq /swp_def. iMod "Hwp".
  iMod (@wptp_strong_adequacy _ _ (IrisG _ _ Hinv stateI) _ [_]
    with "[Hσ] [Hwp]") as "H";[ done | done | | ].
  { by iApply big_sepL2_singleton. }
  iAssert (|={∅}▷=>^n |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct n as [ | n ]; first done. iModIntro. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as "(%Hns & Hσ & Hval & %Hlen & ->) /=".
  destruct t2 as [ | e' []]; simpl in Hlen; [lia | | lia].
  rewrite big_sepL2_singleton.
  iApply ("Hφ" with "[//] [%] Hσ Hval").
  intros ->. apply Hns; first done. by rewrite elem_of_list_singleton.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

Corollary wp_adequacy Σ Λ `{!invGpreS Σ} s e σ φ :
  (∀ `{Hinv : !invGS Σ} `{!HasNoLc Σ},
     ⊢ |={⊤}=> ∃ (stateI : state Λ → iProp Σ),
       let _ : irisGS Λ Σ := IrisG _ _ Hinv stateI
       in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ??.
  iMod Hwp as (stateI) "[Hσ Hwp]".
  iExists s, stateI, (λ v, ⌜φ v⌝%I) => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 ->) "% H Hv".
  destruct (to_val e2) as [ v2 | ] eqn:Hv.
  - simpl. iMod "Hv" as "%". iApply fupd_mask_intro_discard; [done|].
    iSplit; iPureIntro.
    + intros ??. destruct t2'; last done. intros [= ->].
      rewrite to_of_val in Hv. injection Hv as ->. done.
    + intros ? ?. rewrite elem_of_list_singleton. naive_solver.
  - iModIntro. iSplit; iPureIntro.
    + intros ??. destruct t2'; last done. intros [= ->].
      rewrite to_of_val in Hv. done.
    + intros ? ?. rewrite elem_of_list_singleton. naive_solver.
Qed.
