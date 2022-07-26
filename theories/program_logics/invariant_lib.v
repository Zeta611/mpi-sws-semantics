From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.base_logic Require Export invariants.
From semantics.pl.heap_lang Require Export primitive_laws_nolater.
From semantics.pl.heap_lang Require Import adequacy proofmode.

(** Rules for impredicative invariants *)

Section inv.
  Context `{heapGS Σ}.
  Lemma inv_alloc N F E e Φ :
    F -∗
    (inv N F -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "HF Hs".
    iMod (inv_alloc N with "HF") as "#Hinv".
    by iApply "Hs".
  Qed.
  Lemma inv_open N E F e Φ :
    ↑N ⊆ E →
    inv N F -∗
    (▷ F -∗ WP e @ (E ∖ ↑N) {{ v, ▷ F ∗ Φ v }})%I -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hincl) "#Hinv Hs".
    iMod (inv_acc with "Hinv") as "(HF & Hcl)"; first done.
    iApply wp_fupd'. iApply wp_wand_r.
    iSplitR "Hcl". { iApply "Hs". iFrame. }
    iIntros (v) "[HF Hphi]". iMod ("Hcl" with "HF"). done.
  Qed.
End inv.
