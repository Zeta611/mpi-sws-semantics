From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From semantics.pl Require Export invariant_lib.
From semantics.pl.program_logic Require Export notation.
From semantics.pl.heap_lang Require Export primitive_laws proofmode.
From iris.prelude Require Import options.



(** Rules for fancy updates *)
Section fupd.
Context `{heapGS Σ}.
Implicit Types (P Q : iProp Σ).
(** Axiomatic rules shown in the lecture notes *)

Lemma fupd_return E P :
  P ⊢ |={E, E}=> P.
Proof.
  eauto.
Qed.

Lemma fupd_bind E1 E2 E3 P Q :
  (|={E1, E2}=> P) ∗ (P -∗ |={E2, E3}=> Q) ⊢ |={E1, E3}=> Q.
Proof.
  iIntros "[>HP HPQ]". by iApply "HPQ".
Qed.

(*Check bupd_fupd.*)

Lemma fupd_wp' (e : expr) (Φ : val → iProp Σ) s E1 E2 E3:
  (|={E1, E2}=> WP e @ s; E2; E3 {{ Φ }}) -∗ WP e @ s; E1; E3 {{ Φ }}.
Proof. iApply fupd_wp. Qed.
Lemma fupd_wp (e : expr) (Φ : val → iProp Σ) E :
  (|={E}=> WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
Proof. iApply fupd_wp'. Qed.

Lemma fupd_timeless P `{!Timeless P} E :
  ▷ P -∗ |={E}=> P.
Proof.
  by iIntros ">$".
Qed.

Lemma fupd_inv_open N E P :
  ↑N ⊆ E →
  inv N P -∗ |={E, E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N, E}=∗ True).
Proof.
  intros. by iApply inv_acc.
Qed.

(*Check fupd_mask_frame_r.*)

Lemma fupd_intro_mask E1 E2 P :
  E2 ⊆ E1 →
  (|={E1}=> P) -∗ |={E1, E2}=> |={E2, E1}=> P.
Proof.
  iIntros (?) "Ha". iApply fupd_mask_intro; first done.
  by iIntros ">_".
Qed.
End fupd.

Section derived.
Context `{heapGS Σ}.
Implicit Types (P Q : iProp Σ).
(** FIXME the following derived rules are exercises for you.
  You may use the IPM, but don't use its built-in support for fancy updates, only the lemmas above.
  *)

Lemma fupd_wand E1 E2 P Q :
  (|={E1, E2}=> P) -∗ (P -∗ Q) -∗ |={E1, E2}=> Q.
Proof.
  (* FIXME *)
Admitted.


Lemma fupd_mono E1 E2 P Q :
  (P ⊢ Q) →
  (|={E1, E2}=> P) ⊢ |={E1, E2}=> Q.
Proof.
  (* FIXME *)
Admitted.

Lemma fupd_trans E1 E2 E3 P :
  (|={E1, E2}=> |={E2, E3}=> P) -∗ |={E1, E3}=> P.
Proof.
  (* FIXME *)
Admitted.


Lemma fupd_frame E1 E2 P Q :
  P -∗ (|={E1, E2}=> Q) -∗ |={E1, E2}=> (P ∗ Q).
Proof.
  (* FIXME *)
Admitted.
End derived.
