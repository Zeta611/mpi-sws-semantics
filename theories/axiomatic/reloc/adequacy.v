From iris.heap_lang Require Export lang.
From semantics.axiomatic.heap_lang Require Export adequacy.
From iris.base_logic Require Import ghost_var ghost_map.
From semantics.axiomatic.reloc Require Import ghost_state.
From semantics.axiomatic.reloc Require Export syntactic logrel.
From iris.prelude Require Import options.


Lemma refines_adequate Σ `{reloc_preGS Σ} (τ : ∀ _ : relocGS Σ, semtypeO) ϕ (e e' : expr) σ :
  σ = mkstate σ.(heap) →
  (∀ `{relocGS Σ}, ∀ v v', τ _ v v' -∗ ⌜ϕ v v'⌝) →
  (∀ `{relocGS Σ}, ⊢ refines e e' (τ _)) →
  adequate NotStuck e σ (λ v _, ∃ v' h', rtc thread_step (e', σ) (of_val v', h') ∧ ϕ v v').
Proof.
  intros Hnoproph Hpost Hlog.
  eapply (heap_adequacy Σ _). iIntros (Hheap).
  iMod (ghost_map_alloc σ.(heap)) as "(%γheap & Hauth & _)".
  iMod (ghost_var_alloc e') as "(%γexpr & He1 & He2)".
  set (Hreloc := (RelocGS Σ _ _ _ γexpr γheap)).

  (* initialize the invariant *)
  iApply (inv_alloc srcN (src_inv e' σ.(heap)) with "[Hauth He1]").
  { iExists e', σ.(heap). rewrite exprS_eq heapS_auth_eq. rewrite /exprS_def /heapS_auth_def.
    iFrame. done.
  }

  iIntros "#Hinv".
  iApply wp_fupd.
  iApply (wp_wand with "[He2]").
  { iApply (Hlog Hreloc $! []). iSplit.
    - iExists _, _. iFrame "Hinv".
    - rewrite exprS_eq /exprS_def. iFrame.
  }
  iIntros (v) "(%v' & [_ Hsrc] & #Ht)".
  (* requires that we open invariants around fancy updates *)
  iInv "Hinv" as "(%e'' & %σ'' & >He & >Hheap & >%Hstep)" "Hcl".
  iDestruct (exprS_agree with "He Hsrc") as %->.
  iMod ("Hcl" with "[-]").
  { iNext. iExists _, _. iFrame. done. }
  iModIntro. iDestruct (Hpost with "Ht") as "%Hp".
  iPureIntro. eexists _, _.
  rewrite Hnoproph. split; done.
Qed.

Lemma thread_erased_step e e' σ σ' :
  thread_step (e, σ) (e', σ') →
  erased_step ([e], σ) ([e'], σ').
Proof.
  intros Hprim. exists [].
  eapply (step_atomic _ _ _ _ [] [] []); done.
Qed.

Lemma rtc_thread_erased_step e e' σ σ' :
  rtc thread_step (e, σ) (e', σ') →
  rtc erased_step ([e], σ) ([e'], σ').
Proof.
  intros Ha. eapply (rtc_congruence (λ '(e, σ), ([e], σ)) erased_step) in Ha; first done.
  intros [][]; simpl; apply thread_erased_step.
Qed.

Theorem refines_typesafety Σ `{reloc_preGS Σ} (τ : ∀ _ : relocGS Σ, semtypeO) (e e' : expr) e1 σ σ' :
  σ = mkstate σ.(heap) →
  (∀ `{relocGS Σ}, ⊢ refines e e' (τ _)) →
  rtc thread_step (e, σ) (e1, σ') →
  not_stuck e1 σ'.
Proof.
  intros ? Hlog ?%rtc_thread_erased_step.
  cut (adequate NotStuck e σ (λ v _, ∃ v' h', rtc thread_step (e', σ) (of_val v', h') ∧ True)).
  { intros [_ ?]. eapply adequate_not_stuck; [ done .. | ]. by apply elem_of_list_singleton. }
  eapply (refines_adequate _ τ); eauto.
Qed.
