From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation primitive_laws adequacy.
From semantics.pl.concurrent_logrel Require Import syntactic logrel.
From iris.prelude Require Import options.


Definition trivial_env {Σ} `{heapGS Σ} : envO :=
  λne n, (mk_semtype (λ v, False)%I : semtypeO (Σ := Σ)).

Theorem soundness Σ `{heapGpreS Σ} e τ e' tp σ σ' :
  (∀ `{heapGS Σ}, TY 0; ∅ ⊨ e : τ) →
  rtc erased_step ([e], σ) (tp, σ') →
  e' ∈ tp →
  not_stuck e' σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ _ _, True)); first by intros [_ Hsafe]; eapply Hsafe; eauto.
  eapply (heap_adequacy Σ _).
  iIntros (??) "_".
  iApply (wp_wand with "[]").
  - rewrite -(subst_map_empty e).
    iApply (Hlog _ $! trivial_env).
    iApply context_interp_empty.
  - eauto.
Qed.

Lemma syn_soundness e A e' tp σ σ' :
  syn_typed 0 ∅ e A →
  rtc erased_step ([e], σ) (tp, σ') →
  e' ∈ tp →
  not_stuck e' σ'.
Proof.
  intros ??.
  set (preG := heapGpreS heapΣ).
  eapply (soundness heapΣ).
  + intros. by apply fundamental.
  + done.
Qed.
