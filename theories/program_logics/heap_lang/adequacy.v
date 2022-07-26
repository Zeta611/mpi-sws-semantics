From iris.algebra Require Import auth.
From iris.proofmode Require Import proofmode.
From semantics.pl.program_logic Require Export sequential_wp adequacy.
From iris.heap_lang Require Import notation.
From semantics.pl.heap_lang Require Export proofmode.
From iris.prelude Require Import options.

Class heapGpreS Σ := HeapGpreS {
  heapGpreS_iris :> invGpreS Σ;
  heapGpreS_heap :> gen_heapGpreS loc (option val) Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val)].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iModIntro. iExists
    (λ σ, (gen_heap_interp σ.(heap))%I).
  iFrame. iApply (Hwp (HeapGS _ _ _)).
Qed.
