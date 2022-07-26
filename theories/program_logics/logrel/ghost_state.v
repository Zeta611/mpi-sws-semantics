From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.base_logic.lib Require Import mono_nat.
From semantics.pl Require Import invariant_lib.
From semantics.pl.logrel Require notation syntactic logrel.
From semantics.pl Require Import ghost_state_lib.
From semantics.pl.heap_lang Require Import primitive_laws proofmode.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

(** Update rules *)
Check upd_return.
Check upd_bind.
Check upd_wp.

(** Derived rules *)
Section derived.
  Context `{heapGS Σ}.
  Implicit Types (P Q : iProp Σ).

  Lemma upd_wand P Q :
    (|==> P) -∗
    (P -∗ Q) -∗
    |==> Q.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma upd_mono P Q :
    (P ⊢ Q) →
    (|==> P) ⊢ |==> Q.
  Proof.
    (* FIXME exercise *)
  Admitted.


  Lemma upd_trans P :
    (|==> |==> P) ⊢ |==> P.
  Proof.
    (* FIXME exercise *)
  Admitted.


  Lemma upd_frame P Q :
    P -∗ (|==> Q) -∗ |==> (P ∗ Q).
  Proof.
    (* FIXME: exercise *)
  Admitted.
End derived.

(** ** The mono nat ghost theory *)
Check mono.
Check lb.

Check mono_nat_make_bound.
Check mono_nat_use_bound.
Check mono_nat_increase_val.
Check mono_nat_new.

(* The lb resource is persistent *)
Check mono_nat_lb_persistent.
(* Both resources are also timeless *)
Check mono_nat_lb_timeless.
Check mono_nat_mono_timeless.

Section mono_derived.
(** In addition to the known [heapGS] assumption, we now also need to assume that the ghost state for the theory of mono_nat has been registered with Iris, expressed through the [mono_natG] assumption.
 *)
  Context `{heapGS Σ} `{mono_natG Σ}.
  Implicit Types (P Q : iProp Σ).

  Lemma mono_nat_increase γ n m :
    n ≤ m →
    mono γ n -∗ |==> mono γ m.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma mono_nat_increase_wp γ n m e Φ :
    n ≤ m →
    (mono γ m -∗ WP e {{ Φ }}) -∗
    (mono γ n -∗ WP e {{ Φ }}).
  Proof.
    iIntros (Hle) "He Hauth".
    iApply upd_wp. iApply (upd_wand with "[Hauth]"); last iApply "He".
    by iApply mono_nat_increase.
  Qed.

  Lemma mono_nat_new_wp e Φ n :
    (∀ γ, mono γ n -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }}.
  Proof.
    (* FIXME exercise *)
  Admitted.
End mono_derived.

(** ** Updates in the IPM *)
Section ipm.
  Context `{heapGS Σ} `{mono_natG Σ}.
  Implicit Types (P Q : iProp Σ).

  Lemma update_ipm_1 γ n :
    mono γ 0 -∗
    |==> mono γ n.
  Proof.
    iIntros "Hauth".
    (* [iMod] will eliminate an update modality in front of the hypothesis (using [upd_bind]) *)
    iMod (mono_nat_increase _ _ n with "Hauth") as "Hauth"; first lia.
    (* [iFrame] can also frame hypotheses below an update, using monotonicity *)
    iFrame "Hauth". done.
    Restart.
    iIntros "Hauth".
    iMod (mono_nat_increase with "Hauth") as "$"; [lia | done].
  Abort.

  Lemma update_ipm_2 γ n e Φ  :
    mono γ 0 -∗
    (mono γ n -∗ WP e {{ Φ }}) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros "Hauth He".
    (* [iMod] will automatically apply [upd_wp] to eliminate updates at a WP *)
    iMod (mono_nat_increase with "Hauth") as "Hauth"; first lia.
    by iApply "He".
  Abort.

  Lemma update_ipm_3 n γ :
    (|==> mono γ n) -∗ |==> mono γ (S n).
  Proof.
    (* the [>] intro pattern will eliminate an update when introducing an assumption *)
    iIntros ">Hauth". by iApply mono_nat_increase_val.
  Abort.
End ipm.


(** The Symbol ADT *)
Section logrel_symbol.
  Import logrel.notation syntactic logrel.
  Context `{heapGS Σ} `{mono_natG Σ}.

  Definition assert e := (if: e then #() else #0 #0)%E.

  Definition symbolT : type := ∃: ((Unit → #0) × (#0 → Unit)).
  Definition mk_symbol : expr :=
    let: "c" := ref #0 in
    pack (λ: <>, let: "x" := !"c" in "c" <- "x" + #1;; "x", λ: "y", assert ("y" ≤ !"c")).

  Definition symbolN := nroot .@ "symbol".

  Definition mono_nat_inv γ l : iProp Σ :=
    ∃ n : nat, l ↦ #n ∗ mono γ n.
  Definition mono_natT γ : semtypeO :=
    mk_semtype (λ v, ∃ (n : nat), ⌜v = #n⌝ ∗ lb γ n)%I.

  Lemma mk_symbol_semtyped :
    TY 0; ∅ ⊨ mk_symbol : symbolT.
  Proof using Type*.
    iIntros (δ γ) "#Hctx".
    iPoseProof (context_interp_dom_eq with "Hctx") as "%Hdom".
    rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_iff_L in Hdom.
    subst γ. rewrite subst_map_empty. unfold mk_symbol. simpl.
    wp_alloc l as "Hl". wp_pures.
    (* We allocate the ghost state + invariant *)
    iMod (mono_nat_new 0) as "(%γ & Hauth)".
    iApply (inv_alloc symbolN (mono_nat_inv γ l) with "[Hauth Hl]").
    { unfold mono_nat_inv. eauto with iFrame. }
    iIntros "#HInv".
    iApply wp_value.
    iExists _. iSplitR; first done.
    iExists (mono_natT γ), _, _. iSplitR; first done. iSplit.
    - (* mkSym *)
      iIntros (w) "!> ->".
      wp_pures. iApply (inv_open with "HInv"); first set_solver.
      iIntros "(%n & >Hl & Hauth)".
      wp_load. wp_store.
      iPoseProof (mono_nat_make_bound with "Hauth") as "#Hbound".
      iMod (mono_nat_increase _ _ (n + 1) with "Hauth") as "Hauth"; first lia.
      iApply wp_value. simpl. iSplitL.
      + unfold mono_nat_inv. iNext. iExists (n + 1). iFrame.
        replace (Z.of_nat (n +1)%nat) with (n + 1)%Z by lia; done.
      + eauto with iFrame.
    - (* get *)
      simpl. iIntros (w) "!> (%n & -> & Hlb)". wp_pures.
      iApply (inv_open with "HInv"); first set_solver.
      iIntros "(%m & >Hl & Hauth)".
      wp_load.
      iPoseProof (mono_nat_use_bound with "Hauth Hlb") as "%Hleq".
      wp_pures.  rewrite bool_decide_eq_true_2; last lia.
      wp_pures. iApply wp_value. unfold mono_nat_inv. eauto with iFrame.
  Qed.
End logrel_symbol.

(** Exercise: Oneshot *)
Section logrel_oneshot.
  Import logrel.notation syntactic logrel.
  Context `{heapGS Σ} `{oneshotG Σ nat}.


  Check os_pending_alloc.
  Check os_pending_shoot.
  Check os_shot_persistent.
  Check os_pending_shot_False.
  Check os_pending_pending_False.
  Check os_shot_agree.
  Check os_shot_timeless.
  Check os_pending_timeless.

  Definition code : expr :=
    let: "x" := ref #42 in
    λ: "f", "x" <- #1337;;
            "f" #();;
            assert (!"x" = #1337).

  Definition codeN := nroot .@ "oneshot".

  Lemma code_safe :
    TY 0; ∅ ⊨ code : ((TUnit → TUnit) → TUnit).
  Proof.
    (* FIXME: exercise *)
  Admitted.

End logrel_oneshot.

(** Exercise: Agreement *)
Section logrel_ag.
  Import logrel.notation syntactic logrel.
  Context `{heapGS Σ} `{halvesG Σ Z}.

  Check ghalves_alloc.
  Check ghalves_agree.
  Check ghalves_update.
  Check ghalf_timeless.

  Definition rec_code : expr :=
    λ: "f",
    let: "l" := ref #0 in
    (rec: "loop" <> :=
        let: "x" := !"l" in
        if: "f" (λ: <>, !"l")
        then
          assert (!"l" = "x");;
          "l" <- "x" + #1;;
          "loop" #()
        else !"l")
      #().

  Lemma rec_code_safe :
    TY 0 ; ∅ ⊨ rec_code : (((TUnit → TInt) → TBool) → TInt).
  Proof.
    (* FIXME: exercise *)
  Admitted.
End logrel_ag.

(** Exercise: Red/blue *)

Section logrel_redblue.
  Import logrel.notation syntactic logrel.
  Inductive colour := red | blue.

  Context `{heapGS Σ} `{agmapG Σ nat colour}.

  Check agmap_auth_alloc_empty.
  Check agmap_auth_insert.
  Check agmap_auth_lookup.
  Check agmap_elem_agree.
  Check agmap_elem_persistent.
  Check agmap_elem_timeless.
  Check agmap_auth_timeless.

  Definition mkColourGen : expr :=
    let: "c" := ref #0 in
    (λ: <>, let: "red" := !"c" in "c" <- #1 + "red";; "red",
     λ: <>, let: "blue" := !"c" in "c" <- #1 + "blue";; "blue",
     λ: "red" "blue", assert ("red" ≠ "blue")).

  Lemma mkColourGen_safe :
    TY 0; ∅ ⊨ mkColourGen : (∃: ∃: ((TUnit → #0) × (TUnit → #1)) × (#0 → #1 → TUnit)).
  Proof.
    (* FIXME exercise *)
  Admitted.
End logrel_redblue.
