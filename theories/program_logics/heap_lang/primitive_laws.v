(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap.
From semantics.pl.program_logic Require Export sequential_wp.
From semantics.pl.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export class_instances.
From iris.heap_lang Require Import tactics notation.
From semantics.pl.program_logic Require Export notation.
From iris.prelude Require Import options.

Class heapGS Σ := HeapGS {
  heapGS_invGS : invGS_gen HasNoLc Σ;
  heapGS_gen_heapGS :> gen_heapGS loc (option val) Σ;
}.

Global Instance heapGS_irisGS `{!heapGS Σ} : irisGS heap_lang Σ := {
  iris_invGS := heapGS_invGS;
  state_interp σ := (gen_heap_interp σ.(heap))%I;
}.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦{ dq } v" := (mapsto (L:=loc) (V:=option val) l dq (Some v%V))
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (mapsto (L:=loc) (V:=option val) l DfracDiscarded (Some v%V))
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto (L:=loc) (V:=option val) l (DfracOwn q) (Some v%V))
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=option val) l (DfracOwn 1) (Some v%V))
  (at level 20, format "l  ↦  v") : bi_scope.

Section lifting.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb s E1 E2 f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E1; E2 {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ s; E1; E2 {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E1; E2 {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first done.
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. apply mapsto_persist. Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.mapsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma wp_allocN_seq s E v n Φ :
  (0 < n)%Z →
  ▷ (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v) -∗ Φ (LitV $ LitLoc l)) -∗
  WP AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_head_step_fupd_nomask; first done.
  iIntros (σ1) "Hσ !>"; iSplit; first by destruct n; auto with lia head_step.
  iIntros (e2 σ2 κ efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iApply step_fupd_intro; first done.
  iModIntro. iFrame "Hσ". do 2 (iSplit; first done).
  iApply wp_value_fupd. iApply "HΦ".
  by iApply heap_array_to_seq_mapsto.
Qed.

Lemma wp_alloc s E v Φ :
  ▷ (∀ l, l ↦ v -∗ Φ (LitV $ LitLoc l)) -∗
  WP Alloc (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros "HΦ". iApply wp_allocN_seq; [auto with lia..|].
  iIntros "!>" (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.

Lemma wp_free s E l v Φ :
  ▷ l ↦ v -∗
  (▷ Φ (LitV LitUnit)) -∗
  WP Free (Val $ LitV $ LitLoc l) @ s; E; E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_head_step_fupd_nomask; first done.
  iIntros (σ1) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 κ efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iIntros "!>!>!>". iSplit; first done. iSplit; first done.
  iApply wp_value. by iApply "HΦ".
Qed.

Lemma wp_load s E l dq v Φ :
  ▷ l ↦{dq} v -∗
  ▷ (l ↦{dq} v -∗ Φ v) -∗
  WP Load (Val $ LitV $ LitLoc l) @ s; E; E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_head_step_fupd_nomask; first done.
  iIntros (σ1) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 κ efs Hstep); inv_head_step.
  iApply step_fupd_intro; first done. iNext. iFrame.
  iSplitR; first done. iSplitR; first done. iApply wp_value. by iApply "HΦ".
Qed.

Lemma wp_store s E l v' v Φ :
  ▷ l ↦ v' -∗
  ▷ (l ↦ v -∗ Φ (LitV LitUnit)) -∗
  WP Store (Val $ LitV $ LitLoc l) (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_head_step_fupd_nomask; first done.
  iIntros (σ1) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 κ efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iApply step_fupd_intro; first done. iNext.
  iSplit; first done. iSplit; first done.
  iApply wp_value. by iApply "HΦ".
Qed.
End lifting.
