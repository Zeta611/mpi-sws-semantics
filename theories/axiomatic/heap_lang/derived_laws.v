(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import tactics notation.
From semantics.axiomatic.heap_lang Require Export primitive_laws.
From iris.prelude Require Import options.

(** The [array] connective is a version of [mapsto] that works
with lists of values. *)

Definition array `{!heapGS Σ} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦∗{ dq } vs" := (array l dq vs)
  (at level 20, format "l  ↦∗{ dq }  vs") : bi_scope.
Notation "l ↦∗□ vs" := (array l DfracDiscarded vs)
  (at level 20, format "l  ↦∗□  vs") : bi_scope.
Notation "l ↦∗{# q } vs" := (array l (DfracOwn q) vs)
  (at level 20, format "l  ↦∗{# q }  vs") : bi_scope.
Notation "l ↦∗ vs" := (array l (DfracOwn 1) vs)
  (at level 20, format "l  ↦∗  vs") : bi_scope.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦∗{#q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦∗{#q} vs) (λ q, l ↦∗{#q} vs)%I q.
Proof. split; done || apply _. Qed.

Lemma array_nil l dq : l ↦∗{dq} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l dq v : l ↦∗{dq} [v] ⊣⊢ l ↦{dq} v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l dq vs ws :
  l ↦∗{dq} (vs ++ ws) ⊣⊢ l ↦∗{dq} vs ∗ (l +ₗ length vs) ↦∗{dq} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l dq v vs : l ↦∗{dq} (v :: vs) ⊣⊢ l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l dq v vs R Q :
  Frame false R (l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q →
  Frame false R (l ↦∗{dq} (v :: vs)) Q | 2.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l dq vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{dq} vs -∗ ((l +ₗ off) ↦{dq} v ∗ ∀ v', (l +ₗ off) ↦{dq} v' -∗ l ↦∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs) as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

(** * Rules for allocation *)
Lemma mapsto_seq_array l dq v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦{dq} v) -∗
  l ↦∗{dq} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma wp_allocN s E v n Φ :
  (0 < n)%Z →
  ▷ (∀ l, l ↦∗ replicate (Z.to_nat n) v -∗ Φ (LitV $ LitLoc l)) -∗
  WP AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros (Hzs) "HΦ". iApply wp_allocN_seq; [done..|].
  iNext. iIntros (l) "Hlm". iApply "HΦ".
  by iApply mapsto_seq_array.
Qed.

Lemma wp_allocN_vec s E v n Φ :
  (0 < n)%Z →
  ▷ (∀ l, l ↦∗ vreplicate (Z.to_nat n) v -∗ Φ (#l)) -∗
  WP AllocN #n v @ s ; E; E {{ Φ }}.
Proof.
  iIntros (Hzs) "HΦ". iApply wp_allocN; [ lia | .. ].
  iNext. iIntros (l) "Hl". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

(** * Rules for accessing array elements *)
Lemma wp_load_offset s E l dq off vs v Φ :
  vs !! off = Some v →
  l ↦∗{dq} vs -∗
  ▷ (l ↦∗{dq} vs -∗ Φ v) -∗
  WP ! #(l +ₗ off) @ s; E; E {{ Φ }}.
Proof.
  iIntros (Hlookup) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_load with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) Φ :
  l ↦∗{dq} vs -∗
  ▷ (l ↦∗{dq} vs -∗ Φ (vs !!! off)) -∗
  WP ! #(l +ₗ off) @ s; E; E {{ Φ }}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma wp_store_offset s E l off vs v Φ :
  is_Some (vs !! off) →
  l ↦∗ vs -∗
  ▷ (l ↦∗ <[off:=v]> vs -∗ Φ #()) -∗
  WP #(l +ₗ off) <- v @ s; E; E {{ Φ }}.
Proof.
  iIntros ([w Hlookup]) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_store with "Hl1"). iIntros "!> Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v Φ :
  l ↦∗ vs -∗
  ▷ (l ↦∗ vinsert off v vs -∗ Φ #()) -∗
  WP #(l +ₗ off) <- v @ s; E; E {{ Φ }}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

End lifting.

Typeclasses Opaque array.
