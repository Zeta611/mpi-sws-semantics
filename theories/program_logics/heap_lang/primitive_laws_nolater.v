From stdpp Require Import fin_maps.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From semantics.pl.heap_lang Require Export primitive_laws derived_laws.
From iris.base_logic.lib Require Export gen_heap gen_inv_heap.
From semantics.pl.program_logic Require Export sequential_wp.
From semantics.pl.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export class_instances.
From iris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

Section lifting.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Heap *)
Lemma wp_allocN_seq s E v n Φ :
  (0 < n)%Z →
  (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v) -∗ Φ (LitV $ LitLoc l)) -∗
  WP AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ". iApply wp_allocN_seq; done.
Qed.

Lemma wp_alloc s E v Φ :
  (∀ l, l ↦ v -∗ Φ (LitV $ LitLoc l)) -∗
  WP Alloc (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros "HΦ". by iApply wp_alloc.
Qed.

Lemma wp_free s E l v Φ :
  l ↦ v -∗
  (Φ (LitV LitUnit)) -∗
  WP Free (Val $ LitV $ LitLoc l) @ s; E; E {{ Φ }}.
Proof.
  iIntros "Hl HΦ". iApply (wp_free with "Hl HΦ").
Qed.

Lemma wp_load s E l dq v Φ :
  l ↦{dq} v -∗
  (l ↦{dq} v -∗ Φ v) -∗
  WP Load (Val $ LitV $ LitLoc l) @ s; E; E {{ Φ }}.
Proof.
  iIntros "Hl HΦ". iApply (wp_load with "Hl HΦ").
Qed.

Lemma wp_store s E l v' v Φ :
  l ↦ v' -∗
  (l ↦ v -∗ Φ (LitV LitUnit)) -∗
  WP Store (Val $ LitV $ LitLoc l) (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros "Hl HΦ".
  iApply (wp_store with "Hl HΦ").
Qed.


(*** Derived *)
Lemma wp_allocN s E v n Φ :
  (0 < n)%Z →
  (∀ l, l ↦∗ replicate (Z.to_nat n) v -∗ Φ (LitV $ LitLoc l)) -∗
  WP AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E; E {{ Φ }}.
Proof.
  iIntros. by iApply wp_allocN.
Qed.

Lemma wp_allocN_vec s E v n Φ :
  (0 < n)%Z →
  (∀ l, l ↦∗ vreplicate (Z.to_nat n) v -∗ Φ (#l)) -∗
  WP AllocN #n v @ s ; E; E {{ Φ }}.
Proof.
  iIntros. by iApply wp_allocN_vec.
Qed.

(** * Rules for accessing array elements *)
Lemma wp_load_offset s E l dq (off : nat) vs v Φ :
  vs !! off = Some v →
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ Φ v) -∗
  WP ! #(l +ₗ off) @ s; E; E {{ Φ }}.
Proof.
  iIntros (?) "Hl HΦ". by iApply (wp_load_offset with "Hl HΦ").
Qed.

Lemma wp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) Φ :
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ Φ (vs !!! off)) -∗
  WP ! #(l +ₗ off) @ s; E; E {{ Φ }}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma wp_store_offset s E l (off : nat) vs v Φ :
  is_Some (vs !! off) →
  l ↦∗ vs -∗
  (l ↦∗ <[off:=v]> vs -∗ Φ #()) -∗
  WP #(l +ₗ off) <- v @ s; E; E {{ Φ }}.
Proof.
  iIntros (?) "Hl HΦ". by iApply (wp_store_offset with "Hl HΦ").
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v Φ :
  l ↦∗ vs -∗
  (l ↦∗ vinsert off v vs -∗ Φ #()) -∗
  WP #(l +ₗ off) <- v @ s; E; E {{ Φ }}.
Proof.
  iIntros "Hl HΦ". by iApply (wp_store_offset_vec with "Hl HΦ").
Qed.
End lifting.
