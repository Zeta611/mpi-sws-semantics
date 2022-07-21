From iris.program_logic Require Import language ectx_language.
From iris.heap_lang Require Export lang notation tactics.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From semantics.axiomatic Require Export invariant_lib fupd.
From semantics.axiomatic.program_logic Require Export notation.
From semantics.axiomatic.heap_lang Require Import adequacy.
From semantics.axiomatic.heap_lang Require Export proofmode.
From iris Require Import prelude.


Class reloc_preGS Σ := RelocPreGS {
  reloc_preGS_heapG :> heapGpreS Σ;
  reloc_preGS_sheapG :> ghost_mapG Σ loc (option val);
  reloc_preGS_sexprG :> ghost_varG Σ expr;
}.

Class relocGS Σ := RelocGS {
  relocGS_heapG :> heapGS Σ;
  relocGS_sheapG :> ghost_mapG Σ loc (option val);
  relocGS_sexprG :> ghost_varG Σ expr;
  relocGS_sexpr_name : gname;
  relocGS_sheap_name : gname;
}.

Definition relocΣ : gFunctors := #[heapΣ; ghost_mapΣ loc (option val); ghost_varΣ expr].
Global Instance subG_relocΣ Σ : subG relocΣ Σ → reloc_preGS Σ.
Proof. solve_inG. Qed.

Section definitionsS.
  Context `{relocGS Σ}.
  Notation ename := relocGS_sexpr_name.
  Notation hname := relocGS_sheap_name.

  Definition heapS_pointsto_def (l : loc) (v : val) := ghost_map_elem hname l (DfracOwn 1) (Some v).
  Definition heapS_pointsto_aux : seal (@heapS_pointsto_def). Proof. by eexists. Qed.
  Definition heapS_pointsto := heapS_pointsto_aux.(unseal).
  Definition heapS_pointsto_eq : @heapS_pointsto = @heapS_pointsto_def := heapS_pointsto_aux.(seal_eq).

  Definition exprS_def (e : expr) := ghost_var ename (1/2)%Qp e.
  Definition exprS_aux : seal (@exprS_def). Proof. by eexists. Qed.
  Definition exprS := exprS_aux.(unseal).
  Definition exprS_eq : @exprS = @exprS_def := exprS_aux.(seal_eq).

  Definition heapS_auth_def (σ : gmap loc (option val)) := ghost_map_auth hname 1 σ.
  Definition heapS_auth_aux : seal (@heapS_auth_def). Proof. by eexists. Qed.
  Definition heapS_auth := heapS_auth_aux.(unseal).
  Definition heapS_auth_eq : @heapS_auth = @heapS_auth_def := heapS_auth_aux.(seal_eq).

  Global Instance heapS_pointsto_timeless l v : Timeless (heapS_pointsto l v).
  Proof. rewrite heapS_pointsto_eq. apply _. Qed.
  Global Instance heapS_auth_timeless σ : Timeless (heapS_auth σ).
  Proof. rewrite heapS_auth_eq. apply _. Qed.
  Global Instance exprS_timeless e: Timeless (exprS e).
  Proof. rewrite exprS_eq. apply _. Qed.
End definitionsS.

Notation "l ↦ₛ v" := (heapS_pointsto l v) (at level 20) : bi_scope.

Section pointsto.
  Context `{relocGS Σ}.

  Lemma pointstoS_agree l v1 v2 : l ↦ₛ v1 -∗ l ↦ₛ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    rewrite !heapS_pointsto_eq !/heapS_pointsto_def.
    iIntros "H1 H2". iPoseProof (ghost_map_elem_agree with "H1 H2") as "%Ha".
    by injection Ha as ->.
  Qed.

  Lemma heapS_lookup l v σ :
    heapS_auth σ -∗ l ↦ₛ v -∗ ⌜σ !! l = Some (Some v)⌝.
  Proof.
    rewrite !heapS_pointsto_eq !heapS_auth_eq.
    iApply ghost_map_lookup.
  Qed.

  Lemma heapS_insert l v σ :
    σ !! l = None →
    heapS_auth σ -∗ |==> heapS_auth (<[l := Some v]> σ) ∗ l ↦ₛ v.
  Proof.
    rewrite !heapS_pointsto_eq !heapS_auth_eq.
    iIntros (?). by iApply ghost_map_insert.
  Qed.

  Lemma heapS_update {l v} w σ :
    heapS_auth σ -∗ l ↦ₛ v -∗ |==> heapS_auth (<[l := Some w]> σ) ∗ l ↦ₛ w.
  Proof.
    rewrite !heapS_pointsto_eq !heapS_auth_eq.
    iApply ghost_map_update.
  Qed.

  Lemma heapS_delete l v σ :
    heapS_auth σ -∗ l ↦ₛ v -∗ |==> heapS_auth (delete l σ).
  Proof.
    rewrite !heapS_pointsto_eq !heapS_auth_eq.
    iApply ghost_map_delete.
  Qed.
End pointsto.

Section expr.
  Context `{relocGS Σ}.

  Lemma exprS_agree e1 e2 :
    exprS e1 -∗ exprS e2 -∗ ⌜e1 = e2⌝.
  Proof.
    rewrite !exprS_eq. iApply ghost_var_agree.
  Qed.

  Lemma exprS_update {e1 e1'} e2 :
    exprS e1 -∗ exprS e1' -∗ |==> exprS e2 ∗ exprS e2.
  Proof.
    rewrite !exprS_eq /exprS_def. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %->.
    by iMod (ghost_var_update_halves e2 with "H1 H2") as "[$ $]".
  Qed.
End expr.
