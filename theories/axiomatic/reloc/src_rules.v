From iris.program_logic Require Import language ectx_language.
From iris.heap_lang Require Export lang notation tactics.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From semantics.axiomatic Require Export invariant_lib.
From semantics.axiomatic.program_logic Require Export notation.
From semantics.axiomatic.reloc Require Export ghost_state.
From iris Require Import prelude.

(** ** Source update rules *)

Implicit Types (e : expr) (v w : val).
Implicit Types (l : loc).

(** Iris's language interface supports concurrency and other things we currently do not care about, hence [prim_step] is more general than we need it to be.
  We define [thread_step] as the notion of steps by our single thread.
*)

Definition thread_step : (expr * state) → (expr * state) → Prop := λ '(e1, σ1) '(e2, σ2), prim_step e1 σ1 [] e2 σ2 [].

Lemma prim_thread_step e1 σ1 e2 σ2 :
  prim_step e1 σ1 [] e2 σ2 [] → thread_step (e1, σ1) (e2, σ2).
Proof. done. Qed.
Lemma pure_thread_step e1 e2 σ :
  pure_step e1 e2 → thread_step (e1, σ) (e2, σ).
Proof.
  intros [H1 H2].
  destruct (H1 σ) as (e2' & σ2' & efs & Hprim).
  specialize (H2 _ _ _ _ _ Hprim) as (_ & -> & -> & ->).
  done.
Qed.

Lemma fill_thread_step e1 e2 K σ1 σ2 :
  thread_step (e1, σ1) (e2, σ2) → thread_step (fill K e1, σ1) (fill K e2, σ2).
Proof.
  rewrite /thread_step.
  intros. by apply fill_prim_step.
Qed.
Lemma rtc_fill_thread_step e1 e2 K σ1 σ2 :
  rtc thread_step (e1, σ1) (e2, σ2) → rtc thread_step (fill K e1, σ1) (fill K e2, σ2).
Proof.
  intros Hstep.
  remember (e1, σ1) as c1 eqn:Hc1.
  remember (e2, σ2) as c2 eqn:Hc2.
  revert e1 σ1 e2 σ2 Hc1 Hc2.
  induction Hstep as [ | ? [e0 σ0] ? ?? IH]; intros; subst.
  - injection Hc2; intros; subst. done.
  - etrans.
    + apply rtc_once. by apply fill_thread_step.
    + by apply IH.
Qed.

(** Namespaces *)
Definition relocN := nroot .@ "reloc".
(* for the source invariant *)
Definition srcN := relocN .@ "src".
(* for the location invariants in the logrel *)
Definition logN := relocN .@ "log".

(** Interaction lemmas for the ghost theories *)
Check pointstoS_agree.
Check heapS_lookup.
Check heapS_insert.
Check heapS_update.
Check heapS_delete.

Check exprS_agree.
Check exprS_update.

(** Note that relocGS fixes the two ghost names for [exprS] and [heapS] *)

(** We define the invariant *)
Section invariant.
  (** [relocGS] contains all the ghost state we need, as well as the ghost names γheap and γexpr. *)
  Context `{relocGS Σ}.

  (** Iris's default language, HeapLang, supports some state in addition to the heap. We don't care abou that. *)
  Definition mkstate (σ : gmap loc (option val)) :=
    {| heap := σ; used_proph_id := ∅ |}.
  (** The main invariant *)
  Definition src_inv e0 σ0 : iProp Σ :=
    (∃ e σ, exprS e ∗ heapS_auth σ ∗ ⌜rtc thread_step (e0, mkstate σ0) (e, mkstate σ)⌝).
  (** Since we should carry around that invariant all the time, and we don't care about the initial state the invariant is parameterized is over most of the time, we define the (persistent) [src_ctx] for convenience.
    We just need to thread this through everywhere.
  *)
  Definition src_ctx : iProp Σ :=
    (∃ e0 σ0, inv srcN (src_inv e0 σ0))%I.

  Global Instance src_ctx_persistent : Persistent src_ctx.
  Proof. apply _. Qed.
End invariant.

(** Steps for advancing the program *)
Section rules.
  Context `{relocGS Σ}.

  (** This mirrors the two-step proof in the lecture notes *)
  Lemma src_step_pure_explicit_1 (R : iProp Σ) `{!Timeless R} E K e1 e2 :
    ↑srcN ⊆ E →
    (R ∗ exprS (fill K e1) ⊢ |==> exprS (fill K e2) ∗ R) →
    inv srcN R -∗
    exprS (fill K e1) -∗ |={E}=> exprS (fill K e2).
  Proof.
    iIntros (? Hupd) "#Hinv Hsrc".
    iPoseProof (fupd_inv_open _ E with "Hinv") as "-#Hop"; first done.
    iApply fupd_trans. iApply (fupd_wand with "Hop").
    iIntros "(Hinv' & Hclose)".
    iApply (fupd_trans _ (E ∖ ↑srcN)).
    iPoseProof (fupd_timeless with "Hinv'") as "Hinv'".
    iApply (fupd_wand with "Hinv'").
    iIntros "HR".

    iApply fupd_trans. iApply bupd_fupd.
    iMod (Hupd with "[$HR $Hsrc]") as "[Hsrc HR]".
    iModIntro.
    iSpecialize ("Hclose" with "HR").
    iApply (fupd_wand with "Hclose").
    iIntros "_". done.
  Qed.

  (** We can also prove it with the IPM support for fancy updates. *)
  Lemma src_step_pure_explicit_1_ipm (R : iProp Σ) `{!Timeless R} E K e1 e2 :
    ↑srcN ⊆ E →
    (R ∗ exprS (fill K e1) ⊢ |==> exprS (fill K e2) ∗ R) →
    inv srcN R -∗
    exprS (fill K e1) -∗ |={E}=> exprS (fill K e2).
  Proof.
    iIntros (? Hupd) "#Hinv Hsrc".
    iMod (fupd_inv_open with "Hinv") as "(>HR & Hclose)"; first done.
    iMod (Hupd with "[$HR $Hsrc]") as "[$ HR]".
    iMod ("Hclose" with "HR"); done.
  Qed.

  (** With our particular choice of invariant, the above lemma allows to prove the desired update. *)
  Lemma src_step_pure_explicit_2 e1 e2 K E :
    pure_step e1 e2 →
    ↑srcN ⊆ E →
    src_ctx -∗
    exprS (fill K e1) ={E}=∗ exprS (fill K e2).
  Proof.
    iIntros (Hpure ?) "(%e0 & %σ0 & Hinv) Hsrc".
    iApply (src_step_pure_explicit_1 with "Hinv Hsrc"); first done.
    iIntros "[(%e1' & %σ & He1' & Hauth & %Hstep) Hsrc]".
    iDestruct (exprS_agree with "He1' Hsrc") as %->.
    iMod (exprS_update (fill K e2) with "Hsrc He1'") as "(Hsrc & He2)".
    iModIntro; iFrame "Hsrc".
    iExists (fill K e2), σ. iFrame.
    iPureIntro. etrans; first done.
    apply rtc_fill_thread_step.
    apply rtc_once. by apply pure_thread_step.
  Qed.

  (** We can also just prove it all in one go, using the IPM. *)
  Lemma src_step_pure e1 e2 K E :
    pure_step e1 e2 →
    ↑srcN ⊆ E →
    src_ctx -∗
    exprS (fill K e1) ={E}=∗ exprS (fill K e2).
  Proof.
    iIntros (Hpure ?) "(%e0 & %σ0 & Hinv) Hsrc".
    iInv "Hinv" as "(%e1' & %σ & >He1' & >Hauth & >%Hstep)" "Hclose".
    iDestruct (exprS_agree with "He1' Hsrc") as %->.
    iMod (exprS_update (fill K e2) with "Hsrc He1'") as "(Hsrc & He2)".
    iMod ("Hclose" with "[Hauth He2]"); last by iFrame.
    iNext. iExists (fill K e2), σ. iFrame.
    iPureIntro. etrans; first done.
    apply rtc_fill_thread_step.
    apply rtc_once. by apply pure_thread_step.
  Qed.

  (** We lift this to multiple steps of execution, using the [PureExec] typeclass to make it
    compatible with the proofmode. You don't need to understand this in detail. *)
  Lemma src_step_pures (ϕ : Prop) n e1 e2 K E :
    ϕ →
    PureExec ϕ n e1 e2 →
    ↑srcN ⊆ E →
    src_ctx -∗
    exprS (fill K e1) ={E}=∗ exprS (fill K e2).
  Proof.
    iIntros (phi Hpure ?) "#CTX Hsrc".
    unfold PureExec in Hpure. specialize (Hpure phi).
    iInduction Hpure as [ | n] "IH"; first done.
    iMod (src_step_pure with "CTX Hsrc") as "Hsrc"; [done.. | ].
    by iApply "IH".
  Qed.

  (** Now it's your turn! *)
  (** For the following execution lemmas, you will find the following lemmas helpful:
    - prim_thread_step
    - fill_prim_step
    - head_prim_step
  *)

  Lemma src_step_load E K l v :
    ↑srcN ⊆ E →
    src_ctx -∗
    exprS (fill K (! #l)) -∗
    l ↦ₛ v ={E}=∗
    exprS (fill K v) ∗
    l ↦ₛ v.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma src_step_store E K l v w :
    ↑srcN ⊆ E →
    src_ctx -∗
    exprS (fill K (#l <- w)) -∗
    l ↦ₛ v ={E}=∗
    exprS (fill K #()) ∗
    l ↦ₛ w.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma src_step_alloc E K v :
    ↑srcN ⊆ E →
    src_ctx -∗
    exprS (fill K (ref v)) ={E}=∗
    ∃ l : loc,
    exprS (fill K #l) ∗
    l ↦ₛ v.
  Proof.
    (** 
    You will find the following lemmas relating to memory allocation helpful:
    - alloc_fresh
    - state_init_heap_singleton
    - fresh_locs_fresh
    - not_elem_of_dom
    - loc_add_0_l
     *)
    (* FIXME *)
  Admitted.
End rules.
