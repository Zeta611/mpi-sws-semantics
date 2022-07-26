(** Adapted from https://gitlab.mpi-sws.org/iris/reloc/-/blob/master/theories/logic/proofmode/spec_tactics.v *)
From iris.program_logic Require Import language ectx_language.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Export lang notation tactics.
From semantics.pl.reloc Require Import ghost_state logrel.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From semantics.pl.heap_lang Require Import primitive_laws.
From iris Require Import prelude.


Lemma tac_src_bind_gen `{relocGS Σ} Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, src_expr e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (src_expr e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_src_bind `{relocGS Σ} e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, src_expr e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (src_expr (fill K' e'))) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof. intros. by eapply tac_src_bind_gen. Qed.

Ltac src_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Tactic Notation "src_normalise" :=
  iStartProof;
  eapply (tac_src_bind_gen);
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "src_bind" open_constr(efoc) :=
  iStartProof;
  eapply (tac_src_bind efoc);
    [iAssumptionCore (* prove the lookup *)
    |src_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].

Lemma src_expr_step_pure `{relocGS Σ} (ϕ : Prop) n e1 e2 K E :
  ϕ →
  PureExec ϕ n e1 e2 →
  ↑srcN ⊆ E →
  src_expr (fill K e1) ={E}=∗ src_expr (fill K e2).
Proof.
  iIntros (Hphi Hpure ?) "(#CTX & Hs)".
  iFrame "CTX". by iApply src_step_pures.
Qed.

Lemma tac_src_pure `{relocGS Σ} e K' e1 e2 Δ1 E1 i1 e' ϕ ψ Q n :
  (* we have those premises first, because we will be trying to solve them
     with backtracking using reashape_expr; see the accompanying Ltac.
     the first premise decomposes the expression, the second one checks
     that we can make a pure step *)
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  ↑ srcN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, src_expr e)%I →
  ψ →
  ϕ →
  (* we will call simpl on this goal thus re-composing the expression again *)
  e' = fill K' e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (src_expr e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros -> Hpure ?? HΔ1 Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite src_expr_step_pure; [ | done..].
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "src_pure" open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (src_expr (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_src_pure (fill K' e) (K++K') e');
      [by rewrite ?fill_app | iSolveTC | ..])
  end;
  [iSolveTC || fail "src_pure: cannot eliminate modality in the goal"
  |solve_ndisj || fail "src_pure: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "src_pure: cannot find the RHS"
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity) (* ϕ *)
  |simpl; reflexivity ||  fail "src_pure: this should not happen" (* e' = fill K' e2 *)
  |pm_reduce (* new goal *)].


Tactic Notation "src_pures" := repeat (src_pure _).
Tactic Notation "src_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  src_pure (App _ _);
  clear H.
Tactic Notation "src_seq" := src_rec.
Tactic Notation "src_let" := src_rec.
Tactic Notation "src_lam" := src_rec.
Tactic Notation "src_fst" := src_pure (Fst (PairV _ _)).
Tactic Notation "src_snd" := src_pure (Snd (PairV _ _)).
Tactic Notation "src_proj" := src_pure (_ (PairV _ _)).
Tactic Notation "src_case_inl" := src_pure (Case (InjLV _) _ _).
Tactic Notation "src_case_inr" := src_pure (Case (InjRV _) _ _).
Tactic Notation "src_case" := src_pure (Case _ _ _).
Tactic Notation "src_binop" := src_pure (BinOp _ _ _).
Tactic Notation "src_op" := src_binop.
Tactic Notation "src_if_true" := src_pure (If #true _ _).
Tactic Notation "src_if_false" := src_pure (If #false _ _).
Tactic Notation "src_if" := src_pure (If _ _ _).
Tactic Notation "src_pair" := src_pure (Pair _ _).
Tactic Notation "src_closure" := src_pure (Rec _ _ _).

Lemma src_expr_step_store `{relocGS Σ} (v : val) (l : loc) v' K E :
  ↑srcN ⊆ E →
  src_expr (fill K (#l <- v)) ∗ l ↦ₛ v' ={E}=∗
  src_expr (fill K #()) ∗ l ↦ₛ v.
Proof.
  iIntros (?) "([#CTX Hs] & Hl)".
  iFrame "CTX". by iApply (src_step_store with "CTX Hs Hl").
Qed.

Lemma tac_src_store `{relocGS Σ} Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  ↑srcN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, src_expr e, Δ2)%I →
  e = fill K' (Store (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  e2 = fill K' #() →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (src_expr e2)) i2 (l ↦ₛ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- -> ? HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. rewrite /src_expr.
  rewrite !assoc.
  rewrite src_expr_step_store //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I). simpl.
  rewrite assoc.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "src_store" :=
  iStartProof;
  eapply (tac_src_store);
  [iSolveTC || fail "src_store: cannot eliminate modality in the goal"
  |solve_ndisj || fail "src_store: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "src_store: cannot find RHS"
  |src_bind_helper
  |iSolveTC || fail "src_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "src_store: this should not happen"
  |iAssumptionCore || fail "src_store: cannot find '? ↦ₛ ?'"
  |pm_reduce (* new goal *)].


Lemma src_expr_step_load `{relocGS Σ} (v : val) (l : loc) K E :
  ↑srcN ⊆ E →
  src_expr (fill K (!#l)) ∗ l ↦ₛ v ={E}=∗
  src_expr (fill K v) ∗ l ↦ₛ v.
Proof.
  iIntros (?) "([#CTX Hs] & Hl)".
  iFrame "CTX". by iApply (src_step_load with "CTX Hs Hl").
Qed.

Lemma tac_src_load `{relocGS Σ} Δ1 Δ2 E1 i1 i2 K' e e2 (l : loc) v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  ↑srcN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, src_expr e, Δ2)%I →
  e = fill K' (Load #l) →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v)%I →
  e2 = fill K' (of_val v) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (src_expr e2)) i2 (l ↦ₛ v)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite assoc.
  rewrite src_expr_step_load /= //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I).
  rewrite assoc.
  rewrite -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "src_load" :=
  iStartProof;
  eapply (tac_src_load);
  [iSolveTC || fail "src_load: cannot eliminate modality in the goal"
  |solve_ndisj || fail "src_load: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "src_load: cannot find the RHS"
  |src_bind_helper
  |iAssumptionCore || fail "src_load: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "src_load: this should not happen"
  |pm_reduce (* new goal *)].

Lemma src_expr_step_alloc `{relocGS Σ} E K (v : val) :
  ↑srcN ⊆ E →
  src_expr (fill K (ref v)) ={E}=∗ ∃ l : loc, src_expr (fill K (#l)) ∗ l ↦ₛ v.
Proof.
  iIntros (?) "[#CTX Hs]".
  iFrame "CTX". by iApply (src_step_alloc with "CTX Hs").
Qed.

Lemma tac_src_alloc `{relocGS Σ} Δ1 E1 i1 K' e e' v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  ↑srcN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, src_expr e)%I →
  e = fill K' (ref e') →
  IntoVal e' v →
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (src_expr (fill K' #l))) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ₛ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  rewrite src_expr_step_alloc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r, bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  rewrite (comm _ _ (l ↦ₛ _)%I).
  rewrite assoc.
  (*rewrite (comm _ _ (l ↦ₛ _)%I).*)
  rewrite -(assoc _ (l ↦ₛ _)%I src_ctx _). rewrite -assoc.
  rewrite bi.wand_elim_r.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "src_alloc" ident(l) "as" constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "src_alloc:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; src_normalise) || fail 1 "src_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_src_alloc);
  [iSolveTC || fail "src_alloc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "src_alloc: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "src_alloc: cannot find the RHS"
  |src_bind_helper
  |iSolveTC || fail "src_alloc: expressions is not a value"
  |finish ()
(* new goal *)].

Tactic Notation "src_alloc" ident(l) :=
  let H := iFresh in src_alloc l as H.
