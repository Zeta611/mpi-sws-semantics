From iris Require Import prelude.
From stdpp Require Import gmap.
From semantics.systemf_mu_state Require Import lang notation parallel_subst execution tactics logrel .

(** Proving safety of MutBit *)

Definition mutbit_t : type :=
  (Unit → Unit) × (Unit → Bool).

Definition mymutbit : expr :=
  let: "x" := new #0 in
  ((λ: "y", "x" <- #1 - (! "x")),
   (λ: "y", #0 < (! "x"))).

Definition mymutbit_instrumented : expr :=
  let: "x" := new #0 in
  ((λ: "y", assert ((!"x" = #0) || (!"x" = #1));;
            "x" <- #1 - (! "x")),
   (λ: "y", assert ((!"x" = #0) || (!"x" = #1));;
            #0 < !"x")).

(** For the semantic proof, we will get [red_nsteps] assumptions from the expression relation.
  For deterministic steps that don't access the heap, we can directly invert them and know how
  the reduction must look.
  [invert_det_step] tries to do that for a [red_nsteps] assumption as long as possible.
 *)
Ltac invert_det_step Hred :=
  eapply det_step_red in Hred as (? & Hred); [ simpl in Hred | do_det_step].
Ltac invert_det_steps Hred := repeat invert_det_step Hred; simpl in Hred.

Lemma mymutbit_instrumented_safe k W :
  ℰ mutbit_t δ_any k W mymutbit_instrumented.
Proof.
  simp type_interp. intros e2 h1 h2 W2 n1 Hincl1 Hsat1 ? Hred.
  eapply (red_nsteps_fill [AppRCtx _]) in Hred as (n2 & e3 & h3 & ? & Hred_new & Hred).
  eapply new_nsteps_inv in Hred_new as (-> & Hred_new); last done.
  eapply new_step_inv in Hred_new as (l & -> & Heq & ?); last done. subst h3.
  simpl in Hred.
  invert_det_steps Hred.
  eapply nsteps_val_inv' in Hred as (? & -> & ->); last done.

  set (INV := (λ σ : heap, σ = <[l:=#0]> ∅ ∨ σ = <[l:=#1]> ∅)).
  eexists _, (INV :: W2). split; first done.
  split. { eapply suffix_cons_r; reflexivity. }
  split.
  { simpl. eexists (<[ l := #0 ]> ∅). split; first by left.
    rewrite -delete_difference init_heap_singleton.
    split.
    - apply insert_mono. apply map_empty_subseteq.
    - rewrite map_difference_empty. rewrite delete_insert; done.
  }
  unfold mutbit_t.
  simp type_interp. eexists _, _. split; first done. split.
  - (* flip *)
    simp type_interp. eexists _, _. split; first done. split; first done.
    intros v1 kd1 W3 Hincl2 Hv1. simpl.
    simp type_interp. intros e3 h3 h4 W4 n3 Hincl3 Hsat3 ? Hred.
    eapply (red_nsteps_fill [BinOpLCtx _ (LitV _);IfCtx _ _; IfCtx _ _; AppRCtx _]) in Hred as (n4 & e4 & h5 & ? & Hred_load & Hred).
    eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #0 ∨ v = #1)) in Hred_load; [ | done | ].
    2: {
      eapply wsat_wext in Hsat3.
      2: { etrans; last apply Hincl3. apply Hincl2. }
      simpl in Hsat3. destruct Hsat3 as (σ0 & Heq & Hincl & _).
      destruct Heq as [-> | ->].
      - exists #0. split; last eauto.
        eapply lookup_weaken; last done. apply lookup_insert.
      - exists #1. split; last eauto.
        eapply lookup_weaken; last done. apply lookup_insert.
    }
    destruct Hred_load as (v' & -> & -> & -> & ? & Hv').

    destruct Hv' as [-> | ->].
    + invert_det_steps Hred.
      eapply (red_nsteps_fill [BinOpRCtx _ _; StoreRCtx _]) in Hred as (n5 & e5 & h6 & ? & Hload & Hred).
      eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #0)) in Hload; [ | done | ].
      destruct Hload as (v' & -> & -> & -> & _ & ->). 2: { eauto. }
      invert_det_steps Hred.
      eapply store_nsteps_inv' in Hred as (? & -> & ->); [ |  done | done | done ].
      eexists _, W4. split_and!; [done | done | | simp type_interp; eauto].
      specialize (wext_lookup _ _ 0 INV Hincl2 ltac:(done)) as (i' & Hlook').
      specialize (wext_lookup _ _ _ _ Hincl3 Hlook') as (? & ?).
      eapply wsat_update; [done | done | ].
      intros h [-> | ->]; (split; [rewrite lookup_insert; eauto | ]).
      all: rewrite insert_insert; subst INV; simpl; eauto.
    + invert_det_steps Hred.
      eapply (red_nsteps_fill [BinOpLCtx _ (LitV _); IfCtx _ _; AppRCtx _]) in Hred as (n5 & e5 & h6 & ? & Hload & Hred).
      eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #1)) in Hload; [ | done | ].
      destruct Hload as (v' & -> & -> & -> & _ & ->). 2: { eauto. }
      simpl in Hred.
      invert_det_steps Hred.
      eapply (red_nsteps_fill [BinOpRCtx _ _; StoreRCtx _]) in Hred as (n5 & e5 & h6 & ? & Hload & Hred).
      eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #1)) in Hload; [ | done | ].
      destruct Hload as (v' & -> & -> & -> & _ & ->). 2: { eauto. }
      invert_det_steps Hred.
      eapply store_nsteps_inv' in Hred as (? & -> & ->); [ |  done | done | done ].
      eexists _, W4. split_and!; [done | done | | simp type_interp; eauto].
      specialize (wext_lookup _ _ 0 INV Hincl2 ltac:(done)) as (i' & Hlook').
      specialize (wext_lookup _ _ _ _ Hincl3 Hlook') as (? & ?).
      eapply wsat_update; [done | done | ].
      intros h [-> | ->]; (split; [rewrite lookup_insert; eauto | ]).
      all: rewrite insert_insert; subst INV; simpl; eauto.
  - (* get *)
    simp type_interp. eexists _, _. split; first done. split; first done.
    intros v1 kd1 W3 Hincl2 Hv1. simpl.
    simp type_interp. intros e3 h3 h4 W4 n3 Hincl3 Hsat3 ? Hred.
    eapply (red_nsteps_fill [BinOpLCtx _ (LitV _);IfCtx _ _; IfCtx _ _; AppRCtx _]) in Hred as (n4 & e4 & h5 & ? & Hred_load & Hred).
    eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #0 ∨ v = #1)) in Hred_load; [ | done | ].
    2: {
      eapply wsat_wext in Hsat3.
      2: { etrans; last apply Hincl3. apply Hincl2. }
      simpl in Hsat3. destruct Hsat3 as (σ0 & Heq & Hincl & _).
      destruct Heq as [-> | ->].
      - exists #0. split; last eauto.
        eapply lookup_weaken; last done. apply lookup_insert.
      - exists #1. split; last eauto.
        eapply lookup_weaken; last done. apply lookup_insert.
    }
    destruct Hred_load as (v' & -> & -> & -> & ? & Hv').

    destruct Hv' as [-> | ->].
    + invert_det_steps Hred.
      eapply (red_nsteps_fill [BinOpRCtx _ _]) in Hred as (n5 & e5 & h6 & ? & Hload & Hred).
      eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #0)) in Hload; [ | done | ].
      destruct Hload as (v' & -> & -> & -> & _ & ->). 2: { eauto. }
      invert_det_steps Hred.
      eapply nsteps_val_inv' in Hred as (? & -> & ->); last done.
      eexists _, W4. split_and!; [done | done | done | simp type_interp; eauto].
    + invert_det_steps Hred.
      eapply (red_nsteps_fill [BinOpLCtx _ (LitV _); IfCtx _ _; AppRCtx _]) in Hred as (n5 & e5 & h6 & ? & Hload & Hred).
      eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #1)) in Hload; [ | done | ].
      destruct Hload as (v' & -> & -> & -> & _ & ->). 2: { eauto. }
      simpl in Hred. invert_det_steps Hred.
      eapply (red_nsteps_fill [BinOpRCtx _ _]) in Hred as (n5 & e5 & h6 & ? & Hload & Hred).
      eapply (load_nsteps_inv' _ _ _ _ _ _ (λ v, v = #1)) in Hload; [ | done | ].
      destruct Hload as (v' & -> & -> & -> & _ & ->). 2: { eauto. }
      invert_det_steps Hred.
      eapply nsteps_val_inv' in Hred as (? & -> & ->); last done.
      eexists _, W4. split_and!; [done | done | done | simp type_interp; eauto].
Qed.
