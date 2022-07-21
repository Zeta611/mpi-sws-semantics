From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Export tactics.
From iris.heap_lang Require Import notation.
From semantics.axiomatic.heap_lang Require Export derived_laws.
From semantics.axiomatic.program_logic Require Export notation.
From iris.prelude Require Import options.
Import uPred.

Lemma tac_wp_expr_eval `{!heapGS Σ} Δ s E1 E2 Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E1; E2 {{ Φ }}) → envs_entails Δ (WP e @ s; E1; E2 {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

Lemma tac_wp_pure `{!heapGS Σ} Δ Δ' s E1 E2 K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E1; E2 {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E1; E2 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.

Lemma tac_wp_value_nofupd `{!heapGS Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_value. Qed.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 (Val _) _) =>
      eapply tac_wp_value_nofupd
  end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ _ K e');
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

(* will spawn an evar for [E2] *)
Lemma tac_wp_bind `{!heapGS Σ} K Δ s E1 E2 E3 Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E1; E2 {{ v, WP f (Val v) @ s; E2; E3 {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E1; E3 {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

(* don't change masks for bound expression *)
Lemma tac_wp_bind_nomask `{!heapGS Σ} K Δ s E1 E2 Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E1; E1 {{ v, WP f (Val v) @ s; E1; E2 {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E1; E2 {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind_nomask K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

Ltac wp_bind_core' K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind'" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core' K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma wand_apply' (P R Q : iProp Σ) :
  (P -∗ R) →
  (R -∗ Q) →
  P -∗ Q.
Proof.
  intros Ha Hb. iIntros "HP". iApply Hb. iApply Ha. done.
Qed.

Lemma tac_wp_allocN Δ Δ' s E1 E2 j K v n Φ :
  (0 < n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E1; E2 {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E1; E2 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? ? HΔ.
  rewrite -wp_bind. eapply wand_apply'; last exact: wp_allocN.
  rewrite into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite right_id wand_elim_r.
Qed.

Lemma tac_wp_alloc Δ Δ' s E1 E2 j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦ v)) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E1; E2 {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E1; E2 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ.
  rewrite -wp_bind. eapply wand_apply'; last exact: wp_alloc.
  rewrite into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite right_id wand_elim_r.
Qed.

Lemma tac_wp_free Δ Δ' s E1 E2 i K l v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  (let Δ'' := envs_delete false i false Δ' in
   envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E1; E2 {{ Φ }})) →
  envs_entails Δ (WP fill K (Free (LitV l)) @ s; E1; E2 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? Hlk Hfin.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_free.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk).
  by apply later_mono, sep_mono_r.
Qed.

Lemma tac_wp_load Δ Δ' s E1 E2 i K b l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E1; E2 {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E1; E2 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' s E1 E2 i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E1; E2 {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E1; E2 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [iSolveTC
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac|iSolveTC
         |finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_free" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_free: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_free _ _ _ _ _ _ K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [iSolveTC
    |solve_mapsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E1 ?E2 ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
