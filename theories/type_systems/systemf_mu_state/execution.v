From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf_mu_state Require Import lang notation.
(* TODO: everywhere replace the metavar σ for heaps with h *)

(** ** Deterministic reduction *)

Record det_step (e1 : expr) (e2 : expr) := {
  det_step_safe h : reducible e1 h;
  det_step_det e2' h h' :
    contextual_step (e1, h) (e2', h') → e2' = e2 ∧ h' = h
}.

Record det_base_step (e1 e2 : expr) := {
  det_base_step_safe h : base_reducible e1 h;
  det_base_step_det e2' h h' :
    base_step (e1, h) (e2', h') → e2' = e2 ∧ h' = h
}.

Lemma det_base_step_det_step e1 e2 : det_base_step e1 e2 → det_step e1 e2.
Proof.
  intros [Hp1 Hp2]. split.
  - intros h. destruct (Hp1 h) as (e2' & h' & ?).
    eexists e2', h'. by apply base_contextual_step.
  - intros e2' h h' ?%base_reducible_contextual_step; [ | done]. by eapply Hp2.
Qed.

(** *** Pure execution lemmas *)
Local Ltac inv_step :=
  repeat match goal with
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step (?e, ?σ) (?e2, ?σ2) |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.
Local Ltac solve_exec_safe := intros; subst; eexists _, _; econstructor; eauto.
Local Ltac solve_exec_detdet := simpl; intros; inv_step; try done.
Local Ltac solve_det_exec :=
  subst; intros; apply det_base_step_det_step;
    constructor; [solve_exec_safe | solve_exec_detdet].

Lemma det_step_beta x e e2 :
  is_val e2 →
  det_step (App (@Lam x e) e2) (subst' x e2 e).
Proof. solve_det_exec. Qed.

Lemma det_step_tbeta e :
  det_step ((Λ, e) <>) e.
Proof. solve_det_exec. Qed.

Lemma det_step_unpack e1 e2 x :
  is_val e1 →
  det_step (unpack (pack e1) as x in e2) (subst' x e1 e2).
Proof. solve_det_exec. Qed.

Lemma det_step_unop op e v v' :
  to_val e = Some v →
  un_op_eval op v = Some v' →
  det_step (UnOp op e) v'.
Proof. solve_det_exec. by simplify_eq. Qed.

Lemma det_step_binop op e1 v1 e2 v2 v' :
  to_val e1 = Some v1 →
  to_val e2 = Some v2 →
  bin_op_eval op v1 v2 = Some v' →
  det_step (BinOp op e1 e2) v'.
Proof. solve_det_exec. by simplify_eq. Qed.

Lemma det_step_if_true e1 e2 :
  det_step (if: #true then e1 else e2) e1.
Proof. solve_det_exec. Qed.
Lemma det_step_if_false e1 e2 :
  det_step (if: #false then e1 else e2) e2.
Proof. solve_det_exec. Qed.

Lemma det_step_fst e1 e2 :
  is_val e1 →
  is_val e2 →
  det_step (Fst (e1, e2)) e1.
Proof. solve_det_exec. Qed.
Lemma det_step_snd e1 e2 :
  is_val e1 →
  is_val e2 →
  det_step (Snd (e1, e2)) e2.
Proof. solve_det_exec. Qed.

Lemma det_step_casel e e1 e2 :
  is_val e →
  det_step (Case (InjL e) e1 e2) (e1 e).
Proof. solve_det_exec. Qed.
Lemma det_step_caser e e1 e2 :
  is_val e →
  det_step (Case (InjR e) e1 e2) (e2 e).
Proof. solve_det_exec. Qed.

Lemma det_step_unroll e :
  is_val e →
  det_step (unroll (roll e)) e.
Proof. solve_det_exec. Qed.

(** ** n-step reduction *)
(** Reduce in n steps to an irreducible expression.
    (this is ⇝^n from the lecture notes)
 *)
Definition red_nsteps (n : nat) e h e' h' := nsteps contextual_step n (e, h) (e', h') ∧ irreducible e' h'.

Lemma det_step_red e e' e'' h h'' n :
  det_step e e' →
  red_nsteps n e h e'' h'' →
  1 ≤ n ∧ red_nsteps (n - 1) e' h e'' h''.
Proof.
  intros [Hprog Hstep] Hred.
  specialize (Hprog h).
  destruct Hred as [Hred  Hirred].
  destruct n as [ | n].
  { inversion Hred; subst.
    exfalso; eapply not_reducible; done.
  }
  inversion Hred as [ | ??[e1 h1]? Hstep0]; subst. simpl.
  apply Hstep in Hstep0 as [<- <-].
  split; first lia.
  replace (n - 0) with n by lia. done.
Qed.

Lemma contextual_step_red_nsteps n e e' e'' h h' h'':
  contextual_step (e, h) (e', h') →
  red_nsteps n e' h' e'' h'' →
  red_nsteps (S n) e h e'' h''.
Proof.
  intros Hstep [Hsteps Hirred].
  split; last done.
  by econstructor.
Qed.

Lemma nsteps_val_inv n v e' h h' :
  red_nsteps n (of_val v) h e' h' → n = 0 ∧ e' = of_val v ∧ h' = h.
Proof.
  intros [Hred Hirred]; cbn in *.
  destruct n as [ | n].
  - inversion Hred; subst. done.
  - inversion Hred as [ | ??[e1 h1]]; subst. exfalso. eapply val_irreducible; last done.
    rewrite to_of_val. eauto.
Qed.

Lemma nsteps_val_inv' n v e e' h h' :
  to_val e = Some v →
  red_nsteps n e h e' h' → n = 0 ∧ e' = of_val v ∧ h' = h.
Proof. intros Ht. rewrite -(of_to_val _ _ Ht). apply nsteps_val_inv. Qed.

Lemma red_nsteps_fill K k e e' h h' :
  red_nsteps k (fill K e) h e' h' →
  ∃ j e'' h'', j ≤ k ∧
    red_nsteps j e h e'' h'' ∧
    red_nsteps (k - j) (fill K e'') h'' e' h'.
Proof.
  intros [Hsteps Hirred].
  induction k as [ | k IH] in e, e', h, h', Hsteps, Hirred |-*.
  - inversion Hsteps; subst.
    exists 0, e, h'. split_and!; [done | split | ].
    + constructor.
    + by eapply irreducible_fill.
    + done.
  - inversion Hsteps as [ | n [e1 h1] [e2 h2] [e3 h3] Hstep Hsteps' Heq1 Heq2 Heq3]. subst.
    destruct (contextual_ectx_step_case _ _ _ _ _ Hstep) as [(e'' & -> & Hstep') | Hv].
    + apply IH in Hsteps' as (j & e3 & h3 & ? & Hsteps' & Hsteps''); last done.
      eexists (S j), _, _. split_and!; [lia | | done ].
      eapply contextual_step_red_nsteps; done.
    + exists 0, e, h. split_and!; [ lia | | ].
      * split; [constructor | ].
        apply val_irreducible. by apply is_val_spec.
      * simpl. by eapply contextual_step_red_nsteps.
Qed.

(** * Heap execution lemmas *)
Lemma new_step_inv v e e' σ σ' :
  to_val e = Some v →
  base_step (New e, σ) (e', σ') →
  ∃ l, e' = (Lit $ LitLoc l) ∧ σ' = init_heap l 1 v σ ∧ σ !! l = None.
Proof.
  intros <-%of_to_val.
  inversion 1; subst.
  rewrite to_of_val in H5. injection H5 as [= ->].
  eauto.
Qed.

Lemma new_nsteps_inv n v e e' σ σ' :
  to_val e = Some v →
  red_nsteps n (New e) σ e' σ' →
  (n = 1 ∧ base_step (New e, σ) (e', σ')).
Proof.
  intros <-%of_to_val [Hsteps Hirred%not_reducible].
  inversion Hsteps; subst.
  - exfalso; apply Hirred. eapply base_reducible_reducible. eexists _, _. eapply new_fresh.
  - destruct y.
    eapply base_reducible_contextual_step in H.
    2: { eexists _, _. apply new_fresh. }
    inversion H0; subst.
    { eauto. }
    eapply new_step_inv in H; last apply to_of_val.
    destruct H as (l & -> & -> & ?).
    destruct y. apply val_stuck in H1. done.
Qed.

Lemma load_step_inv e v σ e' σ' :
  to_val e = Some v →
  base_step (Load e, σ) (e', σ') →
  ∃ (l : loc) v', v = #l ∧ σ !! l = Some v' ∧ e' = of_val v' ∧ σ' = σ.
Proof.
  intros <-%of_to_val.
  inversion 1; subst.
  symmetry in H0. apply of_val_lit in H0 as ->.
  eauto 8.
Qed.

Definition sub_redexes_are_values (e : expr) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

Lemma contextual_base_reducible e σ :
  reducible e σ → sub_redexes_are_values e → base_reducible e σ.
Proof.
  intros (e' & σ' & Hstep) ?. inversion Hstep; subst.
  assert (K = empty_ectx) as -> by eauto 10 using val_base_stuck.
  rewrite fill_empty /base_reducible; eauto.
Qed.


Ltac solve_sub_redexes_are_values :=
  let K := fresh "K" in
  let e' := fresh "e'" in
  let Heq := fresh "Heq" in
  let Hv := fresh "Hv" in
  let IH := fresh "IH" in
  let Ki := fresh "Ki" in
  let Ki' := fresh "Ki'" in
  intros K e' Heq Hv;
  destruct K as [ | Ki K]; first (done);
  exfalso; induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*;
  [destruct Ki; inversion Heq; subst; simplify_val; cbn in *; congruence
  | eapply IH; first (by rewrite Heq);
    apply fill_item_no_val; done].

Lemma load_nsteps_inv n v e e' σ σ' :
  to_val e = Some v →
  red_nsteps n (Load e) σ e' σ' →
  (n = 0 ∧ σ' = σ ∧ e' = Load e ∧ ¬ reducible (Load e) σ) ∨
  (n = 1 ∧ base_step (Load e, σ) (e', σ')).
Proof.
  intros <-%of_to_val [Hsteps Hirred%not_reducible].
  inversion Hsteps; subst.
  - by left.
  - right. destruct y.
    eapply base_reducible_contextual_step in H.
    2: { eapply contextual_base_reducible; [eexists _, _; done | solve_sub_redexes_are_values]. }
    inversion H0; subst.
    { eauto. }
    eapply load_step_inv in H as (l & ? & -> & ? & -> & ->); last apply to_of_val.
    destruct y. apply val_stuck in H1. simplify_val. done.
Qed.

(** useful derived lemma when we know upfront that l satisfies some invariant [P] *)
Lemma load_nsteps_inv' n l e e' σ σ' (P : val → Prop) :
  to_val e = Some (LitV $ LitLoc l) →
  (∃ v', σ !! l = Some v' ∧ P v') →
  red_nsteps n (Load e) σ e' σ' →
  ∃ v' : val, n = 1 ∧ e' = v' ∧ σ' = σ ∧ σ !! l = Some v' ∧ P v'.
Proof.
  intros <-%of_to_val (v' & Hlook & HP) Hred.
  eapply load_nsteps_inv in Hred; last done.
  destruct Hred as [(-> & -> & -> & Hnred) | (-> & Hstep)].
  - exfalso; eapply Hnred. eexists v', _.
    eapply base_contextual_step. econstructor. done.
  - exists v'. split; first done.
    eapply load_step_inv in Hstep; last done.
    destruct Hstep as (l' & v'' & [= <-] & ? & -> & ->).
    split; first by simplify_option_eq.
    split; last done. econstructor; done.
Qed.

Lemma store_step_inv v1 v2 σ e' σ' :
  base_step (Store (of_val v1) (of_val v2), σ) (e', σ') →
  ∃ (l : loc) v', v1 = #l ∧ σ !! l = Some v' ∧ e' = Lit LitUnit ∧ σ' = <[l := v2]> σ.
Proof.
  inversion 1; subst.
  symmetry in H0. apply of_val_lit in H0 as ->.
  simplify_val. simplify_option_eq.
  eauto 8.
Qed.

Lemma store_nsteps_inv n v1 v2 e' σ σ' :
  red_nsteps n (Store (of_val v1) (of_val v2)) σ e' σ' →
  (n = 0 ∧ σ' = σ ∧ e' = Store (of_val v1) (of_val v2) ∧ ¬ reducible (Store (of_val v1) (of_val v2)) σ) ∨
  (n = 1 ∧ base_step (Store (of_val v1) (of_val v2), σ) (e', σ')).
Proof.
  intros [Hsteps Hirred%not_reducible].
  inversion Hsteps; subst.
  - by left.
  - right. destruct y.
    eapply base_reducible_contextual_step in H.
    2: { eapply contextual_base_reducible; [eexists _, _; done | solve_sub_redexes_are_values]. }
    inversion H0; subst.
    { eauto. }
    apply store_step_inv in H as (l & ? & -> & ? & -> & ->).
    destruct y. apply val_stuck in H1. simplify_val. done.
Qed.

Lemma store_nsteps_inv' n e1 e2 v0 v l e' σ σ' :
  to_val e1 = Some (LitV $ LitLoc l) →
  to_val e2 = Some v →
  σ !! l = Some v0 →
  red_nsteps n (Store e1 e2) σ e' σ' →
  n = 1 ∧ e' = Lit $ LitUnit ∧ σ' = <[l := v ]> σ.
Proof.
  intros <-%of_to_val <-%of_to_val Hlook Hred%store_nsteps_inv.
  destruct Hred as [(-> & -> & -> & Hnred) | (-> & Hb)].
  - exfalso; eapply Hnred.
    eexists #(), _.
    eapply base_contextual_step. econstructor; [done | apply to_of_val ].
  - eapply store_step_inv in Hb. destruct Hb as (l' & v' & [= <-] & Hlook' & -> & ->).
    simplify_option_eq. done.
Qed.

(** Additionally useful stepping lemmas *)
Lemma app_step_r (e1 e2 e2': expr) h h' :
  contextual_step (e2, h) (e2', h') → contextual_step (e1 e2, h) (e1 e2', h').
Proof. by apply (fill_contextual_step [AppRCtx _]). Qed.

Lemma app_step_l (e1 e1' e2: expr) h h' :
  contextual_step (e1, h) (e1', h') → is_val e2 → contextual_step (e1 e2, h) (e1' e2, h').
Proof.
  intros ? (v & Hv)%is_val_spec.
  rewrite <-(of_to_val _ _ Hv).
  by apply (fill_contextual_step [AppLCtx _]).
Qed.

Lemma app_step_beta (x: string) (e e': expr) h :
  is_val e' → is_closed [x] e → contextual_step ((λ: x, e)%E e', h) (lang.subst x e' e, h).
Proof.
  intros Hval Hclosed. eapply base_contextual_step, BetaS; eauto.
Qed.

Lemma unroll_roll_step (e: expr) h :
  is_val e → contextual_step ((unroll (roll e))%E, h) (e, h).
Proof.
  intros ?; by eapply base_contextual_step, UnrollS.
Qed.

Lemma fill_reducible K e h : 
  reducible e h → reducible (fill K e) h.
Proof.
  intros (e' & h' & Hstep).
  exists (fill K e'), h'. eapply fill_contextual_step. done.
Qed.

Lemma reducible_contextual_step_case K e e' h1 h2 :
  contextual_step (fill K e, h1) (e', h2) → 
  reducible e h1 →
  ∃ e'', e' = fill K e'' ∧ contextual_step (e, h1) (e'', h2).
Proof.
  intros [ | Hval]%contextual_ectx_step_case Hred; first done.
  exfalso. apply is_val_spec in Hval as (v & Hval). 
  apply reducible_not_val in Hred. congruence.
Qed.

(** Contextual lifting lemmas for deterministic reduction *)
Tactic Notation "lift_det" uconstr(ctx) := 
  intros; 
  let Hs := fresh in 
  match goal with 
  | H : det_step _ _ |- _ => destruct H as [? Hs]
  end;
  simplify_val; econstructor; 
  [intros; by eapply (fill_reducible ctx) | 
   intros ? ? ? (? & -> & [-> ->]%Hs)%(reducible_contextual_step_case ctx); done ].

Lemma det_step_pair_r e1 e2 e2' :
  det_step e2 e2' →
  det_step (e1, e2)%E (e1, e2')%E.
Proof. lift_det [PairRCtx _]. Qed.

Lemma det_step_pair_l e1 e1' e2 :
  is_val e2 →
  det_step e1 e1' →
  det_step (e1, e2)%E (e1', e2)%E.
Proof. lift_det [PairLCtx _]. Qed.
Lemma det_step_binop_r e1 e2 e2' op :
  det_step e2 e2' →
  det_step (BinOp op e1 e2)%E (BinOp op e1 e2')%E.
Proof. lift_det [BinOpRCtx _ _]. Qed.
Lemma det_step_binop_l e1 e1' e2 op :
  is_val e2 →
  det_step e1 e1' →
  det_step (BinOp op e1 e2)%E (BinOp op e1' e2)%E.
Proof. lift_det [BinOpLCtx _ _]. Qed.
Lemma det_step_if e e' e1 e2 :
  det_step e e' →
  det_step (If e e1 e2)%E (If e' e1 e2)%E.
Proof. lift_det [IfCtx _ _]. Qed.
Lemma det_step_app_r e1 e2 e2' :
  det_step e2 e2' →
  det_step (App e1 e2)%E (App e1 e2')%E.
Proof. lift_det [AppRCtx _]. Qed.
Lemma det_step_app_l e1 e1' e2 :
  is_val e2 →
  det_step e1 e1' →
  det_step (App e1 e2)%E (App e1' e2)%E.
Proof. lift_det [AppLCtx _]. Qed.
Lemma det_step_snd_lift e e' :
  det_step e e' →
  det_step (Snd e)%E (Snd e')%E.
Proof. lift_det [SndCtx]. Qed.
Lemma det_step_fst_lift e e' :
  det_step e e' →
  det_step (Fst e)%E (Fst e')%E.
Proof. lift_det [FstCtx]. Qed.
Lemma det_step_store_r e1 e2 e2' :
  det_step e2 e2' →
  det_step (Store e1 e2)%E (Store e1 e2')%E.
Proof. lift_det [StoreRCtx _]. Qed.
Lemma det_step_store_l e1 e1' e2 :
  is_val e2 →
  det_step e1 e1' →
  det_step (Store e1 e2)%E (Store e1' e2)%E.
Proof. lift_det [StoreLCtx _]. Qed.


#[global]
Hint Resolve app_step_r app_step_l app_step_beta unroll_roll_step : core.
#[global]
Hint Extern 1 (is_val _) => (simpl; fast_done) : core.
#[global]
Hint Immediate is_val_of_val : core.

#[global]
Hint Resolve det_step_beta det_step_tbeta det_step_unpack det_step_unop det_step_binop det_step_if_true det_step_if_false det_step_fst det_step_snd det_step_casel det_step_caser det_step_unroll : core.

#[global]
Hint Resolve det_step_pair_r det_step_pair_l det_step_binop_r det_step_binop_l det_step_if det_step_app_r det_step_app_l det_step_snd_lift det_step_fst_lift det_step_store_l det_step_store_r : core.

#[global]
Hint Constructors nsteps : core.

#[global] 
Hint Extern 1 (is_val _) => simpl : core.

Ltac do_det_step :=
  match goal with 
  | |- nsteps det_step _ _ _ => econstructor 2; first do_det_step
  | |- det_step _ _ => simpl; solve[eauto 10]
  end.
