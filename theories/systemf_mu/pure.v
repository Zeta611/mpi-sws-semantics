From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Import maps.
From semantics.systemf_mu Require Import lang notation.

Lemma contextual_ectx_step_case K e e' :
  contextual_step (fill K e) e' →
  (∃ e'', e' = fill K e'' ∧ contextual_step e e'') ∨ is_val e.
Proof.
  (* FIXME: exercise for you :) *)
(*Qed.*)
Admitted.

(** ** Deterministic reduction *)

Record det_step (e1 e2 : expr) := {
  det_step_safe : reducible e1;
  det_step_det e2' :
    contextual_step e1 e2' → e2' = e2
}.

Record det_base_step (e1 e2 : expr) := {
  det_base_step_safe : base_reducible e1;
  det_base_step_det e2' :
    base_step e1 e2' → e2' = e2
}.

Lemma det_base_step_det_step e1 e2 : det_base_step e1 e2 → det_step e1 e2.
Proof.
  intros [Hp1 Hp2]. split.
  - destruct Hp1 as (e2' & ?).
    eexists e2'. by apply base_contextual_step.
  - intros e2' ?%base_reducible_contextual_step; [ | done]. by apply Hp2.
Qed.

(** *** Pure execution lemmas *)
Local Ltac inv_step :=
  repeat match goal with
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?e ?e2 |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.
Local Ltac solve_exec_safe := intros; subst; eexists; econstructor; eauto.
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
Definition red_nsteps (n : nat) (e e' : expr) := nsteps contextual_step n e e' ∧ irreducible e'.

Lemma det_step_red e e' e'' n :
  det_step e e' →
  red_nsteps n e e'' →
  1 ≤ n ∧ red_nsteps (n - 1) e' e''.
Proof.
  intros [Hprog Hstep] Hred.
  inversion Hprog; subst.
  destruct Hred as [Hred  Hirred].
  destruct n as [ | n].
  { inversion Hred; subst.
    exfalso; eapply not_reducible; done.
  }
  inversion Hred; subst. simpl.
  apply Hstep in H as ->. apply Hstep in H1 as ->.
  split; first lia.
  replace (n - 0) with n by lia. done.
Qed.

Lemma contextual_step_red_nsteps n e e' e'' :
  contextual_step e e' →
  red_nsteps n e' e'' →
  red_nsteps (S n) e e''.
Proof.
  intros Hstep [Hsteps Hirred].
  split; last done.
  by econstructor.
Qed.

Lemma nsteps_val_inv n v e' :
  red_nsteps n (of_val v) e' → n = 0 ∧ e' = of_val v.
Proof.
  intros [Hred Hirred]; cbn in *.
  destruct n as [ | n].
  - inversion Hred; subst. done.
  - inversion Hred; subst. exfalso. eapply val_irreducible; last done.
    rewrite to_of_val. eauto.
Qed.

Lemma nsteps_val_inv' n v e e' :
  to_val e = Some v →
  red_nsteps n e e' → n = 0 ∧ e' = of_val v.
Proof. intros Ht. rewrite -(of_to_val _ _ Ht). apply nsteps_val_inv. Qed.

Lemma red_nsteps_fill K k e e' :
  red_nsteps k (fill K e) e' →
  ∃ j e'', j ≤ k ∧
    red_nsteps j e e'' ∧
    red_nsteps (k - j) (fill K e'') e'.
Proof.
  (* FIXME: this is an exercise :) *)
Admitted.


(** Additionally useful stepping lemmas *)
Lemma app_step_r (e1 e2 e2': expr) :
  contextual_step e2 e2' → contextual_step (e1 e2) (e1 e2').
Proof. by apply (fill_contextual_step [AppRCtx _]). Qed.

Lemma app_step_l (e1 e1' e2: expr) :
  contextual_step e1 e1' → is_val e2 → contextual_step (e1 e2) (e1' e2).
Proof.
  intros ? (v & Hv)%is_val_spec.
  rewrite <-(of_to_val _ _ Hv).
  by apply (fill_contextual_step [AppLCtx _]).
Qed.

Lemma app_step_beta (x: string) (e e': expr) :
  is_val e' → is_closed [x] e → contextual_step ((λ: x, e) e') (lang.subst x e' e).
Proof.
  intros Hval Hclosed. eapply base_contextual_step, BetaS; eauto.
Qed.

Lemma unroll_roll_step (e: expr) :
  is_val e → contextual_step (unroll (roll e)) e.
Proof.
  intros ?; by eapply base_contextual_step, UnrollS.
Qed.


Lemma fill_reducible K e :
  reducible e → reducible (fill K e).
Proof.
  intros (e' & Hstep).
  exists (fill K e'). eapply fill_contextual_step. done.
Qed.

Lemma reducible_contextual_step_case K e e' :
  contextual_step (fill K e) (e') →
  reducible e →
  ∃ e'', e' = fill K e'' ∧ contextual_step e e''.
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
   intros ? (? & -> & ->%Hs)%(reducible_contextual_step_case ctx); done ].

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


#[global]
Hint Resolve app_step_r app_step_l app_step_beta unroll_roll_step : core.
#[global]
Hint Extern 1 (is_val _) => (simpl; fast_done) : core.
#[global]
Hint Immediate is_val_of_val : core.

#[global]
Hint Resolve det_step_beta det_step_tbeta det_step_unpack det_step_unop det_step_binop det_step_if_true det_step_if_false det_step_fst det_step_snd det_step_casel det_step_caser det_step_unroll : core.

#[global]
Hint Resolve det_step_pair_r det_step_pair_l det_step_binop_r det_step_binop_l det_step_if det_step_app_r det_step_app_l det_step_snd_lift det_step_fst_lift : core.

#[global]
Hint Constructors nsteps : core.

#[global]
Hint Extern 1 (is_val _) => simpl : core.

(** Prove a single deterministic step using the lemmas we just proved *)
Ltac do_det_step :=
  match goal with
  | |- nsteps det_step _ _ _ => econstructor 2; first do_det_step
  | |- det_step _ _ => simpl; solve[eauto 10]
  end.
