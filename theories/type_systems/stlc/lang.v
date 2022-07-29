From stdpp Require Export binders strings.
From stdpp Require Import options.
From semantics.lib Require Import maps.

(** * Simply Typed Lambda Calculus *)

(** ** Expressions and values. *)
(** [Z] is Coq's version of the integers.
    All the standard operations, like [+], are defined on it.

    The type [binder] is defined as [x ::= BNamed (s: string) | BAnon]
    where BAnon can be used if we don't want to use the variable in
    the function.
*)
Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Lam (x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | LitInt (n: Z)
  | Plus (e1 e2 : expr).

Inductive val :=
  | LitIntV (n: Z)
  | LamV (x : binder) (e : expr).

(* Injections into expr *)
Definition of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV x e => Lam x e
  end.

(* try to make an expr into a val *)
Definition to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam x e => Some (LamV x e)
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v; simpl; reflexivity.
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e; simpl; try congruence.
  all: injection 1 as <-; simpl; reflexivity.
Qed.

(* Inj is a type class for injective functions.
   It is defined as:
    [Inj R S f := ∀ x y, S (f x) (f y) → R x y]
*)
#[export] Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite <-!to_of_val, Hv. Qed.

(* A predicate which holds true whenever an
   expression is a value. *)
Definition is_val (e : expr) : Prop :=
  match e with
  | LitInt n => True
  | Lam x e => True
  | _ => False
  end.
Lemma is_val_spec e : is_val e ↔ ∃ v, to_val e = Some v.
Proof.
  destruct e; simpl.
  (* naive_solver is an automation tactic like intuition, firstorder, auto, ...
     It is provided by the stdpp library. *)
  all: naive_solver.
Qed.

Lemma is_val_of_val v : is_val (of_val v).
Proof.
  apply is_val_spec. rewrite to_of_val. eauto.
Qed.

(* A small tactic that simplifies handling values. *)
Ltac simplify_val :=
  repeat match goal with
  | H: to_val (of_val ?v) = ?o |- _ => rewrite to_of_val in H
  | H: is_val ?e |- _ => destruct (proj1 (is_val_spec e) H) as (? & ?); clear H
  end.

(* values are values *)
Lemma is_val_val (v: val): is_val (of_val v).
Proof.
  destruct v; simpl; done.
Qed.

(* we tell eauto to use the lemma is_val_val *)
#[global]
Hint Immediate is_val_val : core.


(** ** Operational Semantics *)

(** *** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | LitInt n => LitInt n
  (* The function [decide] can be used to decide propositions.
    [decide P] is of type {P} + {¬ P}.
    It can only be applied to propositions for which, by type class inference,
    it can be determined that the proposition is decidable. *)
  | Var y => if decide (x = y) then es else Var y
  | Lam y e =>
      Lam y $ if decide (BNamed x = y) then e else subst x es e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Plus e1 e2 => Plus (subst x es e1) (subst x es e2)
  end.

(* We lift substitution to binders. *)
Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.


(** *** Small-Step Semantics *)
(* We use right-to-left evaluation order,
   which means in a binary term (e.g., e1 + e2),
   the left side can only be reduced once the right
   side is fully evaluated (i.e., is a value). *)
Inductive step : expr → expr → Prop :=
  | StepBeta x e e'  :
      is_val e' →
      step (App (Lam x e) e') (subst' x e' e)
  | StepAppL e1 e1' e2 :
    is_val e2 →
    step e1 e1' →
    step (App e1 e2) (App e1' e2)
  | StepAppR e1 e2 e2' :
    step e2 e2' →
    step (App e1 e2) (App e1 e2')
  | StepPlusRed (n1 n2 n3: Z) :
    (n1 + n2)%Z = n3 →
    step (Plus (LitInt n1) (LitInt n2)) (LitInt n3)
  | StepPlusL e1 e1' e2 :
    is_val e2 →
    step e1 e1' →
    step (Plus e1 e2) (Plus e1' e2)
  | StepPlusR e1 e2 e2' :
    step e2 e2' →
    step (Plus e1 e2) (Plus e1 e2').

(* We make the tactic eauto aware of the constructors of [step].
   Then it can automatically solve goals where we want to prove a step. *)
#[global] Hint Constructors step : core.


(* A term is reducible, if it can take a step. *)
Definition reducible (e : expr) :=
  ∃ e', step e e'.


(** *** Big-Step Semantics *)
Inductive big_step : expr → val → Prop :=
  | bs_lit (n : Z) :
      big_step (LitInt n) (LitIntV n)
  | bs_lam (x : binder) (e : expr) :
      big_step (Lam x e) (LamV x e)
  | bs_add e1 e2 (z1 z2 : Z) :
      big_step e1 (LitIntV z1) →
      big_step e2 (LitIntV z2) →
      big_step (Plus e1 e2) (LitIntV (z1 + z2))%Z
  | bs_app e1 e2 x e v2 v :
      big_step e1 (@LamV x e) →
      big_step e2 v2 →
      big_step (subst' x (of_val v2) e) v →
      big_step (App e1 e2) v
    .
#[export] Hint Constructors big_step : core.


Lemma big_step_vals (v: val): big_step (of_val v) v.
Proof.
  induction v; econstructor.
Qed.

Lemma big_step_inv_vals (v w: val): big_step (of_val v) w → v = w.
Proof.
  destruct v; inversion 1; eauto.
Qed.


(** *** Contextual Semantics *)
(** Base reduction *)
Inductive base_step : expr → expr → Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 →
     e' = subst' x e2 e1 →
     base_step (App (Lam x e1) e2) e'
  | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (LitInt n1) →
     e2 = (LitInt n2) →
     (n1 + n2)%Z = n3 →
     base_step (Plus e1 e2) (LitInt n3).

Inductive ectx :=
  | HoleCtx
  | AppLCtx (K: ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K: ectx)
  | PlusLCtx (K: ectx) (v2 : val)
  | PlusRCtx (e1 : expr) (K: ectx).

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | PlusLCtx K v2 => Plus (fill K e) (of_val v2)
  | PlusRCtx e1 K => Plus e1 (fill K e)
  end.

(* filling a context with another context *)
Fixpoint comp_ectx (Ko Ki: ectx) :=
  match Ko with
  | HoleCtx => Ki
  | AppLCtx K v2 => AppLCtx (comp_ectx K Ki) v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K Ki)
  | PlusLCtx K v2 => PlusLCtx (comp_ectx K Ki) v2
  | PlusRCtx e1 K => PlusRCtx e1 (comp_ectx K Ki)
  end.

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' →
    e2 = fill K e2' →
    base_step e1' e2' →
    contextual_step e1 e2.

Definition contextual_reducible (e : expr) :=
  ∃ e', contextual_step e e'.

#[export] Hint Constructors base_step : core.
#[export] Hint Constructors contextual_step : core.
(* Lemmas about the contextual semantics *)
Definition empty_ectx := HoleCtx.

Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 → contextual_step e1 e2.
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.

Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 → contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.


(** Open and closed expressions *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lam x e => is_closed (x :b: X) e
  | LitInt _ => true
  | App e1 e2
  | Plus e1 e2 => is_closed X e1 && is_closed X e2
  end.

Notation closed X e := (Is_true (is_closed X e)).
#[export] Instance closed_proof_irrel X e : ProofIrrel (closed X e).
Proof. unfold closed. apply _. Qed.
#[export] Instance closed_dec X e : Decision (closed X e).
Proof. unfold closed. apply _. Defined.

Lemma closed_weaken X Y e : closed X e → X ⊆ Y → closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma closed_weaken_nil X e : closed [] e → closed X e.
Proof. intros. by apply closed_weaken with [], list_subseteq_nil. Qed.

Lemma closed_subst X Y e x es :
  closed Y es → closed (x :: X) e → closed (X ++ Y) (subst x es e).
Proof.
  induction e as [y|y e IH|e1 e2|n|e1 e2]in X |-*; simpl; intros Hc1 Hc2; eauto.
  - eapply bool_decide_unpack, elem_of_cons in Hc2 as [->|Hc2].
    + destruct decide; try congruence. eapply closed_weaken; eauto with set_solver.
    + destruct decide.
      * eapply closed_weaken; eauto with set_solver.
      * simpl. eapply bool_decide_pack. set_solver.
  - destruct y as [|y]; simpl in *; eauto.
    destruct decide as [Heq|].
    + injection Heq as ->. eapply closed_weaken; eauto. set_solver.
    + rewrite app_comm_cons. eapply IH; eauto.
      eapply closed_weaken; eauto. set_solver.
  - eapply andb_True. eapply andb_True in Hc2 as [H1 H2].
    split; eauto.
  - eapply andb_True. eapply andb_True in Hc2 as [H1 H2].
    split; eauto.
Qed.

Lemma closed_subst_nil X e x es :
  closed [] es → closed (x :: X) e → closed X (subst x es e).
Proof.
  intros Hc1 Hc2. eapply closed_subst in Hc1; eauto.
  revert Hc1. rewrite right_id; [done|apply _].
Qed.

Lemma closed_do_subst' X e x es :
  closed [] es → closed (x :b: X) e → closed X (subst' x es e).
Proof. destruct x; eauto using closed_subst_nil. Qed.

Lemma subst_closed X e x es : closed X e → x ∉ X → subst x es e = e.
Proof.
  induction e in X |-*; simpl; rewrite ?bool_decide_spec, ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_closed_nil e x es : closed [] e → subst x es e = e.
Proof. intros. apply subst_closed with []; set_solver. Qed.
