From stdpp Require Import gmap base relations tactics.
From iris Require Import prelude.
From semantics.ts.stlc Require Import lang notation.


(* In these exercises, we will use the reflexive, transitive closure
   of relations from the library stdpp defined by:

   Inductive rtc {X} (R: X → X → Prop):
    | rtc_refl x : rtc R x x
    | rtc_l x y z :
        R x y →
        rtc R y z →
        rtc R x z.

  With the following instruction, we make eauto aware
  of its constructors.
*)
#[local] Hint Constructors rtc : core.



(** Exercise 2 (LN Exercise 1): Deterministic Operational Semantics *)


Lemma val_no_step e e':
  step e e' → is_val e → False.
Proof. Admitted.

(** You might find the following tactic useful,
  which derives a contradiction when you have a [step e1 e2] assumption and
  [e1] is a value.

  Example:
  H1: step e e'
  H2: is_val e
  =====================
  ???

  Then [val_no_step.] will solve the goal by applying the [val_no_step] lemma.

  (We neither expect you to understand how exactly the tactic does this nor
   to be able to write such a tactic yourself. Where useful, we will always
   provide you with custom tactics and explain in a comment what they do.)

*)
Ltac val_no_step :=
  match goal with
  | [H: step ?e1 ?e2 |- _] =>
    solve [exfalso; eapply (val_no_step _ _ H); done]
  end.

Lemma step_det e e' e'':
  step e e' → step e e'' → e' = e''.
Proof. Admitted.

(** Exercise 3 (LN Exercise 2): Call-by-name Semantics *)
Inductive cbn_step : expr → expr → Prop :=
  | CBNStepBeta x e e'  :
  cbn_step (App (Lam x e) e') (subst' x e' e)
  (* | .... *).

(* We make the eauto tactic aware of the constructors of cbn_step *)
#[global] Hint Constructors cbn_step : core.

Lemma different_results :
 ∃ (e: expr) (e1 e2: expr), rtc cbn_step e e1 ∧ rtc step e e2 ∧ is_val e1 ∧ is_val e2 ∧ e1 ≠ e2.
Proof. Admitted.

Lemma val_no_cbn_step e e':
  cbn_step e e' → is_val e →  False.
Proof.
Admitted.

(* Same tactic as [val_no_step] but for cbn_step.*)
Ltac val_no_cbn_step :=
  match goal with
  | [H: cbn_step ?e1 ?e2 |- _] =>
    solve [exfalso; eapply (val_no_cbn_step _ _ H); done]
  end.

Lemma cbn_step_det e e' e'':
  cbn_step e e' → cbn_step e e'' → e' = e''.
Proof. Admitted.



(** Exercise 4 (LN Exercise 3): Big-step vs small-step semantics *)
Lemma big_step_steps e v :
  big_step e v → rtc step e (of_val v).
Proof. Admitted.

Lemma steps_big_step e (v: val):
  rtc step e v → big_step e v.
Proof. Admitted.


(** Exercise 5 (LN Exercise 4): left-to-right evaluation *)
Inductive ltr_step : expr → expr → Prop := .

#[global] Hint Constructors ltr_step : core.

Lemma different_steps_ltr_step :
 ∃ (e: expr) (e1 e2: expr), ltr_step e e1 ∧ step e e2 ∧ e1 ≠ e2.
Admitted.

Lemma big_step_ltr_steps e v :
  big_step e v → rtc ltr_step e (of_val v).
Proof. Admitted.

Lemma ltr_steps_big_step e (v: val):
  rtc ltr_step e v → big_step e v.
Proof. Admitted.


