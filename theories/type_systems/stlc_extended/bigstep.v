From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.stlc_extended Require Import lang notation types.

(** * Big-step semantics *)

Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A : type).

Inductive big_step : expr → val → Prop :=
  | bs_lit (l : base_lit) :
      big_step (Lit l) (LitV l)
  | bs_lam (x : binder) (e : expr) :
      big_step (λ: x, e)%E (λ: x, e)%V
  | bs_app e1 e2 x e v2 v :
      big_step e1 (LamV x e) →
      big_step e2 v2 →
      big_step (subst' x (of_val v2) e) v →
      big_step (App e1 e2) v
  (* FIXME : extend the big-step semantics *)
    .
#[export] Hint Constructors big_step : core.
#[export] Hint Constructors base_step : core.
#[export] Hint Constructors contextual_step : core.

Lemma big_step_of_val e v :
  e = of_val v →
  big_step e v.
Proof.
  intros ->.
  induction v; simpl; eauto.
  (* FIXME : this should be fixed once you have added the right semantics *)
Admitted.

Lemma big_step_val v v' :
  big_step (of_val v) v' → v' = v.
Proof.
  enough (∀ e, big_step e v' → e = of_val v → v' = v) by naive_solver.
  intros e Hb.
  induction Hb in v |-*; intros Heq; subst; destruct v; inversion Heq; subst; naive_solver.
Qed.
