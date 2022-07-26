From stdpp Require Import base relations tactics.
From iris Require Import prelude.
From semantics.lib Require Import sets maps.
From semantics.ts.stlc Require Import lang notation.

(** The following two lemmas will be helpful in the sequel.
  They just lift multiple reduction steps (via [rtc]) to application.
 *)
Lemma steps_app_r (e1 e2 e2' : expr) :
  rtc step e2 e2' →
  rtc step (e1 e2) (e1 e2').
Proof.
  induction 1 as [ e | e e' e'' Hstep Hsteps IH].
  - reflexivity.
  - eapply (rtc_l _ _ (e1 e')).
    { by eapply StepAppR. }
    done.
Qed.

Lemma steps_app_l (e1 e1' e2 : expr) :
  is_val e2 →
  rtc step e1 e1' →
  rtc step (e1 e2) (e1' e2).
Proof.
  intros Hv.
  induction 1 as [ e | e e' e'' Hstep Hsteps IH].
  - reflexivity.
  - eapply (rtc_l _ _ (e' e2)).
    { by eapply StepAppL. }
    done.
Qed.


(** * Untyped λ calculus *)

(** We do not re-define the language to remove primitive addition -- instead, we just
  restrict our usage in this file to variables, application, and lambdas.
 *)


Definition I_val : val := λ: "x", "x".
Definition F_val : val := λ: "x" "y", "x".
Definition S_val : val := λ: "x" "y", "y".
Definition ω : val := λ: "x", "x" "x".
Definition Ω : expr := ω ω.


(** Ω reduces to itself! *)
Lemma Omega_step : step Ω Ω.
Proof.
  apply StepBeta. done.
Qed.

(** ** Scott encodings *)

Definition zero : val := λ: "x" "y", "x".

Definition succ (n : val) : val := λ: "x" "y", "y" n.
(** [Succ] can be seen as a constructor: it takes [n] at the level of the language. *)
Definition Succ : val := λ: "n" "x" "y", "y" "n".

Fixpoint enc_nat (n : nat) : val :=
  match n with
  | 0 => zero
  | S n => succ (enc_nat n)
  end.

Lemma enc_nat_closed n :
  closed [] (enc_nat n).
Proof.
  induction n as [ | n IH].
  - done.
  - simpl. by apply closed_weaken_nil.
Qed.

Lemma enc_0_red (z s : val) :
  is_closed [] z →
  rtc step (enc_nat 0 z s) z.
Proof.
  intros Hcl.
  eapply rtc_l.
  { econstructor; first auto. econstructor. auto. }
  simpl. eapply rtc_l.
  { econstructor. auto. }
  simpl. rewrite subst_closed_nil; done.
Qed.

Lemma enc_S_red n (z s : val) :
  rtc step (enc_nat (S n) z s) (s (enc_nat n)).
Proof.
  simpl. eapply rtc_l.
  { econstructor; first auto. econstructor. auto. }
  simpl. eapply rtc_l.
  { econstructor. auto. }
  simpl. rewrite (subst_closed_nil (enc_nat n)); last apply enc_nat_closed.
  rewrite subst_closed_nil; last apply enc_nat_closed.
  reflexivity.
Qed.

Lemma Succ_red n : step (Succ (enc_nat n)) (enc_nat (S n)).
Proof. econstructor. apply is_val_val. Qed.

Lemma Succ_red_n n : rtc step (Nat.iter n Succ zero) (enc_nat n).
Proof.
  induction n as [ | n IH].
  - reflexivity.
  - simpl.
    etrans.
    { simpl. eapply steps_app_r. apply IH. }
    eapply rtc_l.
    { apply Succ_red. }
    reflexivity.
Qed.

(** ** Recursion *)
Definition Fix' : val := λ: "z" "y", "y" (λ: "x", "z" "z" "y" "x").
Definition Fix (s : val) : val := λ: "x", Fix' Fix' s "x".
Arguments Fix : simpl never.

Local Hint Immediate is_val_val : core.

(** We prove that it satisfies the recursive unfolding *)
Lemma Fix_step (s r : val) :
  is_closed [] s →
  rtc step (Fix s r) (s ((Fix s))%E r).
Proof.
  intros Hclosed.
  eapply rtc_l.
  { econstructor. auto. }
  eapply rtc_l.
  { simpl. econstructor; first by auto.
    econstructor. { rewrite subst_closed_nil; auto. }
    econstructor. done.
  }
  simpl. rewrite subst_closed_nil; last done.
  eapply rtc_l.
  { econstructor; first by auto.
    econstructor. auto.
  }
  simpl. reflexivity.
Qed.

(** Example usage: addition on Scott-encoded numbers *)
Definition add_step : val := λ: "r", λ: "n" "m", "n" "m" (λ: "p", Succ ("r" "p" "m")).
Definition add := Fix add_step.

(** We are now going to prove it correct:
 [add (enc_nat n) (enc_nat m)) ≻* (enc_nat (n + m))]

 First, we prove that it satisfies the expected defining equations for Peano addition.
 *)

Lemma add_step_0 m : rtc step (add (enc_nat 0) (enc_nat m)) (enc_nat m).
Proof.
  (* use the unfolding equation of the fixpoint combinator *)
  etrans.
  { eapply steps_app_l; first by auto.
    eapply Fix_step. done.
  }
  (* subst it into the [add_step] function *)
  eapply rtc_l.
  { econstructor; auto. econstructor; auto. econstructor. auto. }
  simpl.
  (* subst in the zero *)
  eapply rtc_l.
  { econstructor; auto. econstructor. done. }
  simpl.
  (* subst in the m *)
  eapply rtc_l.
  { econstructor; auto. }
  simpl.

  (* do a step *)
  etrans.
  { apply (enc_0_red (enc_nat m) (λ: "p", Succ (Fix add_step "p" (enc_nat m)))).
    apply enc_nat_closed.
  }
  reflexivity.
Qed.

Lemma add_step_S n m : rtc step (add (enc_nat (S n)) (enc_nat m)) (Succ (add (enc_nat n) (enc_nat m))).
Proof.
  (* use the unfolding equation of the fixpoint combinator *)
  etrans.
  { eapply steps_app_l; first by auto.
    eapply Fix_step. done.
  }
  (* subst it into the [add_step] function *)
  eapply rtc_l.
  { econstructor; auto. econstructor; auto. econstructor. auto. }
  simpl.
  (* subst in the zero *)
  eapply rtc_l.
  { econstructor; auto. econstructor. done. }
  simpl.
  (* subst in the m *)
  eapply rtc_l.
  { econstructor; auto. }
  simpl.
  (* do a step *)
  etrans.
  { rewrite subst_closed_nil; last apply enc_nat_closed.
    apply (enc_S_red n (enc_nat m) (λ: "p", Succ (Fix add_step "p" (enc_nat m)))).
  }

  eapply rtc_l.
  { econstructor. auto. }
  simpl.
  rewrite subst_closed_nil; last apply enc_nat_closed.
  reflexivity.
Qed.

Lemma add_correct n m : rtc step (add (enc_nat n) (enc_nat m)) (enc_nat (n + m)).
Proof.
  induction n as [ | n IH].
  - apply add_step_0.
  - etrans. { apply add_step_S. }
    etrans. { apply steps_app_r. apply IH. }
    eapply rtc_l. { apply Succ_red. }
    reflexivity.
Qed.
