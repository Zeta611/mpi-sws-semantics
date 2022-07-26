(* Throughout the course, we will be using the [stdpp] library to provide
  some useful and common features.
  We will introduce you to its features as we need them.
 *)
 From stdpp Require Import base tactics numbers strings.
 From stdpp Require relations.
 From semantics.lib Require Import maps.

 (** * Exercise sheet 0 *)

(* We are using Coq's notion of integers, [Z].
  All the standard operations, like [+] and [*], are defined on it.
*)
Inductive expr :=
  | Const (z : Z)
  | Plus (e1 e2 : expr)
  | Mul (e1 e2 : expr).

 (** Exercise 1: Arithmetics *)
 Fixpoint expr_eval (e : expr) : Z :=
  (* TODO: write the function *)
  0.

 Lemma expr_eval_test: expr_eval (Plus (Const (-4)) (Const 5)) = 1%Z.
 Proof.
    (* Should be solved by: simpl. lia. *)
 Admitted.

 Lemma plus_eval_comm e1 e2 :
   expr_eval (Plus e1 e2) = expr_eval (Plus e2 e1).
 Proof. Admitted.
 Lemma plus_syntax_not_comm :
   Plus (Const 0) (Const 1) ≠ Plus (Const 1) (Const 0).
 Proof. Admitted.

 (** Exercise 2: Arithmetics Structural Semantics *)

 Inductive step : expr → expr → Prop :=
   | step_plus_l e1 e2 e2' :
       step e2 e2' → step (Plus e1 e2) (Plus e1 e2')
   | step_plus_r e1 e1' z2 :
       step e1 e1' → step (Plus e1 (Const z2)) (Plus e1' (Const z2))
   | step_plus z1 z2 :
       step (Plus (Const z1) (Const z2)) (Const (z1 + z2))
   | step_mul_l e1 e2 e2' :
       step e2 e2' → step (Mul e1 e2) (Mul e1 e2')
   | step_mul_r e1 e1' z2 :
       step e1 e1' → step (Mul e1 (Const z2)) (Mul e1' (Const z2))
   | step_mul z1 z2 :
       step (Mul (Const z1) (Const z2)) (Const (z1 * z2))
 .
 #[export] Hint Constructors step : core.

 Lemma no_step_const z e' :
   step (Const z) e' → False.
 Proof.
 Admitted.

 Lemma step_deterministic e e' e'' :
   step e e' → step e e'' → e' = e''.
 Proof.
   intros Hstep1 Hstep2.
   induction Hstep1 as [ ??? H IH | ??? H IH | | ??? H IH | ??? H IH | ] in e'', Hstep2 |-*.
   { inversion Hstep2; subst.
     + f_equal. by apply IH.
     + exfalso; by eapply no_step_const.
     + exfalso; by eapply no_step_const.
   }
   { inversion Hstep2; subst.
     + exfalso; by eapply no_step_const.
     + f_equal. by apply IH.
     + exfalso; by eapply no_step_const.
   }
   (* you get the idea, let's apply some automation... *)
   (* [naive_solver] is a clever automation tactic by [stdpp] that can solve many simple things. *)
   all: inversion Hstep2; subst; first [ try exfalso; by eapply no_step_const | naive_solver].
 Qed.

 (** Now let's define some notation to make it look nice! *)
 (* We declare a so-called notation scope, so that we can still use the nice notations for addition on natural numbers [nat] and integers [Z]. *)
 Declare Scope expr.
 Delimit Scope expr with E.
 Notation "e1 + e2" := (Plus e1%E e2%E) : expr.
 Notation "e1 * e2" := (Mul e1%E e2%E) : expr.

 (* We can use our nice notation to write expressions!
    (note the [%E] to tell Coq to parse this as an arithmetical expression with the
    notations we just defined).
  *)
 Check (Const 5 + Const 5)%E.
 (* The notation also still works for [Z] and [nat]: *)
 Check (5 + 5)%Z.
 Check (5 + 5).

 (** Exercise 3: Reflexive-transitive closure *)
 Section rtc.
  Context {X : Type}.

   Inductive rtc (R : X → X → Prop) : X → X → Prop :=
     | rtc_base x : rtc R x x
     | rtc_step x y z : R x y → rtc R y z → rtc R x z.

   Lemma rtc_reflexive R : Reflexive (rtc R).
   Proof. unfold Reflexive. Admitted.
   Lemma rtc_transitive R : Transitive (rtc R).
   Proof. unfold Transitive. Admitted.

   Lemma rtc_subrel (R: X → X → Prop) (x y : X): R x y → rtc R x y.
   Proof. Admitted.

   Section typeclass.
     (* We can use Coq's typeclass mechanism to enable the use of the [transitivity] and [reflexivity] tactics on our goals.
       Typeclasses enable easy extensions of existing mechanisms -- in this case, by telling Coq to use the knowledge about our definition of [rtc].
      *)
    (* [Transitive] is a typeclass. With [Instance] we provide an instance of it. *)
    Global Instance rtc_transitive_inst R : Transitive (rtc R).
    Proof.
      apply rtc_transitive.
    Qed.
    Global Instance rtc_reflexive_inst R : Reflexive (rtc R).
    Proof.
      apply rtc_reflexive.
    Qed.
  End typeclass.
End rtc.

(* Let's put this to the test! *)
Goal rtc step (Const 42) (Const 42).
Proof.
  (* this uses the [rtc_reflexive_inst] instance we registered. *)
  reflexivity.
Qed.
Goal rtc step (Const 42 * (Const 5 + Const 5)%E)%E (Const 420).
Proof.
  (* this uses the [rtc_transitive_inst] instance we registered. *)
  etransitivity.
  + eapply rtc_step; eauto. reflexivity.
  + eapply rtc_step; eauto. reflexivity.
Qed.

Section stdpp.
  (* In fact, [rtc] is so common that it is already provided by the [stdpp] library! *)
  Import stdpp.relations.
  Print rtc.

  (* The typeclass instances are also already registered. *)
  Goal rtc step (Const 42) (Const 42).
  Proof. reflexivity. Qed.

End stdpp.

(* Prove the following lemmas. *)
Lemma plus_right e1 e2 e2':
 rtc step e2 e2' → rtc step (Plus e1 e2) (Plus e1 e2').
Proof. Admitted.

Lemma plus_left e1 e1' n:
 rtc step e1 e1' → rtc step (Plus e1 (Const n)) (Plus e1' (Const n)).
Proof. Admitted.

Lemma plus_to_consts e1 e2 n m:
 rtc step e1 (Const n) → rtc step e2 (Const m) → rtc step (e1 + e2)%E (Const (n + m)%Z).
Proof. Admitted.


(** Exercise 4: Open arithmetical expressions *)

(* Finally, we introduce variables into our arithmetic expressions.
   Variables are of Coq's [string] type.
*)
Inductive expr' :=
  | Var (x: string)
  | Const' (z : Z)
  | Plus' (e1 e2 : expr')
  | Mul' (e1 e2 : expr').

(* We call an expression closed under the list X,
   if it only contains variables in X *)
Fixpoint is_closed (X: list string) (e: expr') : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Const' z => true
  | Plus' e1 e2 => is_closed X e1 && is_closed X e2
  | Mul' e1 e2 => is_closed X e1 && is_closed X e2
  end.

Definition closed X e := is_closed X e = true.


(* Some examples of closed terms. *)
Lemma example_no_vars_closed:
  closed [] (Plus' (Const' 3) (Const' 5)).
Proof.
  (* [done] is an automation tactic provided by [stdpp] to solve simple goals. *)
  unfold closed. simpl. done.
Qed.

Lemma example_some_vars_closed:
  closed ["x"; "y"] (Plus' (Var "x") (Var "y")).
Proof.
  unfold closed. simpl. done.
Qed.

Lemma example_not_closed:
  ¬ closed ["x"] (Plus' (Var "x") (Var "y")).
Proof.
  unfold closed. simpl. done.
Qed.

Lemma closed_mono X Y e:
  X ⊆ Y → closed X e → closed Y e.
Proof.
  unfold closed. intros Hsub; induction e; simpl.
  - (* bool_decide is an stdpp function, which can be used to decide simple decidable propositions.
       Make a search for it to find the right lemmas to complete this subgoal. *)
    admit.
  - done.
  - (* Locate the notation for && by typing: Locate "&&". Then search for the right lemmas.*)
    admit.
  - admit.
Admitted.

(* we define a substitution operation on open expressions *)
Fixpoint subst (e: expr') (x: string) (e': expr') : expr' :=
  match e with
  | Var y => if (bool_decide (x = y)) then e' else Var y
  | Const' z => Const' z
  | Plus' e1 e2 => Plus' (subst e1 x e') (subst e2 x e')
  | Mul' e1 e2 => Mul' (subst e1 x e') (subst e2 x e')
  end.

Lemma subst_closed e e' x X:
  closed X e → ¬ (x ∈ X) → subst e x e' = e.
Proof. Admitted.


(* To evaluate an arithmetic expression, we define an evaluation function [expr_eval], which maps them to integers.
   Since our expressions contain variables, we pass a finite map as the argument, which is used to look up variables.
   The type of finite maps that we use is called [gmap].
*)
Fixpoint expr_eval' (m: gmap string Z) (e : expr') : Z :=
  match e with
  | Var x => default 0%Z (m !! x) (* this is the lookup operation on gmaps *)
  | Const' z => z
  | Plus' e1 e2 => (expr_eval' m e1) + (expr_eval' m e2)
  | Mul' e1 e2 => (expr_eval' m e1) * (expr_eval' m e2)
  end.

(* Prove the following lemma which explains how substitution interacts with evaluation *)
Lemma eval_subst_extend (m: gmap string Z) e x e':
  expr_eval' m (subst e x e') = expr_eval' (<[x := expr_eval' m e']> m) e.
Proof. Admitted.

