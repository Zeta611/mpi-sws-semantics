From stdpp Require Import base relations.
From iris Require Import prelude.
From semantics.lib Require Import sets maps.
From semantics.ts.stlc Require Import lang notation types parallel_subst.
From Equations Require Import Equations.

Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A : type).

(** *** Big-Step Semantics for cbn *)
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
      big_step (subst' x e2 e) v →
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



(** ** Definition of the logical relation. *)
(**
  In Coq, we need to make argument why the logical relation is well-defined precise:
  This holds true in particular for the mutual recursion between the value relation and the expression relation
   (note that the value relation is defined in terms of the expression relation, and vice versa).
  We therefore define a termination measure [mut_measure] that makes sure that for each recursive call, we either
   - decrease the size of the type
   - or switch from the expression case to the value case.

  We use the Equations package to define the logical relation, as it's tedious to make the termination
   argument work with Coq's built-in support for recursive functions---but under the hood, the Equations also
   just encodes it as a Coq Fixpoint.
 *)
Inductive type_case : Set :=
  | expr_case | val_case.

(* The [type_size] function just structurally descends, essentially taking the size of the "type tree". *)
Equations type_size (t : type) : nat :=
  type_size Int := 1;
  type_size (Fun A B) := type_size A + type_size B + 2.
(* The definition of the expression relation uses the value relation -- therefore, it needs to be larger, and we add [1]. *)
Equations mut_measure (c : type_case) (t : type) : nat :=
  mut_measure expr_case t := 1 + type_size t;
  mut_measure val_case t := type_size t.

Definition sem_type : Type := val → Prop.

(** The main definition of the logical relation.
  To handle the mutual recursion, both the expression and value relation are handled by one definition, with [type_case] determining the case.

   The argument [v] has a type that is determined by the case of the relation (so the whole thing is dependently-typed).
   The [by wf ..] part tells Equations to use [mut_measure] for the well-formedness argument.
 *)
Equations type_interp (c : type_case) (t : type) (v : match c with val_case => val | expr_case => expr end) : Prop by wf (mut_measure c t) := {
  type_interp val_case Int v =>
    ∃ z : Z, v = z ;
  type_interp val_case (A → B) v =>
    ∃ x e, v = @LamV x e ∧ closed (x :b: nil) e ∧
      ∀ e',
        type_interp expr_case A e' →
        type_interp expr_case B (subst' x e' e);

  type_interp expr_case t e =>
    (* NOTE: we now need to explicitly require that expressions here are closed. *)
    ∃ v, big_step e v ∧ closed [] e ∧ type_interp val_case t v
}.
Next Obligation.
  (** [simp] is a tactic provided by [Equations]. It rewrites with the defining equations of the definition.
    [simpl]/[cbn] will NOT unfold definitions made with Equations.
   *)
  repeat simp mut_measure; simp type_size. lia.
Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.

(** We derive the expression/value relation. *)
Definition sem_val_rel t v := type_interp val_case t v.
Definition sem_expr_rel t e := type_interp expr_case t e.

Notation 𝒱 := sem_val_rel.
Notation ℰ := sem_expr_rel.

Lemma val_rel_closed v A:
  𝒱 A v → closed [] v.
Proof.
  induction A; simp type_interp.
  - intros [z ->]. done.
  - intros (x & e & -> & Hcl & _). done.
Qed.

Lemma expr_rel_closed e A :
  ℰ A e → closed [] e.
Proof.
  simp type_interp. intros (v & ? & ? & _); done.
Qed.

Lemma sem_expr_rel_of_val A v:
  ℰ A v → 𝒱 A v.
Proof.
  simp type_interp.
  intros (v' & ->%big_step_inv_vals & Hv').
  apply Hv'.
Qed.

(** Interpret a type *)
Definition interp_type A : sem_type := 𝒱 A.

(** *** Semantic typing of contexts *)
(** Substitutions map to expressions -- this is so that we can more easily reuse notions like closedness *)
Implicit Types
  (θ : gmap string expr).

(* NOTE: our context now contains expressions. *)
Inductive sem_context_rel : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel ∅ ∅
  | sem_context_rel_insert Γ θ e x A :
    ℰ A e →
    sem_context_rel Γ θ →
    sem_context_rel (<[x := A]> Γ) (<[x := e]> θ).

Notation 𝒢 := sem_context_rel.

Lemma sem_context_rel_exprs Γ θ x A :
  sem_context_rel Γ θ →
  Γ !! x = Some A →
  ∃ e, θ !! x = Some e ∧ ℰ A e.
Proof.
  induction 1 as [|Γ θ e y B Hvals Hctx IH].
  - naive_solver.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + eexists; first by rewrite lookup_insert.
    + eapply IH in Hlook as (e' & Hlook & He).
      eexists; split; first by rewrite lookup_insert_ne.
      done.
Qed.

Lemma sem_context_rel_subset Γ θ :
  𝒢 Γ θ → dom Γ ⊆ dom θ.
Proof.
  intros Hctx. apply elem_of_subseteq. intros x (A & Hlook)%elem_of_dom.
  eapply sem_context_rel_exprs in Hlook as (e & Hlook & He); last done.
  eapply elem_of_dom; eauto.
Qed.

Lemma sem_context_rel_closed Γ θ:
  𝒢 Γ θ → subst_closed [] θ.
Proof.
  induction 1; rewrite /subst_closed.
  - naive_solver.
  - intros y e'. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply expr_rel_closed.
    + eapply IHsem_context_rel; last done.
Qed.

(** The semantic typing judgment *)
Definition sem_typed Γ e A :=
  ∀ θ, 𝒢 Γ θ → ℰ A (subst_map θ e).
Notation "Γ ⊨ e : A" := (sem_typed Γ e A) (at level 74, e, A at next level).


Lemma termination e A :
  (∅ ⊢ e : A)%ty →
  ∃ v, big_step e v.
Proof.
  (* FIXME: prove this.
    You may want to add suitable intermediate lemmas, just as for the cbv logrel
      seen in the lecture. 
  *)
(*Qed.*)
Admitted.
