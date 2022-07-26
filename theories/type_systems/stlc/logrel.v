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


(** ** Definition of the logical relation. *)
(**
  In Coq, we need to make argument why the logical relation is well-defined precise:
  This holds true in particular for the mutual recursion between the value relation and the expression relation
   (note that the value relation is defined in terms of the expression relation, and vice versa).
  We therefore define a termination measure [mut_measure] that makes sure that for each recursive call, we either
   - decrease the size of the type
   - or switch from the expression case to the value case.

  We use the Equations package to define the logical relation, as it's tedious to make the termination
   argument work with Coq's built-in support for recursive functions---but under the hood, Equations also
   just encodes it as a Coq Fixpoint.
 *)
Inductive type_case : Set :=
  | expr_case | val_case.

(* The [type_size] function just structurally descends, essentially taking the size of the "type tree". *)
Equations type_size (t : type) : nat :=
  type_size Int := 1;
  type_size (Fun A B) := type_size A + type_size B + 1.
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
      ∀ v',
        type_interp val_case A v' →
        type_interp expr_case B (subst' x v' e);

  type_interp expr_case t e =>
    ∃ v, big_step e v ∧ type_interp val_case t v
}.
Next Obligation.
  (** [simp] is a tactic provided by [Equations]. It rewrites with the defining equations of the definition.
    [simpl]/[cbn] will NOT unfold definitions made with Equations.
   *)
  repeat simp mut_measure; simp type_size; lia.
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

Inductive sem_context_rel : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A v →
    sem_context_rel Γ θ →
    sem_context_rel (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.

Lemma sem_context_rel_vals Γ θ x A :
  sem_context_rel Γ θ →
  Γ !! x = Some A →
  ∃ e v, θ !! x = Some e ∧ to_val e = Some v ∧ 𝒱 A v.
Proof.
  induction 1 as [|Γ θ v y B Hvals Hctx IH].
  - naive_solver.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + do 2 eexists. split; first by rewrite lookup_insert.
      split; first by eapply to_of_val. done.
    + eapply IH in Hlook as (e & w & Hlook & He & Hval).
      do 2 eexists; split; first by rewrite lookup_insert_ne.
      split; first done. done.
Qed.

Lemma sem_context_rel_subset Γ θ :
  𝒢 Γ θ → dom Γ ⊆ dom θ.
Proof.
  intros Hctx. apply elem_of_subseteq. intros x (A & Hlook)%elem_of_dom.
  eapply sem_context_rel_vals in Hlook as (e & v & Hlook & Heq & Hval); last done.
  eapply elem_of_dom; eauto.
Qed.

Lemma sem_context_rel_closed Γ θ:
  𝒢 Γ θ → subst_closed [] θ.
Proof.
  induction 1; rewrite /subst_closed.
  - naive_solver.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_closed.
    + eapply IHsem_context_rel; last done.
Qed.

(** The semantic typing judgment *)
Definition sem_typed Γ e A :=
  ∀ θ, 𝒢 Γ θ → ℰ A (subst_map θ e).
Notation "Γ ⊨ e : A" := (sem_typed Γ e A) (at level 74, e, A at next level).

(** *** Compatibility lemmas *)
Lemma compat_int Γ z : Γ ⊨ (LitInt z) : Int.
Proof.
  intros θ _. simp type_interp.
  exists z. split; simpl.
  - constructor.
  - simp type_interp. eauto.
Qed.

Lemma compat_var Γ x A :
  Γ !! x = Some A →
  Γ ⊨ (Var x) : A.
Proof.
  intros Hx θ Hctx; simpl.
  eapply sem_context_rel_vals in Hx as (e & v & He & Heq & Hv); last done.
  rewrite He. simp type_interp. exists v. split; last done.
  rewrite -(of_to_val _ _ Heq).
  by apply big_step_vals.
Qed.

Lemma compat_app Γ e1 e2 A B :
  Γ ⊨ e1 : (A → B) →
  Γ ⊨ e2 : A →
  Γ ⊨ (e1 e2) : B.
Proof.
  intros Hfun Harg θ Hctx; simpl.
  specialize (Hfun _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (x & e & -> & Hcl & Hv1).
  specialize (Harg _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2 & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v. split; last done.
  eauto.
Qed.


(** Lambdas need to be closed by the context *)
Lemma compat_lam_named Γ x e A B X :
  closed X e →
  (X ⊆ elements (dom (<[x := A]> Γ))) →
  (<[ x := A ]> Γ) ⊨ e : B →
  Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ Hctxt. simpl.
  simp type_interp.
  assert (body_closed : closed [x] (subst_map (delete x θ) e)).
  { (* this proof is slightly technical, sadly *)
    eapply subst_map_closed'; first done.
    intros y Hel. destruct (decide (x = y)); first subst.
    - rewrite lookup_delete; set_solver.
    - rewrite lookup_delete_ne //=.
      eapply Hsub, elem_of_elements, elem_of_dom in Hel as [C Hlook].
      rewrite lookup_insert_ne //= in Hlook.
      eapply sem_context_rel_vals in Hlook as (e' & v & Hlook' & Hev & Hval); last done.
      rewrite Hlook'. eapply closed_weaken_nil.
      eapply of_to_val in Hev as <-.
      by eapply val_rel_closed.
  }
  exists ((λ: x, subst_map (delete x θ) e))%V.
  split; first by eauto.
  simp type_interp.
  eexists (BNamed x), _. split; first reflexivity.
  split; first done.

  intros v' Hv'.
  specialize (Hbody (<[ x := of_val v']> θ)).
  simpl. rewrite subst_subst_map; last by eapply sem_context_rel_closed.
  apply Hbody.
  apply sem_context_rel_insert; done.
Qed.

Lemma compat_add Γ e1 e2 :
  Γ ⊨ e1 : Int →
  Γ ⊨ e2 : Int →
  Γ ⊨ (e1 + e2) : Int.
Proof.
  intros He1 He2 θ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ Hctx). specialize (He2 _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  exists (z1 + z2)%Z. split.
  - constructor; done.
  - exists (z1 + z2)%Z. done.
Qed.

Lemma sem_soundness Γ e A :
  (Γ ⊢ e : A)%ty →
  Γ ⊨ e : A.
Proof.
  induction 1 as [ | Γ x e A B Hsyn IH | | | ].
  - by apply compat_var.
  - set (X := elements (dom (<[x := A]>Γ))).
    specialize (syn_typed_closed _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_named; last done.
    + apply Hcl. apply elem_of_elements.
    + done.
  - apply compat_int.
  - by eapply compat_app.
  - by apply compat_add.
Qed.

Lemma termination e A :
  (∅ ⊢ e : A)%ty →
  ∃ v, big_step e v.
Proof.
  intros Hsem%sem_soundness.
  specialize (Hsem ∅).
  simp type_interp in Hsem.
  rewrite subst_map_empty in Hsem.
  destruct Hsem as (v & Hbs & _); last eauto.
  constructor.
Qed.
