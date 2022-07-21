From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.stlc_extended Require Import lang notation parallel_subst types bigstep.
From Equations Require Export Equations.

(** * Logical relation for the extended STLC *)

Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A : type).

(** ** Definition of the logrel *)
(**
  In Coq, we need to make argument why the logical relation is well-defined precise:
  This holds true in particular for the mutual recursion between the value relation and the expression relation.
  We therefore define a termination measure [mut_measure] that makes sure that for each recursive call, we either
   - decrease the size of the type
   - or switch from the expression case to the value case.

  We use the Equations package to define the logical relation, as it's tedious to make the termination
   argument work with Coq's built-in support for recursive functions.
 *)
Inductive type_case : Set :=
  | expr_case | val_case.

Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size (A → B) := type_size A + type_size B + 1;
  type_size (A × B) := type_size A + type_size B + 1;
  type_size (A + B) := max (type_size A) (type_size B) + 1
.

Equations mut_measure (c : type_case) A : nat :=
  mut_measure expr_case A := 1 + type_size A;
  mut_measure val_case A := type_size A.

(** A semantic type consists of a value-predicate and a proof of closedness *)
Record sem_type := mk_ST {
  sem_type_car :> val → Prop;
  sem_type_closed_val v : sem_type_car v → is_closed [] (of_val v);
  }.

Implicit Types
  (τ : sem_type)
.

(** The logical relation *)
Equations type_interp (c : type_case) (t : type) (v : match c with val_case => val | expr_case => expr end) : Prop by wf (mut_measure c t) := {
  type_interp val_case Int v=>
    ∃ z : Z, v = #z ;
  type_interp val_case (A × B) v =>
    (* FIXME *)
    False ;
  type_interp val_case (A + B) v =>
    (* FIXME *)
    False;
  type_interp val_case (A → B) v =>
    ∃ x e, v = LamV x e ∧ is_closed (x :b: nil) e ∧
      ∀ v',
        type_interp val_case A v' →
        type_interp expr_case B (subst' x (of_val v') e);

  type_interp expr_case t e =>
    ∃ v, big_step e v ∧ type_interp val_case t v
}.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.
(* FIXME: after you have properly extended the definition of the logrel,
  you may want to uncomment this to solve the side conditions for well-formedness
  spawned by Equations. *)
(*Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.*)
(*Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.*)
(*Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.*)
(*Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.*)

(** Value relation and expression relation *)
Definition sem_val_rel A v := type_interp val_case A v.
Definition sem_expr_rel A e := type_interp expr_case A e.

Notation 𝒱 := sem_val_rel.
Notation ℰ := sem_expr_rel.

Lemma sem_expr_rel_of_val A v :
  ℰ A (of_val v) → 𝒱 A v.
Proof.
  simp type_interp.
  intros (v' & ->%big_step_val & Hv').
  apply Hv'.
Qed.

Lemma val_rel_is_closed v A:
  𝒱 A v → is_closed [] (of_val v).
Proof.
  induction A as [ | | A IH1 B IH2 | A IH1 B IH2] in v |-*; simp type_interp.
  - intros [z ->]. done.
  - intros (x & e & -> & ? & _). done.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
(*Qed.*)
Admitted.

(** Interpret a syntactic type *)
Program Definition interp_type A : sem_type := {|
  sem_type_car := 𝒱 A;
|}.
Next Obligation. by eapply val_rel_is_closed. Qed.

(* Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

(** Context relation *)
Inductive sem_context_rel : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A v →
    sem_context_rel Γ θ →
    sem_context_rel (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.

Lemma sem_context_rel_vals {Γ θ x A} :
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
  𝒢 Γ θ → subst_is_closed [] θ.
Proof.
  induction 1 as [ | Γ θ v x A Hv Hctx IH]; rewrite /subst_is_closed.
  - naive_solver.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_is_closed.
    + eapply IH; last done.
Qed.

(** Semantic typing judgment *)
Definition sem_typed Γ e A :=
  ∀ θ, 𝒢 Γ θ → ℰ A (subst_map θ e).
Notation "Γ ⊨ e : A" := (sem_typed Γ e A) (at level 74, e, A at next level).

(** ** Compatibility lemmas *)
Lemma compat_int Γ z : Γ ⊨ (Lit $ LitInt z) : Int.
Proof.
  intros θ _. simp type_interp.
  exists #z. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_var Γ x A :
  Γ !! x = Some A →
  Γ ⊨ (Var x) : A.
Proof.
  intros Hx θ Hctx; simpl.
  specialize (sem_context_rel_vals Hctx Hx) as (e & v & He & Heq & Hv).
  rewrite He. simp type_interp. exists v. split; last done.
  rewrite -(of_to_val _ _ Heq).
  by apply big_step_of_val.
Qed.

Lemma compat_app Γ e1 e2 A B :
  Γ ⊨ e1 : (A → B) →
  Γ ⊨ e2 : A →
  Γ ⊨ (e1 e2) : B.
Proof.
  intros Hfun Harg θ Hctx; simpl.

  specialize (Hfun _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (x & e & -> & Hv1).
  specialize (Harg _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2  & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v. split; last done.
  eauto.
Qed.

(** Lambdas need to be closed by the context *)
Lemma compat_lam_named Γ x e A B X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom (<[x := A]> Γ)) →
  (<[ x := A ]> Γ) ⊨ e : B →
  Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ Hctxt. simpl.
  simp type_interp.

  exists ((λ: x, subst_map (delete x θ) e))%V.
  split; first by eauto.
  simp type_interp.
  eexists (BNamed x), _. split_and!; first reflexivity.
  { eapply closed_subst_weaken; [ | | apply Hcl].
    - eapply subst_is_closed_subseteq; last by eapply sem_context_rel_closed.
      apply map_delete_subseteq.
    - intros y Hy%Hsub Hn. apply elem_of_list_singleton.
      apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
      destruct (decide (x = y)) as [<- | Hneq]; first done.
      rewrite lookup_delete_ne in Hn; last done.
      rewrite lookup_insert_ne in Hy; last done.
      apply sem_context_rel_subset in Hctxt.
      move: Hctxt. rewrite elem_of_subseteq.
      move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
      naive_solver.
  }

  intros v' Hv'.
  specialize (Hbody (<[ x := of_val v']> θ)).
  simpl. rewrite subst_subst_map.
  2: { by eapply sem_context_rel_closed. }
  apply Hbody.
  apply sem_context_rel_insert; done.
Qed.

Lemma compat_lam_anon Γ e A B X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  Γ ⊨ e : B →
  Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ Hctxt. simpl.
  simp type_interp.

  exists (λ: <>, subst_map θ e)%V.
  split; first by eauto.
  simp type_interp.
  eexists BAnon, _. split_and!; first reflexivity.
  { simpl.
    eapply closed_subst_weaken; [ | | apply Hcl].
    - by eapply sem_context_rel_closed.
    - intros y Hy%Hsub Hn.
      apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
      apply sem_context_rel_subset in Hctxt.
      move: Hctxt. rewrite elem_of_subseteq.
      move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
      naive_solver.
  }

  intros v' Hv'.
  specialize (Hbody θ).
  simpl. apply Hbody; done.
Qed.

Lemma compat_int_binop Γ op e1 e2 :
  bin_op_typed op Int Int Int →
  Γ ⊨ e1 : Int →
  Γ ⊨ e2 : Int →
  Γ ⊨ (BinOp op e1 e2) : Int.
Proof.
  intros Hop He1 He2 θ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ Hctx). specialize (He2 _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
Qed.

(* FIXME : add the necessary compatibility lemmas *)

Lemma sem_soundness Γ e A :
  Γ ⊢ e : A →
  Γ ⊨ e : A.
Proof.
  induction 1 as [ | Γ x e A B Hsyn IH | Γ e A B Hsyn IH| |  ].
  - by apply compat_var.
  - set (X := elements (dom (<[x := A]>Γ))).
    specialize (syn_typed_closed _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_named; last done.
    + apply Hcl. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - set (X := elements (dom Γ)).
    specialize (syn_typed_closed _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_anon; last done.
    + apply Hcl. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - apply compat_int.
  - by eapply compat_app.
  (* FIXME : extend according to your new typing rules. *)
Qed.
