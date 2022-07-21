From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts.
From semantics.systemf Require Import lang notation parallel_subst types bigstep.
From Equations Require Export Equations.


(** * Logical relation for SystemF *)

Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
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
  type_size Bool := 1;
  type_size Unit := 1;
  type_size (A → B) := type_size A + type_size B + 1;
  type_size (#α) := 1;
  type_size (∀: A) := type_size A + 2;
  type_size (∃: A) := type_size A + 2;
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
(** Two tactics we will use later on.
  [pose_sem_type P as N] defines a semantic type at name [N] with the value predicate [P].
  [specialize_sem_type S with P as N] specializes a universal quantifier over sem types in [S] with
    a semantic type with predicate [P], giving it the name [N].
 *)
(* slightly complicated formulation to make the proof term [p] opaque and prevent it from polluting the context *)
Tactic Notation "pose_sem_type" uconstr(P) "as" ident(N) :=
  let p := fresh "__p" in
  unshelve refine ((λ p, let N := (mk_ST P p) in _) _); first (simpl in p); cycle 1.
Tactic Notation "specialize_sem_type" constr(S) "with" uconstr(P) "as" ident(N) :=
  pose_sem_type P as N; last specialize (S N).

(** We represent type variable assignments [δ] as lists of semantic types.
  The variable #n (in De Bruijn representation) is mapped to the [n]-th element of the list.
 *)
Definition tyvar_interp := nat → sem_type.
Implicit Types
  (δ : tyvar_interp)
  (τ : sem_type)
.

(** The logical relation *)
Equations type_interp (c : type_case) (t : type) δ (v : match c with val_case => val | expr_case => expr end) : Prop by wf (mut_measure c t) := {
  type_interp val_case Int δ v=>
    ∃ z : Z, v = #z ;
  type_interp val_case Bool δ v =>
    ∃ b : bool, v = #b ;
  type_interp val_case Unit δ v =>
    v = #LitUnit ;
  type_interp val_case (A × B) δ v =>
    ∃ v1 v2 : val, v = (v1, v2)%V ∧ type_interp val_case A δ v1 ∧ type_interp val_case B δ v2;
  type_interp val_case (A + B) δ v =>
    (∃ v' : val, v = InjLV v' ∧ type_interp val_case A δ v') ∨
    (∃ v' : val, v = InjRV v' ∧ type_interp val_case B δ v');
  type_interp val_case (A → B) δ v =>
    ∃ x e, v = LamV x e ∧ is_closed (x :b: nil) e ∧
      ∀ v',
        type_interp val_case A δ v' →
        type_interp expr_case B δ (subst' x (of_val v') e);
  (** Type variable case *)
  type_interp val_case (#α) δ v =>
    (δ α).(sem_type_car) v;
  (** ∀ case *)
  type_interp val_case (∀: A) δ v =>
    ∃ e, v = TLamV e ∧ is_closed [] e ∧
      ∀ τ, type_interp expr_case A (τ .: δ) e;
  (** ∃ case *)
  type_interp val_case (∃: A) δ v =>
    ∃ v', v = PackV v' ∧
      ∃ τ : sem_type, type_interp val_case A (τ .: δ) v';

  type_interp expr_case t δ e =>
    ∃ v, big_step e v ∧ type_interp val_case t δ v
}.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.

(** Value relation and expression relation *)
Definition sem_val_rel A δ v := type_interp val_case A δ v.
Definition sem_expr_rel A δ e := type_interp expr_case A δ e.

Notation 𝒱 := sem_val_rel.
Notation ℰ := sem_expr_rel.

Lemma sem_expr_rel_of_val A δ v :
  ℰ A δ (of_val v) → 𝒱 A δ v.
Proof.
  simp type_interp.
  intros (v' & ->%big_step_val & Hv').
  apply Hv'.
Qed.

Lemma val_rel_is_closed v δ A:
  𝒱 A δ v → is_closed [] (of_val v).
Proof.
  induction A as [ | | | | | A IHA | | A IH1 B IH2 | A IH1 B IH2] in v, δ |-*; simp type_interp.
  - by eapply sem_type_closed_val.
  - intros [z ->]. done.
  - intros [b ->]. done.
  - intros ->. done.
  - intros (e & -> & ? & _). done.
  - intros (v' & -> & (τ & Hinterp)). simpl. by eapply IHA.
  - intros (x & e & -> & ? & _). done.
  - intros (v1 & v2 & -> & ? & ?). simpl; apply andb_True; split; eauto.
  - intros [(v' & -> & ?) | (v' & -> & ?)]; simpl; eauto.
Qed.

(** Interpret a syntactic type *)
Program Definition interp_type A δ : sem_type := {|
  sem_type_car := 𝒱 A δ;
|}.
Next Obligation. by eapply val_rel_is_closed. Qed.

(* Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

(** Context relation *)
Inductive sem_context_rel (δ : tyvar_interp) : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel δ ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A δ v →
    sem_context_rel δ Γ θ →
    sem_context_rel δ (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.

Lemma sem_context_rel_vals {δ Γ θ x A} :
  sem_context_rel δ Γ θ →
  Γ !! x = Some A →
  ∃ e v, θ !! x = Some e ∧ to_val e = Some v ∧ 𝒱 A δ v.
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

Lemma sem_context_rel_subset δ Γ θ :
  𝒢 δ Γ θ → dom Γ ⊆ dom θ.
Proof.
  intros Hctx. apply elem_of_subseteq. intros x (A & Hlook)%elem_of_dom.
  eapply sem_context_rel_vals in Hlook as (e & v & Hlook & Heq & Hval); last done.
  eapply elem_of_dom; eauto.
Qed.

Lemma sem_context_rel_closed δ Γ θ:
  𝒢 δ Γ θ → subst_is_closed [] θ.
Proof.
  induction 1 as [ | Γ θ v x A Hv Hctx IH]; rewrite /subst_is_closed.
  - naive_solver.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_is_closed.
    + eapply IH; last done.
Qed.

(** Semantic typing judgment *)
Definition sem_typed Δ Γ e A :=
  ∀ θ δ, 𝒢 δ Γ θ → ℰ A δ (subst_map θ e).
Notation "'TY' Δ ;  Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).

Section boring_lemmas.
  (** The lemmas in this section are all quite boring and expected statements,
    but are quite technical to prove due to De Bruijn binders.
    We encourage to skip over the proofs of these lemmas.
  *)

  Lemma sem_val_rel_ext B δ δ' v :
    (∀ n v, δ n v ↔ δ' n v) →
    𝒱 B δ v ↔ 𝒱 B δ' v.
  Proof.
    induction B in δ, δ', v |-*; simpl; simp type_interp; eauto; intros Hiff.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros x.
      eapply if_iff; first eauto.
      simp type_interp. f_equiv. intros ?. f_equiv.
      eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; eauto.
    - f_equiv; f_equiv; intros ?; f_equiv; eauto.
  Qed.


  Lemma sem_val_rel_move_ren B δ σ v :
     𝒱 B (λ n, δ (σ n)) v ↔ 𝒱 (rename σ B) δ v.
  Proof.
    induction B in σ, δ, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u; asimpl; done.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl. done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros x.
      eapply if_iff; first done.
      simp type_interp. f_equiv. intros ?. f_equiv.
      done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
    - f_equiv; f_equiv; intros ?; f_equiv; done.
  Qed.


  Lemma sem_val_rel_move_subst B δ σ v :
    𝒱 B (λ n, interp_type (σ n) δ) v ↔ 𝒱 (B.[σ]) δ v.
  Proof.
    induction B in σ, δ, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl.
        etransitivity; last eapply sem_val_rel_move_ren.
        simpl. done.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl.
        etransitivity; last eapply sem_val_rel_move_ren.
        simpl. done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros x.
      eapply if_iff; first done.
      simp type_interp. f_equiv. intros ?. f_equiv.
      done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
    - f_equiv; f_equiv; intros ?; f_equiv; done.
  Qed.

  Lemma sem_val_rel_move_single_subst A B δ v :
    𝒱 B (interp_type A δ .: δ) v ↔ 𝒱 (B.[A/]) δ v.
  Proof.
    rewrite -sem_val_rel_move_subst. eapply sem_val_rel_ext.
    intros [| n] w; simpl; done.
  Qed.

  Lemma sem_val_rel_cons A δ v τ :
    𝒱 A δ v ↔ 𝒱  A.[ren (+1)] (τ .: δ) v.
  Proof.
    rewrite -sem_val_rel_move_subst; simpl.
    eapply sem_val_rel_ext; done.
  Qed.

  Lemma sem_context_rel_cons Γ δ θ τ :
    𝒢 δ Γ θ →
    𝒢 (τ .: δ) (⤉ Γ) θ.
  Proof.
    induction 1 as [ | Γ θ v x A Hv Hctx IH]; simpl.
    - rewrite fmap_empty. constructor.
    - rewrite fmap_insert. constructor; last done.
      rewrite -sem_val_rel_cons. done.
  Qed.
End boring_lemmas.

(** ** Compatibility lemmas *)

Lemma compat_int Δ Γ z : TY Δ; Γ ⊨ (Lit $ LitInt z) : Int.
Proof.
  intros θ δ _. simp type_interp.
  exists #z. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_bool Δ Γ b : TY Δ; Γ ⊨ (Lit $ LitBool b) : Bool.
Proof.
  intros θ δ _. simp type_interp.
  exists #b. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_unit Δ Γ : TY Δ; Γ ⊨ (Lit $ LitUnit) : Unit.
Proof.
  intros θ δ _. simp type_interp.
  exists #LitUnit. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_var Δ Γ x A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ (Var x) : A.
Proof.
  intros Hx θ δ Hctx; simpl.
  specialize (sem_context_rel_vals Hctx Hx) as (e & v & He & Heq & Hv).
  rewrite He. simp type_interp. exists v. split; last done.
  rewrite -(of_to_val _ _ Heq).
  by apply big_step_of_val.
Qed.

Lemma compat_app Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : (A → B) →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (e1 e2) : B.
Proof.
  intros Hfun Harg θ δ Hctx; simpl.

  specialize (Hfun _ _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (x & e & -> & Hv1).
  specialize (Harg _ _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2  & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v. split; last done.
  eauto.
Qed.

(** Lambdas need to be closed by the context *)
Lemma compat_lam_named Δ Γ x e A B X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom (<[x := A]> Γ)) →
  TY Δ; (<[ x := A ]> Γ) ⊨ e : B →
  TY Δ; Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ δ Hctxt. simpl.
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
  apply Hbody. apply sem_context_rel_insert; done.
Qed.

Lemma compat_lam_anon Δ Γ e A B X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ δ Hctxt. simpl.
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

Lemma compat_int_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Int →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Int.
Proof.
  intros Hop He1 He2 θ δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). specialize (He2 _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(z1 + z2)%Z. split.
    - econstructor; done.
    - exists (z1 + z2)%Z. done.
  + exists #(z1 - z2)%Z. split.
    - econstructor; done.
    - exists (z1 - z2)%Z. done.
  + exists #(z1 * z2)%Z. split.
    - econstructor; done.
    - exists (z1 * z2)%Z. done.
Qed.

Lemma compat_int_bool_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Bool →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Bool.
Proof.
  intros Hop He1 He2 θ δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). specialize (He2 _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(bool_decide (z1 < z2))%Z. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 ≤ z2))%Z. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 = z2))%Z. split.
    - econstructor; done.
    - eexists _. done.
Qed.

Lemma compat_unop Δ Γ op A B e :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ (UnOp op e) : B.
Proof.
  intros Hop He θ δ Hctx. simpl.
  simp type_interp. specialize (He _ _ Hctx).
  simp type_interp in He.

  destruct He as (v & Hb & Hv).
  inversion Hop; subst; simp type_interp in Hv.
  - destruct Hv as (b & ->).
    exists #(negb b). split.
    + econstructor; done.
    + by eexists _.
  - destruct Hv as (z & ->).
    exists #(-z)%Z. split.
    + econstructor; done.
    + by eexists _.
Qed.

Lemma compat_tlam Δ Γ e A X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  TY S Δ; (⤉ Γ) ⊨ e : A →
  TY Δ; Γ ⊨ (Λ, e) : (∀: A).
Proof.
  intros Hcl Hsub He θ δ Hctx. simpl.
  simp type_interp.
  exists (Λ, subst_map θ e)%V.
  split; first constructor.

  simp type_interp.
  eexists _. split_and!; first done.
  { eapply closed_subst_weaken; [ | | apply Hcl].
    - by eapply sem_context_rel_closed.
    - intros y Hy%Hsub Hn. exfalso.
      apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
      apply sem_context_rel_subset in Hctx.
      move: Hctx. rewrite elem_of_subseteq.
      move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
      naive_solver.
  }
  intros τ. eapply He.
  by eapply sem_context_rel_cons.
Qed.

Lemma compat_tapp Δ Γ e A B :
  type_wf Δ B →
  TY Δ; Γ ⊨ e : (∀: A) →
  TY Δ; Γ ⊨ (e <>) : (A.[B/]).
Proof.
  (* TODO: exercise for you *)
Admitted.
(*Qed.*)

Lemma compat_pack Δ Γ e n A B :
  type_wf n B →
  type_wf (S n) A →
  TY n; Γ ⊨ e : A.[B/] →
  TY n; Γ ⊨ (pack e) : (∃: A).
Proof.
  (* TODO: this will be an exercise for you soon. *)
(*Qed.*)
Admitted.

Lemma compat_unpack n Γ A B e e' x :
  type_wf n B →
  TY n; Γ ⊨ e : (∃: A) →
  TY S n; <[x:=A]> (⤉Γ) ⊨ e' : B.[ren (+1)] →
  TY n; Γ ⊨ (unpack e as BNamed x in e') : B.
Proof.
  (* TODO: this will be an exercise for you soon *)
(*Qed.*)
Admitted.

Lemma compat_if n Γ e0 e1 e2 A :
  TY n; Γ ⊨ e0 : Bool →
  TY n; Γ ⊨ e1 : A →
  TY n; Γ ⊨ e2 : A →
  TY n; Γ ⊨ (if: e0 then e1 else e2) : A.
Proof.
  intros He0 He1 He2 θ δ Hctx. simpl.
  simp type_interp.
  specialize (He0 _ _ Hctx). simp type_interp in He0.
  specialize (He1 _ _ Hctx). simp type_interp in He1.
  specialize (He2 _ _ Hctx). simp type_interp in He2.

  destruct He0 as (v0 & Hb0 & Hv0). simp type_interp in Hv0. destruct Hv0 as (b & ->).
  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).

  destruct b.
  - exists v1. split; first by repeat econstructor. done.
  - exists v2. split; first by repeat econstructor. done.
Qed.

Lemma compat_pair Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : A →
  TY Δ; Γ ⊨ e2 : B →
  TY Δ; Γ ⊨ (e1, e2) : A × B.
Proof.
  intros He1 He2 θ δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). simp type_interp in He1.
  destruct He1 as (v1 & Hb1 & Hv1).
  specialize (He2 _ _ Hctx). simp type_interp in He2.
  destruct He2 as (v2 & Hb2 & Hv2).
  exists (v1, v2)%V. split; first eauto.
  simp type_interp. exists v1, v2. done.
Qed.

Lemma compat_fst Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Fst e : A.
Proof.
  intros He θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v1. split; first eauto. done.
Qed.

Lemma compat_snd Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Snd e : B.
Proof.
  intros He θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v2. split; first eauto. done.
Qed.

Lemma compat_injl Δ Γ e A B :
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ InjL e : A + B.
Proof.
  intros He θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  exists (InjLV v). split; first eauto.
  simp type_interp. eauto.
Qed.

Lemma compat_injr Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ InjR e : A + B.
Proof.
  intros He θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  exists (InjRV v). split; first eauto.
  simp type_interp. eauto.
Qed.

Lemma compat_case Δ Γ e e1 e2 A B C :
  TY Δ; Γ ⊨ e : B + C →
  TY Δ; Γ ⊨ e1 : (B → A) →
  TY Δ; Γ ⊨ e2 : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 : A.
Proof.
  intros He He1 He2 θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as [(v' & -> & Hv') | (v' & -> & Hv')].
  - specialize (He1 _ _ Hctx). simp type_interp in He1.
    destruct He1 as (v & Hb' & Hv).
    simp type_interp in Hv. destruct Hv as (x & e' & -> & Cl & Hv).
    apply Hv in Hv'. simp type_interp in Hv'. destruct Hv' as (v & Hb'' & Hv'').
    exists v. split; last done.
    econstructor; first done.
    econstructor; [done | apply big_step_of_val; done | done].
  - specialize (He2 _ _ Hctx). simp type_interp in He2.
    destruct He2 as (v & Hb' & Hv).
    simp type_interp in Hv. destruct Hv as (x & e' & -> & Cl & Hv).
    apply Hv in Hv'. simp type_interp in Hv'. destruct Hv' as (v & Hb'' & Hv'').
    exists v. split; last done.
    econstructor; first done.
    econstructor; [done | apply big_step_of_val; done | done].
Qed.

Lemma sem_soundness Δ Γ e A :
  TY Δ; Γ ⊢ e : A →
  TY Δ; Γ ⊨ e : A.
Proof.
  induction 1 as [ | Δ Γ x e A B Hsyn IH | Δ Γ e A B Hsyn IH| Δ Γ e A Hsyn IH| | | | |  | | | | n Γ e1 e2 op A B C Hop ? ? ? ? | | | | | | | ].
  - by apply compat_var.
  - set (X := elements (dom (<[x := A]>Γ))).
    specialize (syn_typed_closed _ _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_named; last done.
    + apply Hcl. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - set (X := elements (dom Γ)).
    specialize (syn_typed_closed _ _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_anon; last done.
    + apply Hcl. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - set (X := elements (dom Γ)).
    specialize (syn_typed_closed _ _ _ _ X Hsyn) as Hcl.
    eapply compat_tlam; last done.
    + apply Hcl. rewrite dom_fmap. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - apply compat_tapp; done.
  - eapply compat_pack; done.
  - eapply compat_unpack; done.
  - apply compat_int.
  - by eapply compat_bool.
  - by eapply compat_unit.
  - by eapply compat_if.
  - by eapply compat_app.
  - inversion Hop; subst.
    1-3: by apply compat_int_binop.
    1-3: by apply compat_int_bool_binop.
  - by eapply compat_unop.
  - by apply compat_pair.
  - by eapply compat_fst.
  - by eapply compat_snd.
  - by eapply compat_injl.
  - by eapply compat_injr.
  - by eapply compat_case.
Qed.

(* dummy delta which we can use if we don't care *)
Program Definition any_type : sem_type := {| sem_type_car := λ v, is_closed [] v |}.
Definition δ_any : var → sem_type := λ _, any_type.

Lemma termination e A :
  (TY 0; ∅ ⊢ e : A)%ty →
  ∃ v, big_step e v.
Proof.
  intros Hsem%sem_soundness.
  specialize (Hsem ∅ δ_any).
  simp type_interp in Hsem.
  rewrite subst_map_empty in Hsem.
  destruct Hsem as (v & Hbs & _); last eauto.
  constructor.
Qed.
