From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts maps.
From semantics.ts.systemf_mu_state Require Import lang notation parallel_subst execution.
From Equations Require Export Equations.
From Autosubst Require Export Autosubst.

(** * Logical relation for SystemF + recursive types *)

(** ** First-order typing for heaps *)
(* We have to explicitly specify the type of first-order types here.

  One alternative approach would be to just require first-orderness in the ref case of the logrel,
  but this breaks the boring lemma about moving substitution: (A.[σ]) might be first-order
  even if A is not (because it contains a type variable), so we fail to prove the equivalence.
  Explicitly defining fotypes in this way prevents type substitution from going below Ref entirely,
  which fixes this problem.
*)

Inductive fotype : Type :=
  | FOInt
  | FOBool
  | FOUnit
  | FOProd (A B : fotype)
  | FOSum (A B : fotype).

Inductive type : Type :=
  (** [var] is the type of variables of Autosubst -- it unfolds to [nat] *)
  | TVar : var → type
  | Int
  | Bool
  | Unit
  (** The [{bind 1 of type}] tells Autosubst to put a De Bruijn binder here *)
  | TForall : {bind 1 of type} → type
  | TExists : {bind 1 of type} → type
  | Fun (A B : type)
  | Prod (A B : type)
  | Sum (A B : type)
  | TMu : {bind 1 of type} → type
  | Ref (a : fotype)
.

Fixpoint of_fotype (a : fotype) : type :=
  match a with
  | FOInt => Int
  | FOBool => Bool
  | FOUnit => Unit
  | FOProd a b => Prod (of_fotype a) (of_fotype b)
  | FOSum a b => Sum (of_fotype a) (of_fotype b)
  end.
Coercion of_fotype : fotype >-> type.

(** Autosubst instances.
  This lets Autosubst do its magic and derive all the substitution functions, etc.
 *)
#[export] Instance Ids_type : Ids type. derive. Defined.
#[export] Instance Rename_type : Rename type. derive. Defined.
#[export] Instance Subst_type : Subst type. derive. Defined.
#[export] Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition typing_context := gmap string type.
Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A B : type)
  (* we use lower-case letters for first-order types *)
  (a : fotype)
.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Notation "# x" := (TVar x) : FType_scope.
Infix "→" := Fun : FType_scope.
Notation "(→)" := Fun (only parsing) : FType_scope.
Notation "∀: τ" :=
  (TForall τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Infix "×" := Prod (at level 70) : FType_scope.
Notation "(×)" := Prod (only parsing) : FType_scope.
Infix "+" := Sum : FType_scope.
Notation "(+)" := Sum (only parsing) : FType_scope.
Notation "μ: A" :=
  (TMu A%ty)
  (at level 100, A at level 200) : FType_scope.

Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)) <$> Γ) (at level 10, format "⤉ Γ").

Implicit Types
  (α : var)
.
Inductive type_wf : nat → type → Prop :=
  | type_wf_TVar m n:
      m < n →
      type_wf n (TVar m)
  | type_wf_Int n: type_wf n Int
  | type_wf_Bool n : type_wf n Bool
  | type_wf_Unit n : type_wf n Unit
  | type_wf_TForall n A :
      type_wf (S n) A →
      type_wf n (TForall A)
  | type_wf_TExists n A :
      type_wf (S n) A →
      type_wf n (TExists A)
  | type_wf_Fun n A B:
      type_wf n A →
      type_wf n B →
      type_wf n (Fun A B)
  | type_wf_Prod n A B :
      type_wf n A →
      type_wf n B →
      type_wf n (Prod A B)
  | type_wf_Sum n A B :
      type_wf n A →
      type_wf n B →
      type_wf n (Sum A B)
  | type_wf_mu n A :
      type_wf (S n) A →
      type_wf n (μ: A)
  | type_wf_ref n a :
      type_wf n (Ref a).
#[export] Hint Constructors type_wf : core.

Inductive bin_op_typed : bin_op → type → type → type → Prop :=
  | plus_op_typed : bin_op_typed PlusOp Int Int Int
  | minus_op_typed : bin_op_typed MinusOp Int Int Int
  | mul_op_typed : bin_op_typed MultOp Int Int Int
  | lt_op_typed : bin_op_typed LtOp Int Int Bool
  | le_op_typed : bin_op_typed LeOp Int Int Bool
  | eq_op_typed : bin_op_typed EqOp Int Int Bool.
#[export] Hint Constructors bin_op_typed : core.

Inductive un_op_typed : un_op → type → type → Prop :=
  | neg_op_typed : un_op_typed NegOp Bool Bool
  | minus_un_op_typed : un_op_typed MinusUnOp Int Int.

Reserved Notation "'TY' Δ ;  Γ ⊢ e : A" (at level 74, e, A at next level).
Inductive syn_typed : nat → typing_context → expr → type → Prop :=
  | typed_var n Γ x A :
      Γ !! x = Some A →
      TY n; Γ ⊢ (Var x) : A
  | typed_lam n Γ x e A B :
      TY n ; (<[ x := A]> Γ) ⊢ e : B →
      type_wf n A →
      TY n; Γ ⊢ (Lam (BNamed x) e) : (A → B)
  | typed_lam_anon n Γ e A B :
      TY n ; Γ ⊢ e : B →
      type_wf n A →
      TY n; Γ ⊢ (Lam BAnon e) : (A → B)
  | typed_tlam n Γ e A :
      (* we need to shift the context up as we descend under a binder *)
      TY S n; (⤉ Γ) ⊢ e : A →
      TY n; Γ ⊢ (Λ, e) : (∀: A)
  | typed_tapp n Γ A B e :
      TY n; Γ ⊢ e : (∀: A) →
      type_wf n B →
      (* A.[B/] is the notation for Autosubst's substitution operation that
        replaces variable 0 by [B] *)
      TY n; Γ ⊢ (e <>) : (A.[B/])
  | typed_pack n Γ A B e :
      type_wf n B →
      type_wf (S n) A →
      TY n; Γ ⊢ e : (A.[B/]) →
      TY n; Γ ⊢ (pack e) : (∃: A)
  | typed_unpack n Γ A B e e' x :
      type_wf n B → (* we should not leak the existential! *)
      TY n; Γ ⊢ e : (∃: A) →
      (* As we descend under a type variable binder for the typing of [e'],
          we need to shift the indices in [Γ] and [B] up by one.
        On the other hand, [A] is already defined under this binder, so we need not shift it.
      *)
      TY (S n); (<[x := A]>(⤉Γ)) ⊢ e' : (B.[ren (+1)]) →
      TY n; Γ ⊢ (unpack e as BNamed x in e') : B
  | typed_int n Γ z : TY n; Γ ⊢ (Lit $ LitInt z) : Int
  | typed_bool n Γ b : TY n; Γ ⊢ (Lit $ LitBool b) : Bool
  | typed_unit n Γ : TY n; Γ ⊢ (Lit $ LitUnit) : Unit
  | typed_if n Γ e0 e1 e2 A :
      TY n; Γ ⊢ e0 : Bool →
      TY n; Γ ⊢ e1 : A →
      TY n; Γ ⊢ e2 : A →
      TY n; Γ ⊢ If e0 e1 e2 : A
  | typed_app n Γ e1 e2 A B :
      TY n; Γ ⊢ e1 : (A → B) →
      TY n; Γ ⊢ e2 : A →
      TY n; Γ ⊢ (e1 e2)%E : B
  | typed_binop n Γ e1 e2 op A B C :
      bin_op_typed op A B C →
      TY n; Γ ⊢ e1 : A →
      TY n; Γ ⊢ e2 : B →
      TY n; Γ ⊢ BinOp op e1 e2 : C
  | typed_unop n Γ e op A B :
      un_op_typed op A B →
      TY n; Γ ⊢ e : A →
      TY n; Γ ⊢ UnOp op e : B
  | typed_pair n Γ e1 e2 A B :
      TY n; Γ ⊢ e1 : A →
      TY n; Γ ⊢ e2 : B →
      TY n; Γ ⊢ (e1, e2) : A × B
  | typed_fst n Γ e A B :
      TY n; Γ ⊢ e : A × B →
      TY n; Γ ⊢ Fst e : A
  | typed_snd n Γ e A B :
      TY n; Γ ⊢ e : A × B →
      TY n; Γ ⊢ Snd e : B
  | typed_injl n Γ e A B :
      type_wf n B →
      TY n; Γ ⊢ e : A →
      TY n; Γ ⊢ InjL e : A + B
  | typed_injr n Γ e A B :
      type_wf n A →
      TY n; Γ ⊢ e : B →
      TY n; Γ ⊢ InjR e : A + B
  | typed_case n Γ e e1 e2 A B C :
      TY n; Γ ⊢ e : B + C →
      TY n; Γ ⊢ e1 : (B → A) →
      TY n; Γ ⊢ e2 : (C → A) →
      TY n; Γ ⊢ Case e e1 e2 : A
  | typed_roll n Γ e A :
      TY n; Γ ⊢ e : (A.[(μ: A)/]) →
      TY n; Γ ⊢ (roll e) : (μ: A)
  | typed_unroll n Γ e A :
      TY n; Γ ⊢ e : (μ: A) →
      TY n; Γ ⊢ (unroll e) : (A.[(μ: A)/])
  (** Typing rules for state *)
  (* We use lower-case letters, which imposes the requirement to use first-order types.
     (The coercion [of_fotype] does a lot of work here.) *)
  | typed_load n Γ e a :
      TY n; Γ ⊢ e : (Ref a) →
      TY n; Γ ⊢ !e : a
  | typed_store n Γ e1 e2 a :
      TY n; Γ ⊢ e1 : (Ref a) →
      TY n; Γ ⊢ e2 : a →
      TY n; Γ ⊢ (e1 <- e2) : Unit
  | typed_new n Γ e a :
      TY n; Γ ⊢ e : a →
      TY n; Γ ⊢ (new e) : Ref a
where "'TY'  Δ ;  Γ ⊢ e : A" := (syn_typed Δ Γ e%E A%ty).
#[export] Hint Constructors syn_typed : core.

Lemma syn_typed_closed Δ Γ e A X :
  TY Δ; Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  induction 1 as [ | ??????? IH | | n Γ e A H IH | | | n Γ A B e e' x Hwf H1 IH1 H2 IH2 | | | | | | | | | | | | | | | | | | ] in X |-*; simpl; intros Hx; try done.
  { (* var *) apply bool_decide_pack, Hx. apply elem_of_dom; eauto. }
  { (* lam *) apply IH.
    intros y. rewrite elem_of_dom lookup_insert_is_Some.
    intros [<- | [? Hy]]; first by apply elem_of_cons; eauto.
    apply elem_of_cons. right. eapply Hx. by apply elem_of_dom.
  }
  { (* anon lam *) naive_solver. }
  { (* tlam *)
    eapply IH. intros x Hel. apply Hx.
    by rewrite dom_fmap in Hel.
  }
  3: { (* unpack *)
    apply andb_True; split.
    - apply IH1. apply Hx.
    - apply IH2. intros y. rewrite elem_of_dom lookup_insert_is_Some.
    intros [<- | [? Hy]]; first by apply elem_of_cons; eauto.
    apply elem_of_cons. right. eapply Hx.
    apply elem_of_dom. revert Hy. rewrite lookup_fmap fmap_is_Some. done.
  }
  (* everything else *)
  all: repeat match goal with
              | |- Is_true (_ && _)  => apply andb_True; split
              end.
  all: try naive_solver.
Qed.

Goal TY 0; ∅ ⊢ (λ: "x", #1 + "x") : (Int → Int).
Proof. eauto. Qed.
Goal TY 0; ∅ ⊢ (Λ, λ: "x", "x") : (∀: #0 → #0).
Proof. eauto 8. Qed.
Goal TY 0; ∅ ⊢ (new #42 <- #1337) : Unit.
Proof. eapply (typed_store _ _ _ _ FOInt); eauto. Qed.

(** ** Worlds *)
(** We represent heap invariants as predicates on heaps,
  and worlds as lists of such invariants.
 *)
Definition heap_inv := heap → Prop.
Definition world := list heap_inv.
Implicit Types (W : world) (INV : heap_inv).
(** [W'] extends [W] if [W] is a suffix of [W'] *)
Definition wext W W' := suffix W W'.
Notation "W' ⊒ W" := (wext W W') (at level 40).
#[export] Instance wext_preorder : PreOrder wext.
Proof. apply _. Qed.

(** Satisfaction is defined straightforwardly by recursion.
  We use map difference ∖ that computes the difference of two maps
  based on the domain.
 *)
Fixpoint wsat W σ :=
  match W with
  | INV :: W' =>
    ∃ σ0, INV σ0 ∧ σ0 ⊆ σ ∧ wsat W' (σ ∖ σ0)
  | [] => True
  end.

Lemma wsat_mono σ σ' W :
  σ ⊆ σ' →
  wsat W σ → wsat W σ'.
Proof.
  induction W as [ | INV W' IH] in σ, σ' |-*; first done.
  simpl. intros Hincl (σ0 & Hinv & Hincl' & Hsat).
  exists σ0; split; first done. split; first by etrans.
  eapply IH; last done.
  by apply map_difference_mono.
Qed.

Lemma wsat_wext W W' σ :
  W' ⊒ W →
  wsat W' σ →
  wsat W σ.
Proof.
  intros (L & ->). induction L as [ | INV L' IH] in σ |-*; first done.
  simpl. intros (σ0 & Hinv & Hincl & ?%IH). eapply wsat_mono; last done.
  by apply map_subseteq_difference_l.
Qed.

Lemma wsat_lookup W σ i P :
  wsat W σ → W !! i = Some P →
  ∃ σ0, σ0 ⊆ σ ∧ P σ0.
Proof.
  induction W as [ | INV W IH] in i, σ |-*; first done.
  simpl. intros (σ0 & HINV & Hincl & Hsat).
  destruct i as [ | i]; simpl.
  - intros [= ->]. eauto.
  - intros Hlook. destruct (IH _ _ Hsat Hlook) as (σ1 & ? & ?).
    exists σ1; split; last done. etrans; eauto.
    by apply map_subseteq_difference_l.
Qed.

Lemma wext_lookup W' W i INV :
  W' ⊒ W → W !! i = Some INV → ∃ i', W' !! i' = Some INV.
Proof.
  unfold wext.
  intros Hincl Hlook.
  destruct Hincl as (W''& ->).
  exists (length W'' + i).
  rewrite lookup_app_r; last lia.
  by rewrite Nat.add_comm Nat.add_sub.
Qed.

Lemma wsat_merge σ1 σ2 W1 W2 :
  σ1 ##ₘ σ2 →
  wsat W1 σ1 →
  wsat W2 σ2 →
  wsat (W1 ++ W2) (σ1 ∪ σ2).
Proof.
  intros Hdisj. induction W1 as [ | INV W1 IH] in W2, σ1, σ2, Hdisj |-*.
  - simpl. intros _ Hs. eapply wsat_mono; last done. by apply map_union_subseteq_r.
  - simpl. intros (σ0 & Hinv & Hincl & Hsat1) Hsat2.
    exists σ0. split_and!; [ done | | ].
    + by apply map_union_subseteq_l'.
    + rewrite map_difference_union'; last done.
      assert ((σ2 ∖ σ0) = σ2) as H.
      { symmetry; apply map_disjoint_difference.
        symmetry. eapply map_disjoint_weaken_l; done.
      }
      rewrite H.
      apply IH; [ | done..].
      eapply map_disjoint_weaken_l; first done. by apply map_subseteq_difference_l.
Qed.

(** Assuming that we have found a heap invariant [P] talking about [l] and that is invariant wrt the concrete value, we can update [l].
 *)
Lemma wsat_update W σ i (l : loc) (v : val) (P : heap_inv) :
  wsat W σ → W !! i = Some P →
  (∀ σ : heap, P σ → is_Some (σ !! l) ∧ P (<[l := v]> σ)) →
  wsat W (<[l := v]> σ).
Proof.
  induction W as [ | INV W IH] in i, σ |-*; first done.
  destruct i as [ | i].
  - intros (σ0 & HINV & Hincl & Hsat).
    intros [= ->] Hupd. eexists. split_and!; [eapply Hupd, HINV | | ].
    + by apply insert_mono.
    + apply Hupd in HINV as [[v0 Hs] _]. eapply wsat_mono; last apply Hsat.
      rewrite (difference_insert _ _ _ _ _ v0). rewrite insert_id; done.
  - intros Hsat Hlook Hupd.
    destruct Hsat as (σ0 & HINV & Hincl & Hsat). simpl in *.
    specialize (wsat_lookup _ _ _ _ Hsat Hlook) as (σ1 & Hincl' & [Hs ?]%Hupd).
    specialize (IH _ _ Hsat Hlook Hupd).
    assert (σ0 !! l = None) as H0l.
    { eapply lookup_weaken_is_Some in Hincl'; last done.
      apply lookup_difference_is_Some in Hincl'. apply Hincl'.
    }
    exists σ0. split_and!; [  done | | ].
    + etrans; first by eapply (insert_subseteq _ l v).
      by apply insert_mono.
    + assert (<[l:=v]> σ ∖ σ0 = <[l:=v]> (σ ∖ σ0)) as ->; last done.
      symmetry. apply insert_difference'. done.
Qed.

(** ** Definition of the logrel *)

(** A semantic type consists of a value-predicate parameterized over a step-index and a world,
   a proof of closedness, and a proof of downwards-closure wrt step-indices,
   and a proof of upwards-closure wrt world extension.
  *)
Record sem_type := mk_ST {
  sem_type_car :> nat → world → val → Prop;
  sem_type_closed_val k W v : sem_type_car k W v → is_closed [] (of_val v);
  sem_type_mono : ∀ k k' W v, sem_type_car k W v → k' ≤ k → sem_type_car k' W v;
  sem_type_mono_world : ∀ k W W' v, sem_type_car k W v → W' ⊒ W → sem_type_car k W' v
  }.

(** Two tactics we will use later on.
  [pose_sem_type P as N] defines a semantic type at name [N] with the value predicate [P].
 *)
(* slightly complicated formulation to make the proof term [p] opaque and prevent it from polluting the context *)
Tactic Notation "pose_sem_type" uconstr(P) "as" ident(N) :=
  let p := fresh "__p" in
  let p2 := fresh "__p2" in
  let p3 := fresh "__p3" in
  unshelve refine ((λ p p2 p3, let N := (mk_ST P p p2 p3) in _) _ _ _); first (simpl in p, p2, p3); cycle 1.
Tactic Notation "specialize_sem_type" constr(S) "with" uconstr(P) "as" ident(N) :=
  pose_sem_type P as N; last specialize (S N).

(** We represent type variable assignments [δ] as functions [f] into semantic types.
  The variable [#n] (in De Bruijn representation) is mapped to [f n].
 *)
Definition tyvar_interp := var → sem_type.
Implicit Types
  (δ : tyvar_interp)
  (τ : sem_type)
.

(**
  In Coq, we need to make argument why the logical relation is well-defined precise:
  (for Coq, that means: we need to show that the recursion is terminating).

  To make this formal, we define a well-founded relation that allows to either decrease the step-index, the type, or switch from the expression case to the value case for recursive calls.
  We define size measures for for all three of these things, and then combine them into a big lexicographic ordering [term_rel].

  Adding in state does not provide much of a complication, _as long as we only consider first-order state_.
  (higher-order state makes the argument quite a bit more difficult, since worlds then also need to be step-indexed).
 *)
Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size Bool := 1;
  type_size Unit := 1;
  type_size (A → B) := type_size A + type_size B + 1;
  type_size (#α) := 1;
  type_size (∀: A) := type_size A + 2;
  type_size (∃: A) := type_size A + 2;
  type_size (A × B) := type_size A + type_size B + 1;
  type_size (A + B) := max (type_size A) (type_size B) + 1;
  type_size (μ: A) := type_size A + 2;
  type_size (Ref A) := 2
.
(* [ltof A R] defines a well-founded measure on type [A] by using a mapping [R] from [A] to [nat]
  (it lifts the < relation on natural numbers to [A]) *)
Definition type_lt := ltof type type_size.
#[local] Instance type_lt_wf : WellFounded type_lt.
Proof. apply well_founded_ltof. Qed.

Inductive type_case : Set :=
  | expr_case | val_case.
Definition type_case_size (c : type_case) : nat :=
  match c with | expr_case => 1 | val_case => 0 end.
Definition type_case_lt := ltof type_case type_case_size.
#[local] Instance type_case_lt_wf : WellFounded type_case_lt.
Proof. apply well_founded_ltof. Qed.

Definition term_rel := Subterm.lexprod nat (type * type_case) lt (Subterm.lexprod type type_case type_lt type_case_lt).
#[local] Instance term_rel_wf : WellFounded term_rel. apply _. Qed.

(** *** The logical relation *)
(** Since the relation is step-indexed now, and the argument that the case for recursive types is well-formed
  fundamentally requires decreasing the step-index, we also need to convince Equations that this definition is well-formed!
   We do this by providing a well-founded termination relation [term_rel] that decreases for each recursive call.
 *)
Equations type_interp (c : type_case) (t : type) δ (k : nat) (W : world) (v : match c with val_case => val | expr_case => expr end) : Prop
  by wf (k, (t, c)) term_rel := {

  type_interp val_case Int δ k W v =>
    ∃ z : Z, v = #z ;
  type_interp val_case Bool δ k W v =>
    ∃ b : bool, v = #b ;
  type_interp val_case Unit δ k W v =>
    v = #LitUnit ;
  type_interp val_case (A × B) δ k W v =>
    ∃ v1 v2 : val, v = (v1, v2)%V ∧ type_interp val_case A δ k W v1 ∧ type_interp val_case B δ k W v2;
  type_interp val_case (A + B) δ k W v =>
    (∃ v' : val, v = InjLV v' ∧ type_interp val_case A δ k W v') ∨
    (∃ v' : val, v = InjRV v' ∧ type_interp val_case B δ k W v');

  type_interp val_case (A → B) δ k W v =>
    ∃ x e, v = LamV x e ∧ is_closed (x :b: nil) e ∧
      (* Slightly weird formulation: for down-closure, we want to quantify over all k' ≤ k --
        but with that formulation, the termination checker will not be able to see that k' will really be smaller!
         Thus, we quantify over the difference kd and subtract *)
      ∀ v' kd W', W' ⊒ W →
        type_interp val_case A δ (k - kd) W' v' →
        type_interp expr_case B δ (k - kd) W' (subst' x (of_val v') e);
  type_interp val_case (#α) δ k W v =>
    (δ α).(sem_type_car) k W v;
  type_interp val_case (∀: A) δ k W v =>
    ∃ e, v = TLamV e ∧ is_closed [] e ∧
      ∀ τ, type_interp expr_case A (τ .: δ) k W e;
  type_interp val_case (∃: A) δ k W v =>
    ∃ v', v = PackV v' ∧
      ∃ τ : sem_type, type_interp val_case A (τ .: δ) k W v';
  (** Defined with two cases: ordinarily, we might require [k > 0] in the body as a guard for the recursive call,
     but this does not count as a proper guard for termination for Coq -- therefore we handle the 0-case separately.
   *)
  type_interp val_case (μ: A) δ (S k) W v =>
    ∃ v', v = (roll v')%V ∧ is_closed [] v' ∧ ∀ kd, type_interp val_case (A.[μ: A/]%ty) δ (k - kd) W v';
  type_interp val_case (μ: A) δ 0 W v =>
    ∃ v', v = (roll v')%V ∧ is_closed [] v';
  (** The reference case *)
  type_interp val_case (Ref a) δ k W v =>
      ∃ (l : loc), v = LitV $ LitLoc l ∧ ∃ i INV, W !! i = Some INV ∧
      INV = (λ σ', ∃ v, σ' = <[ l := v ]> ∅ ∧ TY 0; ∅ ⊢ (of_val v) : a);

  type_interp expr_case t δ k W e =>
    ∀ e' h h' W' n, W' ⊒ W → wsat W' h → n < k → red_nsteps n e h e' h' → ∃ v W'', to_val e' = Some v ∧
      W'' ⊒ W' ∧ wsat W'' h' ∧ type_interp val_case t δ (k - n) W'' v
}.

(** Proving that the arguments are decreasing for recursive calls is a bit more messy now, but it's mostly systematic.
  Therefore we provide a simple automation tactic that will also become useful a few times below.
*)
Ltac dsimpl :=
  repeat match goal with
  | |- term_rel (?k, _) (?k, _) =>
      (* step-index is not decreasing, go right *)
      right
  | |- term_rel (?k1, _) (?k2, _) =>
      (* use [lia] to decide where to go *)
      destruct (decide (k1 < k2)) as [ ? | ?]; [left; lia | assert (k1 = k2) as -> by lia; right]
  | |- Subterm.lexprod type type_case _ _ (?t, _) (?t, _) =>
      (* type is not decreasing, go right *)
      right
  | |- Subterm.lexprod type type_case _ _ (_, ?a) (_, ?a) =>
      (* type case is not decreasing, go left *)
      left
  | |- term_rel (_, _) (_, _) =>
      (* branch non-deterministically and try to solve the remaining goal *)
      first [left; solve [dsimpl] | right; solve [dsimpl]]
  | |- Subterm.lexprod type type_case  _ _ _ _ =>
      (* branch non-deterministically *)
      first [left; solve [dsimpl] | right; solve [dsimpl]]
  | _ =>
      (* try to solve a leaf, i.e. a [type_lt], [type_case_lt] or [lt] goal *)
      unfold type_case_lt, type_lt, ltof; simp type_size; simpl; try lia
  end.
(** The tactic solves all of Equations' obligations for showing that the argument decreases. *)
Solve Obligations with (intros; dsimpl).

(** *** Value relation and expression relation *)
Definition sem_val_rel A δ k W v := type_interp val_case A δ k W v.
Definition sem_expr_rel A δ k W e := type_interp expr_case A δ k W e.

Notation 𝒱 := (type_interp val_case).
Notation ℰ := (type_interp expr_case).

Lemma val_rel_is_closed v δ k W A:
  𝒱 A δ k W v → is_closed [] (of_val v).
Proof.
  induction A as [ | | | | | A IHA | | A IH1 B IH2 | A IH1 B IH2 | A IHA | A] in k, v, δ |-*; simp type_interp.
  - by eapply sem_type_closed_val.
  - intros [z ->]. done.
  - intros [b ->]. done.
  - intros ->. done.
  - intros (e & -> & ? & _). done.
  - intros (v' & -> & (τ & Hinterp)). simpl. by eapply IHA.
  - intros (x & e & -> & ? & _). done.
  - intros (v1 & v2 & -> & ? & ?). simpl; apply andb_True; split; eauto.
  - intros [(v' & -> & ?) | (v' & -> & ?)]; simpl; eauto.
  - destruct k; simp type_interp.
    + intros (v' & -> & ?); done.
    + intros (v' & -> & ? & Ha); done.
  - intros (l & -> & _). done.
Qed.

(** Downwards closure wrt step-index *)
Lemma type_interp_mono : ∀ '(k, (A, c)) δ W k' x, k' ≤ k → type_interp c A δ k W x → type_interp c A δ k' W x.
Proof.
  eapply (well_founded_ind (R := term_rel) term_rel_wf).
  intros (k & A & []) IH δ W k'.
  { (* expression rel *)
    intros e Hk He. simp type_interp in He. simp type_interp. intros e' h h' W' n Hincl Hsat Hn Hred.
    destruct (He e' h h' W' n ltac:(done) ltac:(done) ltac:(lia) Hred) as (v & W'' & Hval & Hincl' & Hsat' & Hv).
    exists v, W''. split; first done.
    split_and!; [done.. | ].
    eapply (IH (k-n, (A, val_case))); [ | lia | done].
    (* show that the induction is decreasing *)
    dsimpl.
  }
  intros v Hk Hv.
  destruct A as [x | | | | A | A | A B | A B | A B | A | A ]; simp type_interp; simp type_interp in Hv.
  - (* var case *)
    by eapply sem_type_mono.
  - (* universal case *)
    destruct Hv as (e & -> & ? & Hv).
    exists e. split_and!; [done.. | ]. intros τ.
    eapply (IH (k, (A, expr_case))); [ dsimpl | done | done].
  - (* existential case *)
    destruct Hv as (v' & -> & (τ & Hv)). exists v'. split; first done.
    exists τ. eapply (IH (k, (A, _))); [ dsimpl | done..].
  - (* fun case *)
    destruct Hv as (x & e & -> & ? & Hv). exists x, e. split_and!; [done..| ].
    intros v' kd W' Hv' Hincl.
    (* slightly tricky due to the contravariant recursive occurrence *)
    set (kd' := k - k').
    specialize (Hv v' (kd + kd')).
    replace (k - (kd + kd')) with (k' - kd) in Hv by lia.
    eapply (IH (k' - kd, (B, expr_case))); [ | lia | by eapply Hv].
    destruct (decide (k' - kd < k)) as [ ? | ?]; first (left; lia).
    assert (k' - kd = k) as -> by lia. dsimpl.
  - (* pair case *)
    destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
    exists v1, v2. split_and!; first done.
    all: eapply (IH (k, (_, _))); [ dsimpl | done..].
  - (* sum case *)
    destruct Hv as [(v' & -> & Hv) | (v' & -> & Hv)]; [ left | right].
    all: exists v'; split; first done.
    all: eapply (IH (k, (_, _))); [ dsimpl | done..].
  - (* rec case *)
    destruct k; simp type_interp in Hv.
    { assert (k' = 0) as -> by lia. simp type_interp. }
    destruct Hv as (v' & -> & ? & Hv).
    destruct k' as [ | k']; simp type_interp.
    { eauto. }
    exists v'. split_and!; [ done.. | ].
    intros kd.
    (* here we crucially use that we can decrease the index *)
    eapply (IH (k - kd, (A.[(μ: A)%ty/], val_case))); [ | lia | done].
    left. lia.
Qed.

(** We can now derive the two desired lemmas *)
Lemma val_rel_mono_idx A δ k k' W v : k' ≤ k → 𝒱 A δ k W v → 𝒱 A δ k' W v.
Proof. apply (type_interp_mono (k, (A, val_case))). Qed.
Lemma expr_rel_mono_idx A δ k k' W e : k' ≤ k → ℰ A δ k W e → ℰ A δ k' W e.
Proof. apply (type_interp_mono (k, (A, expr_case))). Qed.

(** Up-closure wrt worlds *)
Lemma type_interp_mono_world : ∀ '(k, (A, c)) δ W W' x, W' ⊒ W → type_interp c A δ k W x → type_interp c A δ k W' x.
Proof.
  eapply (well_founded_ind (R := term_rel) term_rel_wf).
  intros (k & A & []) IH δ W W'.
  { (* expression rel *)
    intros e HW He. simp type_interp in He. simp type_interp. intros e' h h' W'' n Hincl Hsat Hn Hred.
    destruct (He e' h h' W'' n ltac:(etrans; done) ltac:(done) ltac:(lia) Hred) as (v & W''' & Hval & Hincl' & Hsat' & Hv).
    exists v, W'''. split; first done.
    split_and!; [done.. | ].
    eapply (IH (k-n, (A, val_case))); [ |  | apply Hv].
    - dsimpl.
    - done.
  }
  intros v HW Hv.
  destruct A as [x | | | | A | A | A B | A B | A B | A | A ]; simp type_interp; simp type_interp in Hv.
  - (* var case *)
    by eapply sem_type_mono_world.
  - (* universal case *)
    destruct Hv as (e & -> & ? & Hv).
    exists e. split_and!; [done.. | ]. intros τ.
    eapply (IH (k, (A, expr_case))); [ dsimpl | done | done].
  - (* existential case *)
    destruct Hv as (v' & -> & (τ & Hv)). exists v'. split; first done.
    exists τ. eapply (IH (k, (A, _))); [ dsimpl | done..].
  - (* fun case *)
    destruct Hv as (x & e & -> & ? & Hv). exists x, e. split_and!; [done..| ].
    intros v' kd W'' Hincl Hv'.
    specialize (Hv v' kd W'').
    eapply (IH (k - kd, (B, expr_case))); [ dsimpl | | eapply Hv].
    + done.
    + etrans; done.
    + eapply (IH (k -kd, (A, val_case))); last done; last done. dsimpl.
  - (* pair case *)
    destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
    exists v1, v2. split_and!; first done.
    all: eapply (IH (k, (_, _))); [ dsimpl | done..].
  - (* sum case *)
    destruct Hv as [(v' & -> & Hv) | (v' & -> & Hv)]; [ left | right].
    all: exists v'; split; first done.
    all: eapply (IH (k, (_, _))); [ dsimpl | done..].
  - (* rec case *)
    destruct k; simp type_interp in Hv.
    { simp type_interp. }
    destruct Hv as (v' & -> & ? & Hv).
    simp type_interp.
    exists v'. split_and!; [ done.. | ].
    intros kd.
    (* here we crucially use that we can decrease the index *)
    eapply (IH (k - kd, (A.[(μ: A)%ty/], val_case))); [ | done | done].
    left. lia.
  - (* loc case *)
    destruct Hv as (l & -> & (i & INV & Hlook & Heq)).
    exists l. split; first done.
    destruct (wext_lookup _ _ _ _ HW Hlook) as (i' & Hlook').
    exists i', INV. done.
Qed.

Lemma val_rel_mono_world A δ k W W' v : W' ⊒ W → 𝒱 A δ k W v → 𝒱 A δ k W' v.
Proof. apply (type_interp_mono_world (k, (A, val_case))). Qed.
Lemma expr_rel_mono_world A δ k W W' e : W' ⊒ W → ℰ A δ k W e → ℰ A δ k W' e.
Proof. apply (type_interp_mono_world (k, (A, expr_case))). Qed.

Lemma val_rel_mono A δ k k' W W' v : k' ≤ k → W' ⊒ W → 𝒱 A δ k W v → 𝒱 A δ k' W' v.
Proof.
  intros. eapply val_rel_mono_idx; last eapply val_rel_mono_world; done.
Qed.
Lemma expr_rel_mono A δ k k' W W' e : k' ≤ k → W' ⊒ W → ℰ A δ k W e → ℰ A δ k' W' e.
Proof.
  intros. eapply expr_rel_mono_idx; last eapply expr_rel_mono_world; done.
Qed.

(** This is the Value Inclusion lemma from the lecture notes *)
Lemma sem_val_expr_rel A δ k W v :
  𝒱 A δ k W v → ℰ A δ k W (of_val v).
Proof.
  simp type_interp. intros Hv e' h h' W' n Hincl HW Hn (-> & -> & ->)%nsteps_val_inv.
  rewrite to_of_val. eexists _, W'; split; first done.
  replace (k - 0) with k by lia.
  split_and!; [done | done | ].
  by eapply val_rel_mono_world.
Qed.

Lemma sem_expr_rel_zero_trivial A δ W e :
  ℰ A δ 0 W e.
Proof.
  simp type_interp. intros ???. lia.
Qed.

(** Interpret a syntactic type *)
Program Definition interp_type A δ : sem_type := {|
  sem_type_car := 𝒱 A δ;
|}.
Next Obligation. by eapply val_rel_is_closed. Qed.
Next Obligation. by eapply val_rel_mono. Qed.
Next Obligation. by eapply val_rel_mono_world. Qed.

(** Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

(** Context relation *)
Inductive sem_context_rel (δ : tyvar_interp) (k : nat) (W : world) : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel δ k W ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A δ k W v →
    sem_context_rel δ k W Γ θ →
    sem_context_rel δ k W (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.

Lemma sem_context_rel_vals {δ k W Γ θ x A} :
  sem_context_rel δ k W Γ θ →
  Γ !! x = Some A →
  ∃ e v, θ !! x = Some e ∧ to_val e = Some v ∧ 𝒱 A δ k W v.
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

Lemma sem_context_rel_subset δ k W Γ θ :
  𝒢 δ k W Γ θ → dom Γ ⊆ dom θ.
Proof.
  intros Hctx. apply elem_of_subseteq. intros x (A & Hlook)%elem_of_dom.
  eapply sem_context_rel_vals in Hlook as (e & v & Hlook & Heq & Hval); last done.
  eapply elem_of_dom; eauto.
Qed.

Lemma sem_context_rel_dom_eq δ k W Γ θ :
  𝒢 δ k W Γ θ → dom Γ = dom θ.
Proof.
  induction 1 as [ | ??????? IH].
  - rewrite !dom_empty //.
  - rewrite !dom_insert IH //.
Qed.

Lemma sem_context_rel_closed δ k W Γ θ:
  𝒢 δ k W Γ θ → subst_is_closed [] θ.
Proof.
  induction 1 as [ | Γ θ v x A Hv Hctx IH]; rewrite /subst_is_closed.
  - naive_solver.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_is_closed.
    + eapply IH; last done.
Qed.

Lemma sem_context_rel_mono_idx Γ δ k k' W θ :
  k' ≤ k → 𝒢 δ k W Γ θ → 𝒢 δ k' W Γ θ.
Proof.
  intros Hk. induction 1 as [|Γ θ v y B Hvals Hctx IH]; constructor.
  - eapply val_rel_mono_idx; done.
  - apply IH.
Qed.
Lemma sem_context_rel_mono_world Γ δ k W W' θ :
  W' ⊒ W → 𝒢 δ k W Γ θ → 𝒢 δ k W' Γ θ.
Proof.
  intros HW. induction 1 as [|Γ θ v y B Hvals Hctx IH]; constructor.
  - eapply val_rel_mono_world; done.
  - apply IH.
Qed.
Lemma sem_context_rel_mono Γ δ k k' W W' θ :
  k' ≤ k → W' ⊒ W → 𝒢 δ k W Γ θ → 𝒢 δ k' W' Γ θ.
Proof.
  intros. eapply sem_context_rel_mono_idx; last eapply sem_context_rel_mono_world; done.
Qed.

(** *** Semantic typing judgment *)
Definition sem_typed (Δ : nat) Γ e A :=
  ∀ θ δ k W, 𝒢 δ k W Γ θ → ℰ A δ k W (subst_map θ e).
Notation "'TY' Δ ;  Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).

Section boring_lemmas.
  (** The lemmas in this section are all quite boring and expected statements,
    but are quite technical to prove due to De Bruijn binders.
    We encourage to skip over the proofs of these lemmas.
  *)

  Lemma type_interp_ext  :
    ∀ '(k, (B, c)), ∀ δ δ' W x,
    (∀ n k v W', W' ⊒ W → δ n k W' v ↔ δ' n k W' v) →
    type_interp c B δ k W x ↔ type_interp c B δ' k W x.
  Proof.
    eapply (well_founded_ind (R := term_rel) term_rel_wf).
    intros (k & A & []) IH δ δ'.
    { (* expression rel *)
      intros W e Hd. simp type_interp. eapply forall_proper; intros e'.
      eapply forall_proper; intros h. eapply forall_proper; intros h'.
      eapply forall_proper; intros W'. eapply forall_proper; intros n.
      eapply if_iff'; intros. eapply if_iff'; intros _. eapply if_iff'; intros _.
      eapply if_iff; first done. f_equiv. intros v. f_equiv. intros W''.
      f_equiv. apply and_iff'; intros. f_equiv.
      eapply (IH ((k - n), (A, val_case))); first dsimpl.
      intros; apply Hd. etrans; last etrans; done.
    }
    intros W v Hd. destruct A as [x | | | | A | A | A B | A B | A B | A | A ]; simp type_interp; eauto.
    - apply Hd. done.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      eapply (IH (_, (_, _))); first dsimpl.
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      eapply (IH (_, (_, _))); first dsimpl.
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply forall_proper. intros W'.
      eapply if_iff'; intros.
      eapply if_iff; (eapply (IH (_, (_, _))); first dsimpl).
      all: intros; eapply Hd; etrans; done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; f_equiv; intros ?; f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - destruct k; simp type_interp.
      + done.
      + f_equiv; intros ?. f_equiv. f_equiv.
        eapply forall_proper; intros ?.
        by eapply (IH (_, (_, _))); first dsimpl.
  Qed.

  Lemma type_interp_move_ren :
    ∀ '(k, (B, c)), ∀ δ W σ x, type_interp c B (λ n, δ (σ n)) k W x ↔ type_interp c (rename σ B) δ k W x.
  Proof.
    eapply (well_founded_ind (R := term_rel) term_rel_wf).
    intros (k & A & []) IH δ W σ.
    { (* expression rel *)
      intros e. simp type_interp. eapply forall_proper; intros e'.
      eapply forall_proper; intros h. eapply forall_proper; intros h'.
      eapply forall_proper; intros W'. eapply forall_proper; intros n.

      eapply if_iff; first done. eapply if_iff; first done.
      eapply if_iff; first done. eapply if_iff; first done.
      f_equiv. intros v. f_equiv. intros W''. f_equiv. f_equiv. f_equiv.
      eapply (IH (_, (_, _))).
      (* show that the induction is decreasing *)
      dsimpl.
    }
    intros v. destruct A as [x | | | | A | A | A B | A B | A B | A | A ]; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros ?.
      eapply forall_proper. intros ?. eapply forall_proper. intros ?.
      eapply if_iff; first done. eapply if_iff; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; f_equiv; intros ?; f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - destruct k; simp type_interp.
      + done.
      + f_equiv; intros ?. f_equiv. f_equiv.
        eapply forall_proper; intros ?.
        etransitivity; first eapply (IH (_, (_, _))); first dsimpl.
        asimpl. done.
  Qed.

  Lemma type_interp_move_subst  :
    ∀ '(k, (B, c)), ∀ δ W σ x, type_interp c B (λ n, interp_type (σ n) δ) k W x ↔ type_interp c (B.[σ]) δ k W x.
  Proof.
    eapply (well_founded_ind (R := term_rel) term_rel_wf).
    intros (k & A & []) IH δ W σ.
    { (* expression rel *)
      intros e. simp type_interp. eapply forall_proper; intros e'.
      eapply forall_proper; intros h. eapply forall_proper; intros h'.
      eapply forall_proper; intros W'. eapply forall_proper; intros n.

      eapply if_iff; first done. eapply if_iff; first done.
      eapply if_iff; first done. eapply if_iff; first done.
      f_equiv. intros v. f_equiv. intros W''. f_equiv. f_equiv. f_equiv.
      eapply (IH (_, (_, _))).
      (* show that the induction is decreasing *)
      dsimpl.
    }
    intros v. destruct A as [x | | | | A | A | A B | A B | A B | A | A]; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ??? ?; simpl.
      + asimpl. simp type_interp. done.
      + unfold up; simpl. etransitivity;
          last eapply (type_interp_move_ren (_, (_, _))).
        done.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ? ???; simpl.
      + asimpl. simp type_interp. done.
      + unfold up; simpl. etransitivity;
          last eapply (type_interp_move_ren (_, (_, _))).
        done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros ?.
      eapply forall_proper. intros ?. eapply forall_proper. intros W'.
      eapply if_iff; first done.
      eapply if_iff; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; f_equiv; intros ?; f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - destruct k; simp type_interp.
      + done.
      + f_equiv; intros ?. f_equiv. f_equiv.
        eapply forall_proper; intros ?.
        etransitivity; first eapply (IH (_, (_, _))); first dsimpl.
        asimpl. done.
  Qed.


  Lemma sem_val_rel_move_single_subst A B δ k v W :
    𝒱 B (interp_type A δ .: δ) k W v ↔ 𝒱 (B.[A/]) δ k W v.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w W' ?; simpl; simp type_interp; done.
  Qed.

  Lemma sem_expr_rel_move_single_subst A B δ k W e :
    ℰ B (interp_type A δ .: δ) k W e ↔ ℰ (B.[A/]) δ k W e.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w W' ?; simpl; simp type_interp; done.
  Qed.

  Lemma sem_val_rel_cons A δ k v W τ :
    𝒱 A δ k W v ↔ 𝒱 A.[ren (+1)] (τ .: δ) k W v.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w W' ?; simpl; simp type_interp; done.
  Qed.

  Lemma sem_expr_rel_cons A δ k e W τ :
    ℰ A δ k W e ↔ ℰ A.[ren (+1)] (τ .: δ) k W e.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w W' ?; simpl; simp type_interp; done.
  Qed.

  Lemma sem_context_rel_cons Γ k δ θ τ W :
    𝒢 δ k W Γ θ →
    𝒢 (τ .: δ) k W (⤉ Γ) θ.
  Proof.
    induction 1 as [ | Γ θ v x A Hv Hctx IH]; simpl.
    - rewrite fmap_empty. constructor.
    - rewrite fmap_insert. constructor; last done.
      rewrite -sem_val_rel_cons. done.
  Qed.
End boring_lemmas.

(** Bind lemma *)
Lemma bind K e k W δ A B :
  ℰ A δ k W e →
  (∀ j v W', j ≤ k → W' ⊒ W → 𝒱 A δ j W' v → ℰ B δ j W' (fill K (of_val v))) →
  ℰ B δ k W (fill K e).
Proof.
  intros H1 H2. simp type_interp in H1. simp type_interp.
  intros e' h h' W' n HW Hsat Hn (j & e'' & h'' & Hj & Hred1 & Hred2)%red_nsteps_fill.
  specialize (H1 e'' h h'' W' j ltac:(done) ltac:(done) ltac:(lia) Hred1) as (v & W'' & Hev & Hincl' & Hsat' & Hv).
  specialize (H2 (k-j) v W'' ltac:(lia) ltac:(etrans; done) Hv).
  simp type_interp in H2.
  rewrite (of_to_val _ _ Hev) in H2.
  eapply H2 in Hred2; cycle 1; [ reflexivity | done | lia | ].
  assert (k - n = k - j - (n - j)) as -> by lia.
  destruct Hred2 as (v' & W''' & ? & ? & ? & Hred2).
  exists v', W'''. split_and!; [done | | done | done].
  etrans; done.
Qed.

(** This is the closure-under-expansion lemma from the lecture notes *)
Lemma expr_det_step_closure e e' A δ k W :
  det_step e e' →
  ℰ A δ (k - 1) W e' →
  ℰ A δ k W e.
Proof.
  simp type_interp. intros Hdet Hexpr e'' h h' W' n Hincl Hsat Hn [? Hred]%(det_step_red _ e'); last done.
  destruct (Hexpr e'' h h' W' (n -1) Hincl Hsat ) as (v & W'' & Hev & Hincl' & Hsat' & Hv); [lia | done | ].
  exists v, W''. split; first done. split; first done.
  replace (k - n) with (k - 1 - (n - 1)) by lia. done.
Qed.

Lemma expr_det_steps_closure e e' A δ k W n :
  nsteps det_step n e e' → ℰ A δ (k - n) W e' → ℰ A δ k W e.
Proof.
  induction 1 as [ | n e1 e2 e3 Hstep Hsteps IH] in k |-* .
  - replace (k - 0) with k by lia. done.
  - intros He.
    eapply expr_det_step_closure; first done.
    apply IH. replace (k - 1 - n) with (k - (S n)) by lia. done.
Qed.

(** ** Compatibility lemmas *)

Lemma compat_int Δ Γ z : TY Δ; Γ ⊨ (Lit $ LitInt z) : Int.
Proof.
  intros θ δ k W _.
  eapply (sem_val_expr_rel _ _ _ _ #z).
  simp type_interp. eauto.
Qed.

Lemma compat_bool Δ Γ b : TY Δ; Γ ⊨ (Lit $ LitBool b) : Bool.
Proof.
  intros θ δ k W _.
  eapply (sem_val_expr_rel _ _ _ _ #b). simp type_interp. eauto.
Qed.

Lemma compat_unit Δ Γ : TY Δ; Γ ⊨ (Lit $ LitUnit) : Unit.
Proof.
  intros θ δ k W _.
  eapply (sem_val_expr_rel _ _ _ _ #LitUnit).
  simp type_interp. eauto.
Qed.

Lemma compat_var Δ Γ x A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ (Var x) : A.
Proof.
  intros Hx θ δ k W Hctx; simpl.
  specialize (sem_context_rel_vals Hctx Hx) as (e & v & He & Heq & Hv).
  rewrite He. simp type_interp.
  rewrite -(of_to_val _ _ Heq).
  intros e' h h' W' n Hincl Hsat Hn (-> & -> & ->)%nsteps_val_inv.
  rewrite to_of_val. eexists _, _.
  split_and!; [done.. | ].
  replace (k -0) with k by lia.
  eapply val_rel_mono_world; done.
Qed.

Lemma compat_app Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : (A → B) →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (e1 e2) : B.
Proof.
  intros Hfun Harg θ δ k W Hctx; simpl.
  specialize (Hfun _ _ _ _ Hctx).
  specialize (Harg _ _ _ _ Hctx).

  eapply (bind [AppRCtx _]); first done.
  intros j v W' Hj HW Hv. simpl.

  eapply (bind [AppLCtx _ ]).
  { eapply expr_rel_mono; cycle -1; [done | lia | done]. }
  intros j' f W'' Hj' HW' Hf.

  simp type_interp in Hf. destruct Hf as (x & e & -> & Hcl & Hf).
  specialize (Hf v 0).
  replace (j' - 0) with j' in Hf by lia.
  eapply expr_det_step_closure.
  { eapply det_step_beta. apply is_val_of_val. }
  eapply expr_rel_mono_idx; last apply Hf; [lia | reflexivity | ].
  eapply val_rel_mono; last done; [lia | done].
Qed.

Lemma is_closed_subst_map_delete X Γ (x: string) θ A e:
  closed X e →
  subst_is_closed [] θ →
  dom Γ ⊆ dom θ →
  (∀ y : string, y ∈ X → y ∈ dom (<[x:=A]> Γ)) →
  is_closed (x :b: []) (subst_map (delete x θ) e).
Proof.
  intros He Hθ Hdom1 Hdom2.
  eapply closed_subst_weaken; [ | | apply He].
  - eapply subst_is_closed_subseteq; last done.
    apply map_delete_subseteq.
  - intros y Hy%Hdom2 Hn. apply elem_of_list_singleton.
    apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
    destruct (decide (x = y)) as [<- | Hneq]; first done.
    rewrite lookup_delete_ne in Hn; last done.
    rewrite lookup_insert_ne in Hy; last done.
    move: Hdom1. rewrite elem_of_subseteq.
    move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
    naive_solver.
Qed.

(** Lambdas need to be closed by the context *)
Lemma compat_lam_named Δ Γ x e A B X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom (<[x := A]> Γ)) →
  TY Δ; (<[ x := A ]> Γ) ⊨ e : B →
  TY Δ; Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ δ k W Hctxt. simpl.
  eapply (sem_val_expr_rel _ _ _ _ (LamV x _)).
  simp type_interp.
  eexists (BNamed x), _. split_and!; [done| | ].
  { eapply is_closed_subst_map_delete; eauto.
    + eapply sem_context_rel_closed in Hctxt. naive_solver.
    + eapply sem_context_rel_subset in Hctxt; naive_solver.
  }

  intros v' kd W' Hv' Hincl.
  specialize (Hbody (<[ x := of_val v']> θ) δ (k - kd) W').
  simpl. rewrite subst_subst_map.
  2: { by eapply sem_context_rel_closed. }
  apply Hbody.
  apply sem_context_rel_insert; first done.
  eapply sem_context_rel_mono; [| done| done]. lia.
Qed.

Lemma is_closed_subst_map_anon X Γ θ e:
  closed X e →
  subst_is_closed [] θ →
  dom Γ ⊆ dom θ →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  is_closed [] (subst_map θ e).
Proof.
  intros He Hθ Hdom1 Hdom2.
  eapply closed_subst_weaken; [ | | apply He].
  - eapply subst_is_closed_subseteq; done.
  - intros y Hy%Hdom2 Hn.
    apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
    move: Hdom1. rewrite elem_of_subseteq.
    move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
    naive_solver.
Qed.

Lemma compat_lam_anon Δ Γ e A B X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  intros Hcl Hsub Hbody θ δ k W Hctxt. simpl.
  eapply (sem_val_expr_rel _ _ _ _ (LamV BAnon _)).
  simp type_interp.
  eexists BAnon, _. split_and!; [done| | ].
  { eapply is_closed_subst_map_anon; eauto.
    + eapply sem_context_rel_closed in Hctxt. naive_solver.
    + eapply sem_context_rel_subset in Hctxt; naive_solver.
  }

  intros v' kd W' Hv' Hincl.
  apply (Hbody θ δ (k - kd) W').
  eapply sem_context_rel_mono; [ | done..]. lia.
Qed.

Lemma compat_int_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Int →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Int.
Proof.
  intros Hop He1 He2 θ δ k W Hctx. simpl.
  specialize (He1 _ _ _ _ Hctx).
  specialize (He2 _ _ _ _ Hctx).

  eapply (bind [BinOpRCtx _ _]); first done.
  intros j v2 W' Hj HW Hv2. simpl.

  eapply (bind [BinOpLCtx _ _ ]).
  { eapply expr_rel_mono; last done; [lia | done]. }
  intros j' v1 W'' Hj' HW' Hv1.

  simp type_interp. intros e' h h' W''' n Hincl' Hsat' Hn Hred.
  simp type_interp in Hv1. simp type_interp in Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst; simpl.
  all: eapply det_step_red in Hred as [ ? Hred]; [ |  eapply det_step_binop; done].
  all: apply nsteps_val_inv in Hred as (? & -> & ->).
  all: eexists _, W'''; simpl; split_and!; [done.. | ].
  all: simp type_interp; eauto.
Qed.

Lemma compat_int_bool_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Bool →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Bool.
Proof.
  intros Hop He1 He2 θ δ k W Hctx. simpl.
  specialize (He1 _ _ _ _ Hctx).
  specialize (He2 _ _ _ _ Hctx).

  eapply (bind [BinOpRCtx _ _]); first done.
  intros j v2 W' Hj HW Hv2. simpl.

  eapply (bind [BinOpLCtx _ _ ]).
  { eapply expr_rel_mono; last done; [lia | done]. }
  intros j' v1 W'' Hj' HW' Hv1.

  simp type_interp. intros e' h h' W''' n Hincl' Hsat' Hn Hred.
  simp type_interp in Hv1. simp type_interp in Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst; simpl.
  all: eapply det_step_red in Hred as [ ? Hred]; [ |  eapply det_step_binop; done].
  all: apply nsteps_val_inv in Hred as (? & -> & ->).
  all: eexists _, _; simpl; split_and!; [done.. | ].
  all: simp type_interp; eauto.
Qed.

Lemma compat_unop Δ Γ op A B e :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ (UnOp op e) : B.
Proof.
  intros Hop He θ δ k W Hctx. simpl.
  specialize (He _ _ _ _ Hctx).

  eapply (bind [UnOpCtx _]); first done.
  intros j v W' Hj HW' Hv. simpl.

  simp type_interp. intros e' h h' W'' n HWincl' Hsat' Hn Hred.
  inversion Hop; subst.
  all: simp type_interp in Hv; destruct Hv as (? & ->).
  all: eapply det_step_red in Hred as [ ? Hred]; [ |  eapply det_step_unop; done].
  all: apply nsteps_val_inv in Hred as (? & -> & ->).
  all: eexists _, _; simpl; split_and!; [done.. | ].
  all: simp type_interp; eauto.
Qed.

Lemma compat_tlam Δ Γ e A X :
  closed X e →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  TY S Δ; (⤉ Γ) ⊨ e : A →
  TY Δ; Γ ⊨ (Λ, e) : (∀: A).
Proof.
  intros Hcl Hsub He θ δ k W Hctx. simpl.
  simp type_interp.
  intros e' h h' W' n HW Hsat' Hn Hred. eapply nsteps_val_inv' in Hred as ( -> & -> & ->); last done.
  eexists _, _; split_and!; [done..| ].
  simp type_interp.
  eexists _. split_and!; [ done | | ].
  { eapply is_closed_subst_map_anon; eauto.
    + eapply sem_context_rel_closed in Hctx; naive_solver.
    + eapply sem_context_rel_subset in Hctx; naive_solver.
  }
  intros τ. eapply He.
  replace (k -0) with k by lia. eapply sem_context_rel_cons.
  eapply sem_context_rel_mono_world; done.
Qed.

Lemma compat_tapp Δ Γ e A B :
  type_wf Δ B →
  TY Δ; Γ ⊨ e : (∀: A) →
  TY Δ; Γ ⊨ (e <>) : (A.[B/]).
Proof.
  intros Hwf He θ δ k W Hctx. simpl.

  specialize (He _ _ _ _ Hctx).
  eapply (bind [TAppCtx]); first done.
  intros j v W' Hj HW Hv.
  simp type_interp in Hv.
  destruct Hv as (e' & -> & ? & He').

  set (τ := interp_type B δ).
  specialize (He' τ). simpl.
  eapply expr_det_step_closure.
  { apply det_step_tbeta. }
  eapply sem_expr_rel_move_single_subst.
  eapply expr_rel_mono_idx; last done.
  lia.
Qed.

Lemma compat_pack Γ e n A B :
  type_wf n B →
  type_wf (S n) A →
  TY n; Γ ⊨ e : A.[B/] →
  TY n; Γ ⊨ (pack e) : (∃: A).
Proof.
  intros Hwf Hwf' He θ δ k W Hctx. simpl.

  specialize (He _ _ _ _ Hctx).
  eapply (bind [PackCtx]); first done.
  intros j v W' Hj HW Hv.
  simpl. eapply (sem_val_expr_rel _ _ _ _ (PackV v)).
  simp type_interp. exists v; split; first done.
  exists (interp_type B δ).
  apply sem_val_rel_move_single_subst. done.
Qed.

Lemma compat_unpack n Γ A B e e' x :
  type_wf n B →
  TY n; Γ ⊨ e : (∃: A) →
  TY S n; <[x:=A]> (⤉Γ) ⊨ e' : B.[ren (+1)] →
  TY n; Γ ⊨ (unpack e as BNamed x in e') : B.
Proof.
  intros Hwf He He' θ δ k W Hctx. simpl.

  specialize (He _ _ _ _ Hctx).
  eapply (bind [UnpackCtx _ _]); first done.
  intros j v W' Hj HW Hv.
  simp type_interp in Hv. destruct Hv as (v' & -> & τ & Hv').
  simpl.

  eapply expr_det_step_closure.
  { apply det_step_unpack. apply is_val_of_val. }
  simpl. rewrite subst_subst_map; last by eapply sem_context_rel_closed.

  specialize (He' (<[x := of_val v']> θ) (τ.:δ) (j - 1) W').
  rewrite <-sem_expr_rel_cons in He'.
  apply He'.
  constructor.
  { eapply val_rel_mono_idx; last done. lia. }
  apply sem_context_rel_cons.
  eapply sem_context_rel_mono; last done; [lia | done].
Qed.

Lemma compat_if n Γ e0 e1 e2 A :
  TY n; Γ ⊨ e0 : Bool →
  TY n; Γ ⊨ e1 : A →
  TY n; Γ ⊨ e2 : A →
  TY n; Γ ⊨ (if: e0 then e1 else e2) : A.
Proof.
  intros He0 He1 He2 θ δ k W Hctx. simpl.
  specialize (He0 _ _ _ _ Hctx).
  specialize (He1 _ _ _ _ Hctx).
  specialize (He2 _ _ _ _ Hctx).

  eapply (bind [IfCtx _ _]); first done.
  intros j v W' Hj HW Hv.
  simp type_interp in Hv. destruct Hv as (b & ->).
  simpl.

  destruct b.
  - eapply expr_det_step_closure.
    { apply det_step_if_true. }
    eapply expr_rel_mono; last done; [lia | done].
  - eapply expr_det_step_closure.
    { apply det_step_if_false. }
    eapply expr_rel_mono; last done; [lia | done].
Qed.

Lemma compat_pair Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : A →
  TY Δ; Γ ⊨ e2 : B →
  TY Δ; Γ ⊨ (e1, e2) : A × B.
Proof.
  intros He1 He2 θ δ k W Hctx. simpl.
  specialize (He1 _ _ _ _ Hctx).
  specialize (He2 _ _ _ _ Hctx).

  eapply (bind [PairRCtx _]); first done.
  intros j v2 W' Hj HW Hv2.
  eapply (bind [PairLCtx _]).
  { eapply expr_rel_mono; last done; [lia | done]. }
  intros j' v1 W'' Hj' HW' Hv1.

  simpl.
  eapply (sem_val_expr_rel _ _ _ _ (v1, v2)%V).
  simp type_interp. exists v1, v2. split_and!; first done.
  - done.
  - eapply val_rel_mono; last done; [lia | done].
Qed.

Lemma compat_fst Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Fst e : A.
Proof.
  intros He θ δ k W Hctx.
  specialize (He _ _ _ _ Hctx).
  simpl. eapply (bind [FstCtx]); first done.
  intros j v W' Hj HW Hv.
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).

  eapply expr_det_step_closure.
  { simpl. apply det_step_fst; apply is_val_of_val. }
  eapply sem_val_expr_rel. eapply val_rel_mono_idx; last done. lia.
Qed.

Lemma compat_snd Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Snd e : B.
Proof.
  intros He θ δ k w Hctx.
  specialize (He _ _ _ _ Hctx).
  simpl. eapply (bind [SndCtx]); first done.
  intros j v W' Hj HW Hv.
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).

  eapply expr_det_step_closure.
  { simpl. apply det_step_snd; apply is_val_of_val. }
  eapply sem_val_expr_rel. eapply val_rel_mono_idx; last done. lia.
Qed.

Lemma compat_injl Δ Γ e A B :
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ InjL e : A + B.
Proof.
  intros He θ δ k W Hctx. simpl.
  specialize (He _ _ _ _ Hctx).
  eapply (bind [InjLCtx]); first done.
  intros j v W' Hj HW Hv.
  eapply (sem_val_expr_rel _ _ _ _ (InjLV v)).
  simp type_interp. left. eauto.
Qed.

Lemma compat_injr Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ InjR e : A + B.
Proof.
  intros He θ δ k W Hctx. simpl.
  specialize (He _ _ _ _ Hctx).
  eapply (bind [InjRCtx]); first done.
  intros j v W' Hj HW Hv.
  eapply (sem_val_expr_rel _ _ _ _ (InjRV v)).
  simp type_interp. eauto.
Qed.

Lemma compat_case Δ Γ e e1 e2 A B C :
  TY Δ; Γ ⊨ e : B + C →
  TY Δ; Γ ⊨ e1 : (B → A) →
  TY Δ; Γ ⊨ e2 : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 : A.
Proof.
  intros He He1 He2 θ δ k W Hctx. simpl.
  specialize (He _ _ _ _ Hctx).
  specialize (He1 _ _ _ _ Hctx).
  specialize (He2 _ _ _ _ Hctx).
  eapply (bind [CaseCtx _ _]); first done.
  intros j v W' Hj HW Hv.
  simp type_interp in Hv. destruct Hv as [(v' & -> & Hv') | (v' & -> & Hv')].
  - simpl. eapply expr_det_step_closure.
    { apply det_step_casel. apply is_val_of_val. }
    eapply (bind [AppLCtx _]).
    { eapply expr_rel_mono; last done; [lia | done]. }
    intros j' v W'' Hj' HW' Hv. simpl.
    simp type_interp in Hv. destruct Hv as (x & e' & -> & ? & Hv).
    eapply expr_det_step_closure. { apply det_step_beta. apply is_val_of_val. }
    apply Hv; first done. eapply val_rel_mono; last done; [lia | done].
  - simpl. eapply expr_det_step_closure.
    { apply det_step_caser. apply is_val_of_val. }
    eapply (bind [AppLCtx _]).
    { eapply expr_rel_mono; last done; [lia | done]. }
    intros j' v W'' Hj' HW' Hv. simpl.
    simp type_interp in Hv. destruct Hv as (x & e' & -> & ? & Hv).
    eapply expr_det_step_closure. { apply det_step_beta. apply is_val_of_val. }
    apply Hv; first done. eapply val_rel_mono; last done; [lia | done].
Qed.

Lemma compat_roll n Γ e A :
  TY n; Γ ⊨ e : (A.[(μ: A)%ty/]) →
  TY n; Γ ⊨ (roll e) : (μ: A).
Proof.
  intros He θ δ k W Hctx. simpl.
  specialize (He _ _ _ _ Hctx).

  eapply (bind [RollCtx]); first done.
  intros j v W' Hj HW Hv.
  eapply (sem_val_expr_rel _ _ _ _ (RollV v)).

  specialize (val_rel_is_closed _ _ _ _ _ Hv) as ?.
  destruct j as [ | j]; simp type_interp; first by eauto.
  exists v. split_and!; [done.. | ].
  intros kd. eapply val_rel_mono_idx; last done. lia.
Qed.

Lemma compat_unroll n Γ e A :
  TY n; Γ ⊨ e : (μ: A) →
  TY n; Γ ⊨ (unroll e) : (A.[(μ: A)%ty/]).
Proof.
  intros He θ δ k W Hctx. simpl.
  specialize (He _ _ _ _ Hctx).

  eapply (bind [UnrollCtx]); first done.
  intros j v W' Hj HW Hv.
  destruct j as [ | j]; first by apply sem_expr_rel_zero_trivial.
  simp type_interp in Hv. destruct Hv as (v' & -> & ? & Hv).
  eapply expr_det_step_closure.
  { simpl. apply det_step_unroll. apply is_val_of_val. }
  eapply sem_val_expr_rel. apply Hv.
Qed.


(** A bit of theory about first-order types *)
Lemma canonical_values_int n Γ e:
  TY n; Γ ⊢ e : Int →
  is_val e →
  ∃ n: Z, e = (#n)%E.
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma canonical_values_bool n Γ e:
  TY n; Γ ⊢ e : Bool →
  is_val e →
  ∃ b: bool, e = (#b)%E.
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma canonical_values_unit n Γ e:
  TY n; Γ ⊢ e : Unit →
  is_val e →
  e = (#LitUnit)%E.
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma canonical_values_prod n Γ e A B :
  TY n; Γ ⊢ e : A × B →
  is_val e →
  ∃ e1 e2, e = (e1, e2)%E ∧ is_val e1 ∧ is_val e2 ∧
    TY n; Γ ⊢ e1 : A ∧ TY n; Γ ⊢ e2 : B .
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma canonical_values_sum n Γ e A B :
  TY n; Γ ⊢ e : A + B →
  is_val e →
  (∃ e', e = InjL e' ∧ is_val e' ∧ TY n; Γ ⊢ e' : A) ∨ (∃ e', e = InjR e' ∧ is_val e' ∧ TY n; Γ ⊢ e' : B).
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma type_wf_fotype a : type_wf 0 a.
Proof. induction a; simpl; eauto. Qed.

(* First-order types are simple. *)
Lemma syn_fo_typed_val a δ k W v :
  TY 0; ∅ ⊢ of_val v : a ↔ 𝒱 a δ k W v.
Proof.
  induction a as [ | | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2 ] in v |-*.
  - split.
    + intros [z Heq]%canonical_values_int; simplify_val; last eauto.
      simp type_interp. eauto.
    + simp type_interp. intros (z & ->). constructor.
  - split.
    + intros (b & Heq)%canonical_values_bool; simplify_val; last eauto.
      simp type_interp. eauto.
    + simp type_interp. intros (b & ->). constructor.
  - split.
    + intros Heq%canonical_values_unit; simplify_val; last eauto.
      simp type_interp; eauto.
    + simp type_interp. intros ->. econstructor.
  - split.
    + simpl. intros (e1 & e2 & ? & (v1 & Heq1)%is_val_spec & (v2 & Heq2)%is_val_spec & H1 & H2)%canonical_values_prod; last eauto.
      simplify_val. apply of_val_pair_inv in H; subst v.
      simp type_interp. exists v1, v2. naive_solver.
    + simpl. simp type_interp. intros (v1 & v2 & -> & Hv1%IH1 & Hv2%IH2). econstructor; done.
  - split.
    + simpl. intros [(e & ? & (v' & Heq)%is_val_spec & H) | (e & ? & (v' & Heq)%is_val_spec & H)]%canonical_values_sum; last eauto.
      * simplify_val. apply of_val_injl_inv in H0; subst v.
        simp type_interp. left. naive_solver.
      * simplify_val. apply of_val_injr_inv in H0; subst v.
        simp type_interp. right. naive_solver.
    + simpl. simp type_interp. intros [(v' & -> & Hv%IH1) | (v' & -> & Hv%IH2)].
      * simpl. eapply typed_injl; last done. apply type_wf_fotype.
      * simpl. eapply typed_injr; last done. apply type_wf_fotype.
Qed.

Lemma wsat_init_heap σ l v a W :
  σ !! l = None →
  wsat W σ →
  TY 0; ∅ ⊢ v : a →
  wsat ((λ σ, ∃ v, σ = <[l := v]> ∅ ∧ TY 0; ∅ ⊢ v : a) :: W) (init_heap l 1 v σ).
Proof.
  intros. simpl. eexists. split; [exists v; split; [reflexivity | ] | split ].
  - done.
  - unfold init_heap. simpl. rewrite right_id.
    rewrite -insert_union_singleton_l. apply insert_mono.
    apply map_empty_subseteq.
  - unfold init_heap. simpl. rewrite right_id. rewrite -delete_difference map_difference_empty.
    rewrite delete_union delete_singleton left_id.
    rewrite delete_notin; done.
Qed.

Lemma compat_new Δ Γ e a :
  TY Δ; Γ ⊨ e : a →
  TY Δ; Γ ⊨ new e : (Ref a).
Proof.
  (* FIXME: exercise for you *)
  (* you may find the lemma [wsat_init_heap] above helpful. *)
(*Qed.*)
Admitted.

Lemma compat_load Δ Γ e a :
  TY Δ; Γ ⊨ e : Ref a →
  TY Δ; Γ ⊨ !e : a.
Proof.
  intros He θ δ k W Hctx.
  eapply (bind [LoadCtx]). { eapply He; done. }
  intros j v W' Hj Hext Hv.
  simp type_interp in Hv.
  destruct Hv as (l & -> & (i & INV & Hlook & ->)).

  simp type_interp.

  intros e' σ σ' W'' n Hext' Hsat' Hn.
  eapply wsat_lookup in Hlook; last by eapply wsat_wext.
  destruct Hlook as (? & Hincl & (v & -> & ?)).
  intros Hred. eapply load_nsteps_inv in Hred as [(-> & -> & -> & Hirred) | [-> Hstep]]; last apply to_of_val.
  { exfalso; apply Hirred.
    exists (of_val v), σ. apply base_contextual_step.
    econstructor. eapply lookup_weaken; last done. apply lookup_insert.
  }
  eapply load_step_inv in Hstep; last apply to_of_val.
  destruct Hstep as (? & v' & [= <-] & Hl & -> & ->).
  eapply lookup_weaken_inv in Hincl; [ | apply lookup_insert | done]. subst v'.
  rewrite to_of_val. eexists _, _. split_and!; [reflexivity | reflexivity | done | ].

  (* use that FO types are simple. *)
  apply syn_fo_typed_val; done.
Qed.

Lemma compat_store Δ Γ e1 e2 a :
  TY Δ; Γ ⊨ e1 : Ref a →
  TY Δ; Γ ⊨ e2 : a →
  TY Δ; Γ ⊨ (e1 <- e2) : Unit.
Proof.
  intros He1 He2 θ δ k W Hctx. simpl.
  eapply (bind [StoreRCtx _]). { eapply He2; done. }
  intros j v W' Hj Hext Hv2.

  eapply (bind [StoreLCtx _]).
  { eapply expr_rel_mono; last eapply He1; done. }
  intros j' v' W'' Hj' Hext' Hv1.
  simp type_interp in Hv1.
  destruct Hv1 as (l & -> & (i & INV & Hlook & ->)).

  simp type_interp.
  intros e' σ σ' W''' n Hext'' Hsat' Hn.
  specialize (wsat_lookup W'' _ i _ ltac:(by eapply wsat_wext) Hlook) as (? & Hincl & (vm & -> & ?)).

  intros [(-> & -> & -> & Hirred) | [-> Hstep]]%store_nsteps_inv.
  { exfalso; apply Hirred.
    exists (Lit LitUnit), (<[l := v]> σ). apply base_contextual_step.
    econstructor. 2: by rewrite to_of_val.
    eapply lookup_weaken; last done. apply lookup_insert.
  }
  apply store_step_inv in Hstep.
  destruct Hstep as (? & v' & [= <-] & Hl & -> & ->).
  eexists _, _. split_and!; [reflexivity | reflexivity | | ].
  2: { simp type_interp. done. }

  (* restore the invariant *)
  destruct Hext'' as (Pre & ->).
  eapply (wsat_update _ _ (length Pre + i) _ _ ); [ done | ..].
  { rewrite lookup_app_r; last lia.
    replace (length Pre + i - length Pre) with i by lia.
    done.
  }
  intros σ' (v'' & -> & _). split.
  { apply lookup_insert_is_Some. by left. }
  exists v. rewrite insert_insert. split; first done.
  eapply syn_fo_typed_val; done.
Qed.


Local Hint Resolve compat_var compat_lam_named compat_lam_anon compat_tlam compat_int compat_bool compat_unit compat_if compat_app compat_tapp compat_pack compat_unpack compat_int_binop compat_int_bool_binop compat_unop compat_pair compat_fst compat_snd compat_injl compat_injr compat_case compat_roll compat_unroll compat_new compat_store compat_load: core.

Lemma sem_soundness Δ Γ e A :
  TY Δ; Γ ⊢ e : A →
  TY Δ; Γ ⊨ e : A.
Proof.
  induction 1 as [ | Δ Γ x e A B Hsyn IH | Δ Γ e A B Hsyn IH| Δ Γ e A Hsyn IH| | | | |  | | | | n Γ e1 e2 op A B C Hop ? ? ? ? | | | | | | | | |  | | | ]; eauto.
  - (* lambda *)
    set (X := elements (dom (<[x := A]>Γ))).
    specialize (syn_typed_closed _ _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_named; last done.
    + apply Hcl. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - (* lambda anon *)
    set (X := elements (dom Γ)).
    specialize (syn_typed_closed _ _ _ _ X Hsyn) as Hcl.
    eapply compat_lam_anon; last done.
    + apply Hcl. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - (* tlam *)
    set (X := elements (dom Γ)).
    specialize (syn_typed_closed _ _ _ _ X Hsyn) as Hcl.
    eapply compat_tlam; last done.
    + apply Hcl. rewrite dom_fmap. apply elem_of_elements.
    + intros ??. by apply elem_of_elements.
  - (* binop *) inversion Hop; subst; eauto.
Qed.

(* dummy delta which we can use if we don't care *)
Program Definition any_type : sem_type := {| sem_type_car := λ k W v, is_closed [] v |}.
Definition δ_any : var → sem_type := λ _, any_type.


Definition safe e h :=
  ∀ e' h' n, red_nsteps n e h e' h' → is_val e'.

Lemma type_safety e A :
  TY 0; ∅ ⊢ e : A →
  safe e ∅.
Proof.
  intros He%sem_soundness e' h' n Hred.
  specialize (He ∅ δ_any (S n) []). simp type_interp in He.
  rewrite subst_map_empty in He.
  edestruct (He ) as (v & W' & Hv & _); [ | done | | | eassumption | ].
  - constructor.
  - done.
  - lia.
  - rewrite <- (of_to_val _ _ Hv). apply is_val_of_val.
Qed.


(** Additional lemmas *)
Lemma semantic_app A B δ k W e1 e2 :
  ℰ (A → B) δ k W e1 →
  ℰ A δ k W e2 →
  ℰ B δ k W (e1 e2).
Proof.
  intros He1 He2.
  eapply (bind [AppRCtx e1]); first done.
  intros j v W' Hj Hincl Hv. eapply (bind [AppLCtx _]).
  { eapply expr_rel_mono; [ | done..]. lia. }
  intros j' v' W'' Hj' Hincl' Hf.
  simp type_interp in Hf. destruct Hf as (x & e & -> & Hcl & Hf).
  eapply expr_det_step_closure.
  { apply det_step_beta. apply is_val_of_val. }
  apply Hf; first done.
  eapply val_rel_mono; [ | done..]. lia.
Qed.
