From stdpp Require Import base relations.
From iris Require Import prelude.
From semantics.lib Require Import maps.
From semantics.ts.systemf_mu_state Require Import lang notation.
From Autosubst Require Export Autosubst.

(** ** Syntactic typing *)
(** We use De Bruijn indices with the help of the Autosubst library. *)
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
  | Ref (A : type)
.

(** Autosubst instances.
  This lets Autosubst do its magic and derive all the substitution functions, etc.
 *)
#[export] Instance Ids_type : Ids type. derive. Defined.
#[export] Instance Rename_type : Rename type. derive. Defined.
#[export] Instance Subst_type : Subst type. derive. Defined.
#[export] Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition typing_context := gmap string type.
Definition heap_context := gmap loc type.
Implicit Types
  (Γ : typing_context)
  (Σ : heap_context)
  (v : val)
  (e : expr)
  (A B : type)
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

(** Shift all the indices in the context by one,
   used when inserting a new type interpretation in Δ. *)
(* [<$>] is notation for the [fmap] operation that maps the substitution over the whole map. *)
(* [ren] is Autosubst's renaming operation -- it renames all type variables according to the given function,
  in this case [(+1)] to shift the variables up by 1. *)
Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)) <$> Γ) (at level 10, format "⤉ Γ").


(** [type_wf n A] states that a type [A] has only free variables up to < [n].
 (in other words, all variables occurring free are strictly bounded by [n]). *)
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
  | type_wf_ref n A :
      type_wf n A →
      type_wf n (Ref A)
.
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

Reserved Notation "'TY' Σ ; n ; Γ ⊢ e : A" (at level 74, e, A at next level).
Inductive syn_typed : heap_context → nat → typing_context → expr → type → Prop :=
  | typed_var Σ n Γ x A :
      Γ !! x = Some A →
      TY Σ; n; Γ ⊢ (Var x) : A
  | typed_lam Σ n Γ x e A B :
      TY Σ; n ; (<[ x := A]> Γ) ⊢ e : B →
      type_wf n A →
      TY Σ; n; Γ ⊢ (Lam (BNamed x) e) : (A → B)
  | typed_lam_anon Σ n Γ e A B :
      TY Σ; n ; Γ ⊢ e : B →
      type_wf n A →
      TY Σ; n; Γ ⊢ (Lam BAnon e) : (A → B)
  | typed_tlam Σ n Γ e A :
      (* we need to shift the context up as we descend under a binder *)
      TY (⤉ Σ); S n; (⤉ Γ) ⊢ e : A →
      TY Σ; n; Γ ⊢ (Λ, e) : (∀: A)
  | typed_tapp Σ n Γ A B e :
      TY Σ; n; Γ ⊢ e : (∀: A) →
      type_wf n B →
      (* A.[B/] is the notation for Autosubst's substitution operation that
        replaces variable 0 by [B] *)
      TY Σ; n; Γ ⊢ (e <>) : (A.[B/])
  | typed_pack Σ n Γ A B e :
      type_wf n B →
      type_wf (S n) A →
      TY Σ; n; Γ ⊢ e : (A.[B/]) →
      TY Σ; n; Γ ⊢ (pack e) : (∃: A)
  | typed_unpack Σ n Γ A B e e' x :
      type_wf n B → (* we should not leak the existential! *)
      TY Σ; n; Γ ⊢ e : (∃: A) →
      (* As we descend under a type variable binder for the typing of [e'],
          we need to shift the indices in [Γ] and [B] up by one.
        On the other hand, [A] is already defined under this binder, so we need not shift it.
      *)
      TY (⤉ Σ); (S n); (<[x := A]>(⤉Γ)) ⊢ e' : (B.[ren (+1)]) →
      TY Σ; n; Γ ⊢ (unpack e as BNamed x in e') : B
  | typed_int Σ n Γ z : TY Σ; n; Γ ⊢ (Lit $ LitInt z) : Int
  | typed_bool Σ n Γ b : TY Σ; n; Γ ⊢ (Lit $ LitBool b) : Bool
  | typed_unit Σ n Γ : TY Σ; n; Γ ⊢ (Lit $ LitUnit) : Unit
  | typed_if Σ n Γ e0 e1 e2 A :
      TY Σ; n; Γ ⊢ e0 : Bool →
      TY Σ; n; Γ ⊢ e1 : A →
      TY Σ; n; Γ ⊢ e2 : A →
      TY Σ; n; Γ ⊢ If e0 e1 e2 : A
  | typed_app Σ n Γ e1 e2 A B :
      TY Σ; n; Γ ⊢ e1 : (A → B) →
      TY Σ; n; Γ ⊢ e2 : A →
      TY Σ; n; Γ ⊢ (e1 e2)%E : B
  | typed_binop Σ n Γ e1 e2 op A B C :
      bin_op_typed op A B C →
      TY Σ; n; Γ ⊢ e1 : A →
      TY Σ; n; Γ ⊢ e2 : B →
      TY Σ; n; Γ ⊢ BinOp op e1 e2 : C
  | typed_unop Σ n Γ e op A B :
      un_op_typed op A B →
      TY Σ; n; Γ ⊢ e : A →
      TY Σ; n; Γ ⊢ UnOp op e : B
  | typed_pair Σ n Γ e1 e2 A B :
      TY Σ; n; Γ ⊢ e1 : A →
      TY Σ; n; Γ ⊢ e2 : B →
      TY Σ; n; Γ ⊢ (e1, e2) : A × B
  | typed_fst Σ n Γ e A B :
      TY Σ; n; Γ ⊢ e : A × B →
      TY Σ; n; Γ ⊢ Fst e : A
  | typed_snd Σ n Γ e A B :
      TY Σ; n; Γ ⊢ e : A × B →
      TY Σ; n; Γ ⊢ Snd e : B
  | typed_injl Σ n Γ e A B :
      type_wf n B →
      TY Σ; n; Γ ⊢ e : A →
      TY Σ; n; Γ ⊢ InjL e : A + B
  | typed_injr Σ n Γ e A B :
      type_wf n A →
      TY Σ; n; Γ ⊢ e : B →
      TY Σ; n; Γ ⊢ InjR e : A + B
  | typed_case Σ n Γ e e1 e2 A B C :
      TY Σ; n; Γ ⊢ e : B + C →
      TY Σ; n; Γ ⊢ e1 : (B → A) →
      TY Σ; n; Γ ⊢ e2 : (C → A) →
      TY Σ; n; Γ ⊢ Case e e1 e2 : A
  | typed_roll Σ n Γ e A :
      TY Σ; n; Γ ⊢ e : (A.[(μ: A)/]) →
      TY Σ; n; Γ ⊢ (roll e) : (μ: A)
  | typed_unroll Σ n Γ e A :
      TY Σ; n; Γ ⊢ e : (μ: A) →
      TY Σ; n; Γ ⊢ (unroll e) : (A.[(μ: A)/])
  | typed_loc Σ Δ Γ l A :
      Σ !! l = Some A →
      TY Σ; Δ; Γ ⊢ (Lit $ LitLoc l) : (Ref A)
  | typed_load Σ Δ Γ e A :
      TY Σ; Δ; Γ ⊢ e : (Ref A) →
      TY Σ; Δ; Γ ⊢ !e : A
  | typed_store Σ Δ Γ e1 e2 A :
      TY Σ; Δ; Γ ⊢ e1 : (Ref A) →
      TY Σ; Δ; Γ ⊢ e2 : A →
      TY Σ; Δ; Γ ⊢ (e1 <- e2) : Unit
  | typed_new Σ Δ Γ e A :
      TY Σ; Δ; Γ ⊢ e : A →
      TY Σ; Δ; Γ ⊢ (new e) : Ref A
where "'TY' Σ ; n ; Γ ⊢ e : A" := (syn_typed Σ n Γ e%E A%ty).
#[export] Hint Constructors syn_typed : core.

(** Examples *)
Goal TY ∅; 0; ∅ ⊢ (λ: "x", #1 + "x")%E : (Int → Int).
Proof. eauto. Qed.
(** [∀: #0 → #0] corresponds to [∀ α. α → α] with named binders. *)
Goal TY ∅; 0; ∅ ⊢ (Λ, λ: "x", "x")%E : (∀: #0 → #0).
Proof. repeat econstructor. Qed.
Goal TY ∅; 0; ∅ ⊢ (pack ((λ: "x", "x"), #42)) : ∃: (#0 → #0) × #0.
Proof.
  apply (typed_pack _ _ _ _ Int).
  - eauto.
  - repeat econstructor.
  - (* [asimpl] is Autosubst's tactic for simplifying goals involving type substitutions. *)
    asimpl. eauto.
Qed.
Goal TY ∅; 0; ∅ ⊢ (unpack (pack ((λ: "x", "x"), #42)) as "y" in (λ: "x", #1337) ((Fst "y") (Snd "y"))) : Int.
Proof.
  (* if we want to typecheck stuff with existentials, we need a bit more explicit proofs.
    Letting eauto try to instantiate the evars becomes too expensive. *)
  apply (typed_unpack _ _ _ ((#0 → #0) × #0)%ty).
  - done.
  - apply (typed_pack _ _ _ _ Int); asimpl; eauto.
    repeat econstructor.
  - eapply (typed_app _ _ _ _ _ (#0)%ty); eauto 10.
Qed.

(** fails: we are not allowed to leak the existential *)
Goal TY ∅; 0; ∅ ⊢ (unpack (pack ((λ: "x", "x"), #42)) as "y" in (Fst "y") (Snd "y")) : #0.
Proof.
  apply (typed_unpack _ _ _ ((#0 → #0) × #0)%ty).
Abort.

(* derived typing rule for match *)
Lemma typed_match Σ n Γ e e1 e2 x1 x2 A B C :
  type_wf n B →
  type_wf n C →
  TY Σ; n; Γ ⊢ e : B + C →
  TY Σ; n; <[x1 := B]> Γ ⊢ e1 : A →
  TY Σ; n; <[x2 := C]> Γ ⊢ e2 : A →
  TY Σ; n; Γ ⊢ match: e with InjL (BNamed x1) => e1 | InjR (BNamed x2) => e2 end : A.
Proof. eauto. Qed.

Lemma syn_typed_closed Σ n Γ e A X :
  TY Σ; n; Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  induction 1 as [ | ???????? IH | | Σ n Γ e A H IH | | | Σ n Γ A B e e' x Hwf H1 IH1 H2 IH2 | | | | | | | | | | | | | | | | | | | ] in X |-*; simpl; intros Hx; try done.

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

(** *** Lemmas about [type_wf] *)
Lemma type_wf_mono n m A:
  type_wf n A → n ≤ m → type_wf m A.
Proof.
  induction 1 in m |-*; eauto with lia.
Qed.

Lemma type_wf_rename n A δ:
  type_wf n A →
  (∀ i j, i < j → δ i < δ j) →
  type_wf (δ n) (rename δ A).
Proof.
  induction 1 in δ |-*; intros Hmon; simpl; eauto.
  all: econstructor; eapply type_wf_mono; first eapply IHtype_wf; last done.
  all: intros i j Hlt; destruct i, j; simpl; try lia.
  all: by eapply lt_n_S, Hmon, lt_S_n.
Qed.

(** [A.[σ]], i.e. [A] with the substitution [σ] applied to it, is well-formed under [m] if
   [A] is well-formed under [n] and all the things we substitute up to [n] are well-formed under [m].
 *)
Lemma type_wf_subst n m A σ:
  type_wf n A →
  (∀ x, x < n → type_wf m (σ x)) →
  type_wf m A.[σ].
Proof.
  induction 1 in m, σ |-*; intros Hsub; simpl; eauto.
  + econstructor; eapply IHtype_wf.
    intros [|x]; rewrite /up //=.
    - econstructor. lia.
    - intros Hlt % lt_S_n. eapply type_wf_rename; eauto.
      intros i j Hlt'; simpl; lia.
  + econstructor; eapply IHtype_wf.
    intros [|x]; rewrite /up //=.
    - econstructor. lia.
    - intros Hlt % lt_S_n. eapply type_wf_rename; eauto.
      intros i j Hlt'; simpl; lia.
  + econstructor. eapply IHtype_wf.
    intros [|x]; rewrite /up //=.
    - econstructor. lia.
    - intros Hlt % lt_S_n. eapply type_wf_rename; eauto.
      intros ???. simpl; lia.
Qed.

Fixpoint free_vars A : nat → Prop :=
  match A with
  | TVar n => λ m, m = n
  | Int => λ _, False
  | Bool => λ _, False
  | Unit => λ _, False
  | Fun A B => λ n, free_vars A n ∨ free_vars B n
  | Prod A B => λ n, free_vars A n ∨ free_vars B n
  | Sum A B => λ n, free_vars A n ∨ free_vars B n
  | TForall A => λ n, free_vars A (S n)
  | TExists A => λ n, free_vars A (S n)
  | TMu A => λ n, free_vars A (S n)
  | Ref A => λ n, free_vars A n
  end.

Definition bounded n A :=
  (∀ x, free_vars A x → x < n).

Lemma type_wf_bounded n A:
  type_wf n A ↔ bounded n A.
Proof.
  rewrite /bounded; split.
  - induction 1; simpl; try naive_solver.
    + intros x Hfree % IHtype_wf. lia.
    + intros x Hfree % IHtype_wf. lia.
    + intros x Hfree % IHtype_wf. lia.
  - induction A in n |-*; simpl; eauto.
    + intros Hsub. econstructor. eapply IHA.
      intros ??. destruct x as [|x]; first lia.
      eapply Hsub in H. lia.
    + intros Hsub. econstructor. eapply IHA.
      intros ??. destruct x as [|x]; first lia.
      eapply Hsub in H. lia.
    + intros Hsub. econstructor; eauto.
    + intros Hsub. econstructor; eauto.
    + intros Hsub. econstructor; eauto.
    + intros Hsub. econstructor. eapply IHA.
      intros ??. destruct x as [|x]; first lia.
      eapply Hsub in H. lia.
Qed.

Lemma free_vars_rename A x δ:
  free_vars A x → free_vars (rename δ A) (δ x).
Proof.
  induction A in x, δ |-*; simpl; try naive_solver.
  - intros Hf. apply (IHA (S x) (upren δ) Hf).
  - intros Hf. apply (IHA (S x) (upren δ) Hf).
  - intros Hf. apply (IHA (S x) (upren δ) Hf).
Qed.

Lemma free_vars_subst x n A σ :
  bounded n A.[σ] → free_vars A x → bounded n (σ x).
Proof.
  induction A in n, σ, x |-*; simpl; try naive_solver.
  - rewrite -type_wf_bounded. inversion 1; subst. revert H2; clear H.
    rewrite type_wf_bounded.
    intros Hbd Hfree. eapply IHA in Hbd; last done.
    revert Hbd. rewrite /up //=.
    intros Hbd y Hf. enough (S y < S n) by lia.
    eapply Hbd. simpl. by eapply free_vars_rename.
  - rewrite -type_wf_bounded. inversion 1; subst. revert H2; clear H.
    rewrite type_wf_bounded.
    intros Hbd Hfree. eapply IHA in Hbd; last done.
    revert Hbd. rewrite /up //=.
    intros Hbd y Hf. enough (S y < S n) by lia.
    eapply Hbd. simpl. by eapply free_vars_rename.
  - rewrite -!type_wf_bounded. inversion 1; subst.
    revert H3 H4. rewrite !type_wf_bounded. naive_solver.
  - rewrite -!type_wf_bounded. inversion 1; subst.
    revert H3 H4. rewrite !type_wf_bounded. naive_solver.
  - rewrite -!type_wf_bounded. inversion 1; subst.
    revert H3 H4. rewrite !type_wf_bounded. naive_solver.
  - rewrite -type_wf_bounded. inversion 1; subst. revert H2; clear H.
    rewrite type_wf_bounded.
    intros Hbd Hfree. eapply IHA in Hbd; last done.
    revert Hbd. rewrite /up //=.
    intros Hbd y Hf. enough (S y < S n) by lia.
    eapply Hbd. simpl. by eapply free_vars_rename.
Qed.

Lemma type_wf_rec_type n A:
  type_wf n A.[(μ: A)%ty/] → type_wf (S n) A.
Proof.
  rewrite !type_wf_bounded. intros Hbound x Hfree.
  eapply free_vars_subst in Hbound; last done.
  destruct x as [|x]; first lia; simpl in Hbound.
  eapply type_wf_bounded in Hbound. inversion Hbound; subst; lia.
Qed.

Lemma type_wf_single_subst n A B: type_wf n B → type_wf (S n) A → type_wf n A.[B/].
Proof.
  intros HB HA. eapply type_wf_subst; first done.
  intros [|x]; simpl; eauto.
  intros ?; econstructor. lia.
Qed.

(** We lift [type_wf] to well-formedness of contexts *)
Definition ctx_wf n Γ := (∀ x A, Γ !! x = Some A → type_wf n A).

Lemma ctx_wf_empty n : ctx_wf n ∅.
Proof. rewrite /ctx_wf. set_solver. Qed.

Lemma ctx_wf_insert n x Γ A: ctx_wf n Γ → type_wf n A → ctx_wf n (<[x := A]> Γ).
Proof. intros H1 H2 y B. rewrite lookup_insert_Some. naive_solver. Qed.

Lemma ctx_wf_up n Γ:
  ctx_wf n Γ → ctx_wf (S n) (⤉Γ).
Proof.
  intros Hwf x A; rewrite lookup_fmap.
  intros (B & Hlook & ->) % fmap_Some.
  asimpl. eapply type_wf_subst; first eauto.
  intros y Hlt. simpl. econstructor. lia.
Qed.

Definition heap_ctx_wf Δ (Σ: heap_context) := (∀ x A, Σ !! x = Some A → type_wf Δ A).

Lemma heap_ctx_wf_empty n : heap_ctx_wf n ∅.
Proof. rewrite /heap_ctx_wf. set_solver. Qed.

Lemma heap_ctx_wf_insert n l Σ A: heap_ctx_wf n Σ → type_wf n A → heap_ctx_wf n (<[l := A]> Σ).
Proof. intros H1 H2 y B. rewrite lookup_insert_Some. naive_solver. Qed.

Lemma heap_ctx_wf_up n Σ:
  heap_ctx_wf n Σ → heap_ctx_wf (S n) (⤉Σ).
Proof.
  intros Hwf x A; rewrite lookup_fmap.
  intros (B & Hlook & ->) % fmap_Some.
  asimpl. eapply type_wf_subst; first eauto.
  intros y Hlt. simpl. econstructor. lia.
Qed.

#[global]
Hint Resolve ctx_wf_empty ctx_wf_insert ctx_wf_up heap_ctx_wf_up heap_ctx_wf_empty heap_ctx_wf_empty : core.

(** Well-typed terms at [A] under a well-formed context have well-formed types [A].*)
Lemma syn_typed_wf Σ n Γ e A:
  ctx_wf n Γ →
  heap_ctx_wf n Σ →
  TY Σ; n; Γ ⊢ e : A →
  type_wf n A.
Proof.
  intros Hwf Hhwf; induction 1 as [ | Σ n Γ x e A B Hty IH Hwfty | | Σ n Γ e A Hty IH | Σ n Γ A B e Hty IH Hwfty | Σ n Γ A B e Hwfty Hty IH| | |  | | | Σ n Γ e1 e2 A B HtyA IHA HtyB IHB | Σ n Γ e1 e2 op A B C Hop HtyA IHA HtyB IHB | Σ n Γ e op A B Hop H IH | Σ n Γ e1 e2 A B HtyA IHA HtyB IHB | Σ n Γ e A B Hty IH | Σ n Γ e A B Hty IH | Σ n Γ e A B Hwfty Hty IH | Σ n Γ e A B Hwfty Hty IH| Σ n Γ e e1 e2 A B C Htye IHe Htye1 IHe1 Htye2 IHe2 | Σ n Γ e A Hty IH | Σ n Γ e A Hty IH | Σ n Γ l A Hlook| Σ n Γ e A Hty IH | Σ n Γ e1 e2 A Hty1 IH1 Hty2 IH2 | Σ n Γ e A Hty IH]; eauto.
  - eapply type_wf_single_subst; first done.
    specialize (IH Hwf Hhwf) as Hwf'.
    by inversion Hwf'.
  - specialize (IHA Hwf Hhwf) as Hwf'.
    by inversion Hwf'; subst.
  - inversion Hop; subst; eauto.
  - inversion Hop; subst; eauto.
  - specialize (IH Hwf Hhwf) as Hwf'. by inversion Hwf'; subst.
  - specialize (IH Hwf Hhwf) as Hwf'. by inversion Hwf'; subst.
  - specialize (IHe1 Hwf Hhwf) as Hwf''. by inversion Hwf''; subst.
  - specialize (IH Hwf Hhwf) as Hwf'%type_wf_rec_type.
    by econstructor.
  - eapply type_wf_single_subst; first by apply IH.
    specialize (IH Hwf Hhwf) as Hwf'.
    by inversion Hwf'.
  - specialize (IH Hwf Hhwf) as Hwf'. by inversion Hwf'.
Qed.

Lemma renaming_ctx_inclusion Γ Δ : Γ ⊆ Δ → ⤉Γ ⊆ ⤉Δ.
Proof.
  eapply map_fmap_mono.
Qed.

Lemma renaming_heap_ctx_inclusion Σ Σ' : Σ ⊆ Σ' → ⤉Σ ⊆ ⤉Σ'.
Proof.
  eapply map_fmap_mono.
Qed.

Lemma typed_weakening n m Γ Δ e A Σ Σ' :
  TY Σ; n; Γ ⊢ e : A →
  Γ ⊆ Δ →
  Σ ⊆ Σ' →
  n ≤ m →
  TY Σ'; m; Δ ⊢ e : A.
Proof.
  induction 1 as [| Σ n Γ x e A B Htyp IH | | Σ n Γ e A Htyp IH | | | Σ n Γ A B e e' x Hwf H1 IH1 H2 IH2 | | | | | | | | |  | | | | | | | Σ n Γ l A Hlook | | | ] in Σ', Δ, m |-*; intros Hsub1 Hsub2 Hle; eauto using type_wf_mono.
  - (* var *) econstructor. by eapply lookup_weaken.
  - (* lam *) econstructor; last by eapply type_wf_mono. eapply IH; eauto. by eapply insert_mono.
  - (* tlam *) econstructor. eapply IH; last by lia.
    + by eapply renaming_ctx_inclusion.
    + by eapply renaming_heap_ctx_inclusion.
  - (* pack *)
    econstructor; last naive_solver. all: (eapply type_wf_mono; [ done | lia]).
  - (* unpack *) econstructor.
    + eapply type_wf_mono; done.
    + eapply IH1; done.
    + eapply IH2; last lia.
      * apply insert_mono. by apply renaming_ctx_inclusion.
      * by apply renaming_heap_ctx_inclusion.
  - (* loc *)
    econstructor; by eapply lookup_weaken.
Qed.

Lemma type_wf_subst_dom σ τ n A:
  type_wf n A →
  (∀ m, m < n → σ m = τ m) →
  A.[σ] = A.[τ].
Proof.
  induction 1 in σ, τ |-*; simpl; eauto.
  - (* tforall *)
    intros Heq; asimpl. f_equal.
    eapply IHtype_wf; intros [|m]; rewrite /up; simpl; first done.
    intros Hlt. f_equal. eapply Heq. lia.
  - (* texists *)
    intros Heq; asimpl. f_equal.
    eapply IHtype_wf. intros [ | m]; rewrite /up; simpl; first done.
    intros Hlt. f_equal. apply Heq. lia.
  - (* fun *) intros ?. f_equal; eauto.
  - (* prod *) intros ?. f_equal; eauto.
  - (* sum *) intros ?. f_equal; eauto.
  - (* rec *)
    intros Heq; asimpl. f_equal.
    eapply IHtype_wf; intros [|m]; rewrite /up; simpl; first done.
    intros Hlt. f_equal. eapply Heq. lia.
  - (* ref *)
    intros ?. f_equal. eapply IHtype_wf. done.
Qed.

Lemma type_wf_closed A σ:
  type_wf 0 A →
  A.[σ] = A.
Proof.
  intros Hwf; erewrite (type_wf_subst_dom _ (ids) 0).
  - by asimpl.
  - done.
  - intros ??; lia.
Qed.

Lemma heap_ctx_closed Σ σ:
  heap_ctx_wf 0 Σ →
  fmap (subst σ) Σ = Σ.
Proof.
  intros Hwf. eapply stdpp.fin_maps.map_eq; intros l.
  rewrite lookup_fmap. destruct lookup as [A|]eqn: H; last done; simpl.
  f_equal. eapply type_wf_closed. by eapply Hwf.
Qed.



(** Typing inversion lemmas *)
Lemma var_inversion Σ Γ n (x: string) A: TY Σ; n; Γ ⊢ x : A → Γ !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Σ n Γ (x: string) e C:
  TY Σ; n; Γ ⊢ (λ: x, e) : C →
  ∃ A B, C = (A → B)%ty ∧ type_wf n A ∧ TY Σ; n; <[x:=A]> Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lam_anon_inversion Σ n Γ e C:
  TY Σ; n; Γ ⊢ (λ: <>, e) : C →
  ∃ A B, C = (A → B)%ty ∧ type_wf n A ∧ TY Σ; n; Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma app_inversion Σ n Γ e1 e2 B:
  TY Σ; n; Γ ⊢ e1 e2 : B →
  ∃ A, TY Σ; n; Γ ⊢ e1 : (A → B) ∧ TY Σ; n; Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma if_inversion Σ n Γ e0 e1 e2 B:
  TY Σ; n; Γ ⊢ If e0 e1 e2 : B →
  TY Σ; n; Γ ⊢ e0 : Bool ∧ TY Σ; n; Γ ⊢ e1 : B ∧ TY Σ; n; Γ ⊢ e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma binop_inversion Σ n Γ op e1 e2 B:
  TY Σ; n; Γ ⊢ BinOp op e1 e2 : B →
  ∃ A1 A2, bin_op_typed op A1 A2 B ∧ TY Σ; n; Γ ⊢ e1 : A1 ∧ TY Σ; n; Γ ⊢ e2 : A2.
Proof. inversion 1; subst; eauto. Qed.

Lemma unop_inversion Σ n Γ op e B:
  TY Σ; n; Γ ⊢ UnOp op e : B →
  ∃ A, un_op_typed op A B ∧ TY Σ; n; Γ ⊢ e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma type_app_inversion Σ n Γ e B:
  TY Σ; n; Γ ⊢ e <> : B →
  ∃ A C, B = A.[C/] ∧ type_wf n C ∧ TY Σ; n; Γ ⊢ e : (∀: A).
Proof. inversion 1; subst; eauto. Qed.

Lemma type_lam_inversion Σ n Γ e B:
  TY Σ; n; Γ ⊢ (Λ,e) : B →
  ∃ A, B = (∀: A)%ty ∧ TY ⤉Σ; (S n); ⤉Γ ⊢ e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma type_pack_inversion Σ n Γ e B :
  TY Σ; n; Γ ⊢ (pack e) : B →
  ∃ A C, B = (∃: A)%ty ∧ TY Σ; n; Γ ⊢ e : (A.[C/])%ty ∧ type_wf n C ∧ type_wf (S n) A.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma type_unpack_inversion Σ n Γ e e' x B :
  TY Σ; n; Γ ⊢ (unpack e as x in e') : B →
  ∃ A x', x = BNamed x' ∧ type_wf n B ∧ TY Σ; n; Γ ⊢ e : (∃: A) ∧ TY ⤉Σ; S n; <[x' := A]> (⤉Γ) ⊢ e' : (B.[ren (+1)]).
Proof. inversion 1; subst; eauto 10. Qed.

Lemma pair_inversion Σ n Γ e1 e2 C :
  TY Σ; n; Γ ⊢ (e1, e2) : C →
  ∃ A B, C = (A × B)%ty ∧ TY Σ; n; Γ ⊢ e1 : A ∧ TY Σ; n; Γ ⊢ e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma fst_inversion Σ n Γ e A :
  TY Σ; n; Γ ⊢ Fst e : A →
  ∃ B, TY Σ; n; Γ ⊢ e : A × B.
Proof. inversion 1; subst; eauto. Qed.

Lemma snd_inversion Σ n Γ e B :
  TY Σ; n; Γ ⊢ Snd e : B →
  ∃ A, TY Σ; n; Γ ⊢ e : A × B.
Proof. inversion 1; subst; eauto. Qed.

Lemma injl_inversion Σ n Γ e C :
  TY Σ; n; Γ ⊢ InjL e : C →
  ∃ A B, C = (A + B)%ty ∧ TY Σ; n; Γ ⊢ e : A ∧ type_wf n B.
Proof. inversion 1; subst; eauto. Qed.

Lemma injr_inversion Σ n Γ e C :
  TY Σ; n; Γ ⊢ InjR e : C →
  ∃ A B, C = (A + B)%ty ∧ TY Σ; n; Γ ⊢ e : B ∧ type_wf n A.
Proof. inversion 1; subst; eauto. Qed.

Lemma case_inversion Σ n Γ e e1 e2 A :
  TY Σ; n; Γ ⊢ Case e e1 e2 : A →
  ∃ B C, TY Σ; n; Γ ⊢ e : B + C ∧ TY Σ; n; Γ ⊢ e1 : (B → A) ∧ TY Σ; n; Γ ⊢ e2 : (C → A).
Proof. inversion 1; subst; eauto. Qed.

Lemma roll_inversion Σ n Γ e B:
  TY Σ; n; Γ ⊢ (roll e) : B →
  ∃ A, B = (μ: A)%ty ∧ TY Σ; n; Γ ⊢ e : A.[μ: A/].
Proof. inversion 1; subst; eauto. Qed.

Lemma unroll_inversion Σ n Γ e B:
  TY Σ; n; Γ ⊢ (unroll e) : B →
  ∃ A, B = (A.[μ: A/])%ty ∧ TY Σ; n; Γ ⊢ e : μ: A.
Proof. inversion 1; subst; eauto. Qed.

Lemma new_inversion Σ n Γ e B :
  TY Σ; n; Γ ⊢ (new e) : B →
  ∃ A, B = Ref A ∧ TY Σ; n; Γ ⊢ e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma load_inversion Σ n Γ e B:
  TY Σ; n; Γ ⊢ ! e : B →
  TY Σ; n; Γ ⊢ e : Ref B.
Proof. inversion 1; subst; eauto. Qed.

Lemma store_inversion Σ n Γ e1 e2 B:
  TY Σ; n; Γ ⊢ (e1 <- e2) : B →
  ∃ A, B = Unit ∧ TY Σ; n; Γ ⊢ e1 : Ref A ∧ TY Σ; n; Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma typed_substitutivity Σ n e e' Γ (x: string) A B :
  heap_ctx_wf 0 Σ →
  TY Σ; 0; ∅ ⊢ e' : A →
  TY Σ; n; (<[x := A]> Γ) ⊢ e : B →
  TY Σ; n; Γ ⊢ lang.subst x e' e : B.
Proof.
  intros HwfΣ He'. induction e as [| y | y | | | | | | | | | | | | | | | | | | | ] in n, B, Γ |-*; simpl.
  - inversion 1; subst; auto.
  - intros Hp % var_inversion.
    destruct (decide (x = y)).
    + subst. rewrite lookup_insert in Hp. injection Hp as ->.
      eapply typed_weakening; [done| | done |lia]. apply map_empty_subseteq.
    + rewrite lookup_insert_ne in Hp; last done. auto.
  - destruct y as [ | y].
    { intros (A' & C & -> & Hwf & Hty) % lam_anon_inversion.
      econstructor; last done. destruct decide as [Heq|].
      + congruence.
      + eauto.
    }
    intros (A' & C & -> & Hwf & Hty) % lam_inversion.
    econstructor; last done. destruct decide as [Heq|].
    + injection Heq as [= ->]. by rewrite insert_insert in Hty.
    + rewrite insert_commute in Hty; last naive_solver. eauto.
  - intros (C & Hty1 & Hty2) % app_inversion. eauto.
  - intros (? & Hop & H1) % unop_inversion.
    destruct op; inversion Hop; subst; eauto.
  - intros (? & ? & Hop & H1 & H2) % binop_inversion.
    destruct op; inversion Hop; subst; eauto.
  - intros (H1 & H2 & H3)%if_inversion. naive_solver.
  - intros (C & D & -> & Hwf & Hty) % type_app_inversion. eauto.
  - intros (C & -> & Hty)%type_lam_inversion. econstructor.
    rewrite heap_ctx_closed //=.
    eapply IHe. revert Hty. rewrite fmap_insert.
    eapply syn_typed_wf in He'; eauto.
    rewrite heap_ctx_closed //=.
    rewrite type_wf_closed; eauto.
  - intros (C & D & -> & Hty & Hwf1 & Hwf2)%type_pack_inversion.
    econstructor; [done..|]. apply IHe. done.
  - intros (C & x' & -> & Hwf & Hty1 & Hty2)%type_unpack_inversion.
    econstructor; first done.
    + eapply IHe1. done.
    + destruct decide as [Heq | ].
      * injection Heq as [= ->]. by rewrite fmap_insert insert_insert in Hty2.
      * rewrite fmap_insert in Hty2. rewrite insert_commute in Hty2; last naive_solver.
        revert Hty2. rewrite heap_ctx_closed//=. intros Hty2.
        eapply IHe2. rewrite type_wf_closed in Hty2; first done.
        eapply syn_typed_wf; last apply He'; eauto.
  - intros (? & ? & -> & ? & ?) % pair_inversion. eauto.
  - intros (? & ?)%fst_inversion. eauto.
  - intros (? & ?)%snd_inversion. eauto.
  - intros (? & ? & -> & ? & ?)%injl_inversion. eauto.
  - intros (? & ? & -> & ? & ?)%injr_inversion. eauto.
  - intros (? & ? & ? & ? & ?)%case_inversion. eauto.
  - intros (C & -> & Hty) % roll_inversion. eauto.
  - intros (C & -> & Hty) % unroll_inversion. eauto.
  - intros Hty % load_inversion. eauto.
  - intros (C & -> & Hty1 & Hty2)% store_inversion. eauto.
  - intros (C & -> & Hty) % new_inversion. eauto.
Qed.

(** Canonical values *)
Lemma canonical_values_arr Σ n Γ e A B:
  TY Σ; n; Γ ⊢ e : (A → B) →
  is_val e →
  ∃ x e', e = (λ: x, e')%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_forall Σ n Γ e A:
  TY Σ; n; Γ ⊢ e : (∀: A)%ty →
  is_val e →
  ∃ e', e = (Λ, e')%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_exists Σ n Γ e A :
  TY Σ; n; Γ ⊢ e : (∃: A) →
  is_val e →
  ∃ e', e = (pack e')%E.
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma canonical_values_int Σ n Γ e:
  TY Σ; n; Γ ⊢ e : Int →
  is_val e →
  ∃ n: Z, e = (#n)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_bool Σ n Γ e:
  TY Σ; n; Γ ⊢ e : Bool →
  is_val e →
  ∃ b: bool, e = (#b)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_unit Σ n Γ e:
  TY Σ; n; Γ ⊢ e : Unit →
  is_val e →
  e = (#LitUnit)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_prod Σ n Γ e A B :
  TY Σ; n; Γ ⊢ e : A × B →
  is_val e →
  ∃ e1 e2, e = (e1, e2)%E ∧ is_val e1 ∧ is_val e2.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_sum Σ n Γ e A B :
  TY Σ; n; Γ ⊢ e : A + B →
  is_val e →
  (∃ e', e = InjL e' ∧ is_val e') ∨ (∃ e', e = InjR e' ∧ is_val e').
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_rec Σ n Γ e A:
  TY Σ; n; Γ ⊢ e : (μ: A) →
  is_val e →
  ∃ e', e = (roll e')%E ∧ is_val e'.
Proof.
  inversion 1; simpl; subst; naive_solver.
Qed.

Lemma canonical_values_ref Σ n Γ e A:
  TY Σ; n; Γ ⊢ e : Ref A →
  is_val e →
  ∃ l: loc, e = (#l)%E ∧ Σ !! l = Some A.
Proof.
  inversion 1; simpl; subst; naive_solver.
Qed.

(** Progress *)
Definition heap_type (h: heap) Σ :=
  ∀ l A, Σ !! l = Some A → ∃ v, h !! l = Some v ∧ TY Σ; 0; ∅ ⊢ of_val v : A.

Lemma typed_progress Σ e h A:
  heap_type h Σ →
  TY Σ; 0; ∅ ⊢ e : A →
  is_val e ∨ reducible e h.
Proof.
  intros Hheap. remember ∅ as Γ. remember 0 as n.
  induction 1 as [| | | | Σ n Γ A B e Hty IH | Σ n Γ A B e Hwf Hwf' Hty IH | Σ n Γ A B e e' x Hwf Hty1 IH1 Hty2 IH2 | | | | Σ n Γ e0 e1 e2 A Hty1 IH1 Hty2 IH2 Hty3 IH3 | Σ n Γ e1 e2 A B Hty IH1 _ IH2 | Σ n Γ e1 e2 op A B C Hop Hty1 IH1 Hty2 IH2 | Σ n Γ e op A B Hop Hty IH | Σ n Γ e1 e2 A B Hty1 IH1 Hty2 IH2 | Σ n Γ e A B Hty IH | Σ n Γ e A B Hty IH | Σ n Γ e A B Hwf Hty IH | Σ n Γ e A B Hwf Hty IH| Σ n Γ e e1 e2 A B C Htye IHe Htye1 IHe1 Htye2 IHe2 | Σ n Γ e A Hty IH | Σ n Γ e A Hty IH | Σ n Γ l A Hlook | Σ n Γ e A Hty IH | Σ n Γ e1 e2 A Hty1 IH1 Hty2 IH2 | Σ n Γ e A Hty IH ].
  - subst. naive_solver.
  - left. done.
  - left. done.
  - left; done.
  - right. destruct (IH Hheap HeqΓ Heqn) as [H1|H1].
    + eapply canonical_values_forall in Hty as [e' ->]; last done.
      eexists _, _. eapply base_contextual_step. eapply TBetaS.
    + destruct H1 as (e' & h' & H1). eexists _, _.
      eapply (fill_contextual_step [TAppCtx]). done.
  - (* pack *)
    destruct (IH Hheap HeqΓ Heqn) as [H | H].
    + by left.
    + right. destruct H as (e' & h' & H). eexists _, _. eapply (fill_contextual_step [PackCtx]). done.
  - (* unpack *)
    destruct (IH1 Hheap HeqΓ Heqn) as [H | H].
    + eapply canonical_values_exists in Hty1 as [e'' ->]; last done.
      right. eexists _, _. eapply base_contextual_step. constructor; last done.
      done.
    + right. destruct H as (e'' & h'' & H). eexists _, _.
      eapply (fill_contextual_step [UnpackCtx _ _]). done.
  - (* int *)left. done.
  - (* bool*) left. done.
  - (* unit *) left. done.
  - (* if *)
    destruct (IH1 Hheap HeqΓ Heqn) as [H1 | H1].
    + eapply canonical_values_bool in Hty1 as (b & ->); last done.
      right. destruct b; eexists _, _; eapply base_contextual_step; constructor.
    + right. destruct H1 as (e0' & h' & Hstep).
      eexists _, _. by eapply (fill_contextual_step [IfCtx _ _]).
  - (* app *)
    destruct (IH2 Hheap HeqΓ Heqn) as [H2|H2]; [destruct (IH1 Hheap HeqΓ Heqn) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (x & e & ->); last done.
      right. eexists _, _.
      eapply base_contextual_step, BetaS; eauto.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as (e1' & h' & Hstep).
      eexists _, _. eapply (fill_contextual_step [AppLCtx v]). done.
    + right. destruct H2 as (e2' & h' & H2).
      eexists _, _. eapply (fill_contextual_step [AppRCtx e1]). done.
  - (* binop *)
    assert (A = Int ∧ B = Int) as [-> ->].
    { inversion Hop; subst A B C; done. }
    destruct (IH2 Hheap HeqΓ Heqn) as [H2|H2]; [destruct (IH1 Hheap HeqΓ Heqn) as [H1|H1]|].
    + right. eapply canonical_values_int in Hty1 as [n1 ->]; last done.
      eapply canonical_values_int in Hty2 as [n2 ->]; last done.
      inversion Hop; subst; simpl.
      all: eexists _, _; eapply base_contextual_step; eapply BinOpS; eauto.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as (e1' & h' & Hstep).
      eexists _, _. eapply (fill_contextual_step [BinOpLCtx op v]). done.
    + right. destruct H2 as (e2' & h' & H2).
      eexists _, _. eapply (fill_contextual_step [BinOpRCtx op e1]). done.
  - (* unop *)
    inversion Hop; subst A B op.
    + right. destruct (IH Hheap HeqΓ Heqn) as [H2 | H2].
      * eapply canonical_values_bool in Hty as [b ->]; last done.
        eexists _, _; eapply base_contextual_step; eapply UnOpS; eauto.
      * destruct H2 as (e' & h' & H2). eexists _, _.
        eapply (fill_contextual_step [UnOpCtx _]). done.
    + right. destruct (IH Hheap HeqΓ Heqn) as [H2 | H2].
      * eapply canonical_values_int in Hty as [z ->]; last done.
        eexists _, _; eapply base_contextual_step; eapply UnOpS; eauto.
      * destruct H2 as (e' & h' & H2). eexists _, _.
        eapply (fill_contextual_step [UnOpCtx _]). done.
  - (* pair *)
    destruct (IH2 Hheap HeqΓ Heqn) as [H2|H2]; [destruct (IH1 Hheap HeqΓ Heqn) as [H1|H1]|].
    + left. done.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as (e1' & h' & Hstep).
      eexists _, _. eapply (fill_contextual_step [PairLCtx v]). done.
    + right. destruct H2 as (e2' & h' & H2).
      eexists _, _. eapply (fill_contextual_step [PairRCtx e1]). done.
  - (* fst *)
    destruct (IH Hheap HeqΓ Heqn) as [H | H].
    + eapply canonical_values_prod in Hty as (e1 & e2 & -> & ? & ?); last done.
      right. eexists _, _. eapply base_contextual_step. econstructor; done.
    + right. destruct H as (e' & h' & H).
      eexists _, _. eapply (fill_contextual_step [FstCtx]). done.
  - (* snd *)
    destruct (IH Hheap HeqΓ Heqn) as [H | H].
    + eapply canonical_values_prod in Hty as (e1 & e2 & -> & ? & ?); last done.
      right. eexists _, _. eapply base_contextual_step. econstructor; done.
    + right. destruct H as (e' & h' & H).
      eexists _, _. eapply (fill_contextual_step [SndCtx]). done.
  - (* injl *)
    destruct (IH Hheap HeqΓ Heqn) as [H | H].
    + left. done.
    + right. destruct H as (e' & h' & H).
      eexists _, _. eapply (fill_contextual_step [InjLCtx]). done.
  - (* injr *)
    destruct (IH Hheap HeqΓ Heqn) as [H | H].
    + left. done.
    + right. destruct H as (e' & h' & H).
      eexists _, _. eapply (fill_contextual_step [InjRCtx]). done.
  - (* case *)
    right. destruct (IHe Hheap HeqΓ Heqn) as [H1|H1].
    + eapply canonical_values_sum in Htye as [(e' & -> & ?) | (e' & -> & ?)]; last done.
      * eexists _, _. eapply base_contextual_step. econstructor. done.
      * eexists _, _. eapply base_contextual_step. econstructor. done.
    + destruct H1 as (e' & h' & H1). eexists _, _.
      eapply (fill_contextual_step [CaseCtx e1 e2]). done.
  - (* roll *)
    destruct (IH Hheap HeqΓ Heqn) as [Hval|Hred].
    + by left.
    + right. destruct Hred as (e' & h' & Hred).
      eexists _, _. eapply (fill_contextual_step [RollCtx]). done.
  - (* unroll *)
    destruct (IH Hheap HeqΓ Heqn) as [Hval|Hred].
    + eapply canonical_values_rec in Hty as (e' & -> & Hval'); last done.
      right. eexists _, _. eapply base_contextual_step. by econstructor.
    + right. destruct Hred as (e' & h' & Hred).
      eexists _, _. eapply (fill_contextual_step [UnrollCtx]). done.
  - (* loc *)
    by left.
  - (* load *)
    destruct (IH Hheap HeqΓ Heqn) as [Hval|Hred].
    + eapply canonical_values_ref in Hty as (l & -> & Hlook); last done.
      eapply Hheap in Hlook as (v & Hlook & Hty').
      right. do 2 eexists. eapply base_contextual_step. by econstructor.
    + right. destruct Hred as (e' & h' & Hred).
      do 2 eexists. eapply (fill_contextual_step [LoadCtx]). done.
  - (* store *)
    destruct (IH2 Hheap HeqΓ Heqn) as [H2|H2]; [destruct (IH1 Hheap HeqΓ Heqn) as [H1|H1]|].
    + right. eapply canonical_values_ref in Hty1 as (l & -> & Hlook); last done.
      eapply Hheap in Hlook as (v & Hlook & Hty').
      eapply is_val_spec in H2 as (w & Heq).
      do 2 eexists. eapply base_contextual_step.
      econstructor; eauto.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as (e1' & h' & Hstep).
      do 2 eexists. eapply (fill_contextual_step [StoreLCtx v]). done.
    + right. destruct H2 as (e2' & h' & H2).
      do 2 eexists. eapply (fill_contextual_step [StoreRCtx e1]). done.
  - (* new *)
    destruct (IH Hheap HeqΓ Heqn) as [Hval|Hred].
    + right. eapply is_val_spec in Hval as [v Heq].
      do 2 eexists. eapply base_contextual_step.
      eapply (NewS _ _ _ (fresh (dom h))); last done.
      eapply not_elem_of_dom, is_fresh.
    + right. destruct Hred as (e' & h' & Hred).
      do 2 eexists. eapply (fill_contextual_step [NewCtx]). done.
Qed.

Definition ectx_item_typing Σ (K: ectx_item) (A B: type) :=
  ∀ e Σ', Σ ⊆ Σ' → TY Σ'; 0; ∅ ⊢ e : A → TY Σ'; 0; ∅ ⊢ (fill_item K e) : B.

Notation ectx := (list ectx_item).
Definition ectx_typing Σ (K: ectx) (A B: type) :=
  ∀ e Σ', Σ ⊆ Σ' → TY Σ'; 0; ∅ ⊢ e : A → TY Σ'; 0; ∅ ⊢ (fill K e) : B.

Lemma ectx_item_typing_weaking Σ Σ' k B A :
  Σ ⊆ Σ' → ectx_item_typing Σ k B A → ectx_item_typing Σ' k B A.
Proof.
  intros Hsub Hty e Σ'' Hsub'' Hty'. eapply Hty; last done.
  by transitivity Σ'.
Qed.

Lemma ectx_typing_weaking Σ Σ' K B A :
  Σ ⊆ Σ' → ectx_typing Σ K B A → ectx_typing Σ' K B A.
Proof.
  intros Hsub Hty e Σ'' Hsub'' Hty'. eapply Hty; last done.
  by transitivity Σ'.
Qed.

Lemma fill_item_typing_decompose Σ k e A:
  TY Σ; 0; ∅ ⊢ fill_item k e : A →
  ∃ B, TY Σ; 0; ∅ ⊢ e : B ∧ ectx_item_typing Σ k B A.
Proof.
  unfold ectx_item_typing; destruct k; simpl; inversion 1; subst; eauto 6 using typed_weakening, map_fmap_mono.
Qed.

Lemma fill_typing_decompose Σ K e A:
  TY Σ; 0; ∅ ⊢ fill K e : A →
  ∃ B, TY Σ; 0; ∅ ⊢ e : B ∧ ectx_typing Σ K B A.
Proof.
  unfold ectx_typing; revert e; induction K as [|k K]; intros e; simpl; eauto.
  intros [B [Hit Hty]] % IHK.
  eapply fill_item_typing_decompose in Hit as [B' [? ?]]; eauto.
Qed.

Lemma fill_typing_compose Σ K e A B:
  TY Σ; 0; ∅ ⊢ e : B →
  ectx_typing Σ K B A →
  TY Σ; 0; ∅ ⊢ fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.

Lemma fmap_up_subst_ctx σ Γ: ⤉(subst σ <$> Γ) = subst (up σ) <$> ⤉Γ.
Proof.
  rewrite -!map_fmap_compose.
  eapply map_fmap_ext. intros x A _. by asimpl.
Qed.

Lemma fmap_up_subst_heap_ctx σ Σ: ⤉(subst σ <$> Σ) = subst (up σ) <$> ⤉Σ.
Proof.
  rewrite -!map_fmap_compose.
  eapply map_fmap_ext. intros x A _. by asimpl.
Qed.

Lemma typed_subst_type Σ n m Γ e A σ:
  TY Σ; n; Γ ⊢ e : A → (∀ k, k < n → type_wf m (σ k)) → TY (subst σ) <$> Σ; m; (subst σ) <$> Γ ⊢ e : A.[σ].
Proof.
  induction 1 as [ Σ n Γ x A Heq | | | Σ n Γ e A Hty IH | | Σ n Γ A B e Hwf Hwf' Hty IH | Σ n Γ A B e e' x Hwf Hty1 IH1 Hty2 IH2 | | | | | |? ? ? ? ? ? ? ? ? Hop | ? ? ? ? ? ? ? Hop | | | | | | | |  | | | | ] in σ, m |-*; simpl; intros Hlt; eauto.
  - econstructor. rewrite lookup_fmap Heq //=.
  - econstructor; last by eapply type_wf_subst.
    rewrite -fmap_insert. eauto.
  - econstructor; last by eapply type_wf_subst. eauto.
  - econstructor. rewrite fmap_up_subst_ctx fmap_up_subst_heap_ctx. eapply IH.
    intros [| x] Hlt'; rewrite /up //=.
    + econstructor. lia.
    + eapply type_wf_rename; last by (intros ???; simpl; lia).
      eapply Hlt. lia.
  - replace (A.[B/].[σ]) with (A.[up σ].[B.[σ]/]) by by asimpl.
    eauto using type_wf_subst.
  - (* pack *)
    eapply (typed_pack _ _ _ _ (subst σ B)).
    + eapply type_wf_subst; done.
    + eapply type_wf_subst; first done.
      intros [ | k] Hk; first ( asimpl;constructor; lia).
      rewrite /up //=. eapply type_wf_rename; last by (intros ???; simpl; lia).
      eapply Hlt. lia.
    + replace (A.[up σ].[B.[σ]/]) with (A.[B/].[σ])  by by asimpl.
      eauto using type_wf_subst.
  - (* unpack *)
    eapply (typed_unpack _ _ _ A.[up σ]).
    + eapply type_wf_subst; done.
    + replace (∃: A.[up σ])%ty with ((∃: A).[σ])%ty by by asimpl.
      eapply IH1. done.
    + rewrite fmap_up_subst_ctx fmap_up_subst_heap_ctx. rewrite -fmap_insert.
      replace (B.[σ].[ren (+1)]) with (B.[ren(+1)].[up σ]) by by asimpl.
      eapply IH2.
      intros [ | k] Hk; asimpl; first (constructor; lia).
      eapply type_wf_subst; first (eapply Hlt; lia).
      intros k' Hk'. asimpl. constructor. lia.
  - (* binop *)
    inversion Hop; subst.
    all: econstructor; naive_solver.
  - (* unop *)
    inversion Hop; subst.
    all: econstructor; naive_solver.
  - econstructor; last naive_solver. by eapply type_wf_subst.
  - econstructor; last naive_solver. by eapply type_wf_subst.
  - (* roll *)
    econstructor.
    replace (A.[up σ].[μ: A.[up σ]/])%ty with (A.[μ: A/].[σ])%ty by by asimpl. eauto.
  - (* unroll *)
    replace (A.[μ: A/].[σ])%ty with (A.[up σ].[μ: A.[up σ]/])%ty by by asimpl.
    econstructor. eapply IHsyn_typed. done.
  - (* loc *)
    econstructor. rewrite lookup_fmap H //=.
Qed.

Lemma typed_subst_type_closed Σ C e A:
  type_wf 0 C →
  heap_ctx_wf 0 Σ →
  TY ⤉Σ; 1; ⤉∅ ⊢ e : A → TY Σ; 0; ∅ ⊢ e : A.[C/].
Proof.
  intros Hwf Hwf' Hty. eapply typed_subst_type with (σ := C .: ids) (m := 0) in Hty; last first.
  { intros [|k] Hlt; last lia. done. }
  revert Hty. rewrite !fmap_empty.
  rewrite !(heap_ctx_closed Σ); eauto.
Qed.

Lemma typed_subst_type_closed' Σ x C B e A:
  type_wf 0 A →
  type_wf 1 C →
  type_wf 0 B →
  heap_ctx_wf 0 Σ →
  TY ⤉Σ; 1; <[x := C]> ∅ ⊢ e : A →
  TY Σ; 0; <[x := C.[B/]]> ∅ ⊢ e : A.
Proof.
  intros ???? Hty.
  set (s := (subst (B.:ids))).
  rewrite -(fmap_empty s) -(fmap_insert s).
  replace A with (A.[B/]).
  2: { replace A with (A.[ids]) at 2 by by asimpl.
      eapply type_wf_subst_dom; first done. lia.
  }
  rewrite -(heap_ctx_closed Σ (B.:ids)); last done.
  eapply typed_subst_type.
  { rewrite -(heap_ctx_closed Σ (ren (+1))); done. }
  intros [ | k] Hk; last lia. done.
Qed.

Lemma heap_ctx_insert h l A Σ:
  heap_type h Σ → h !! l = None → Σ ⊆ <[l:=A]> Σ.
Proof.
  intros Hheap Hlook. eapply insert_subseteq.
  specialize (Hheap l). destruct (lookup) as [B|]; last done.
  specialize (Hheap B eq_refl) as (w & Hsome & _). congruence.
Qed.

Lemma heap_type_insert h Σ e v l B :
  heap_type h Σ →
  h !! l = None →
  TY Σ; 0; ∅ ⊢ e : B →
  to_val e = Some v →
  heap_type ({[l := v]} ∪ h) (<[l:=B]> Σ).
Proof.
  intros Hheap Hlook Hty Hval l' A. rewrite lookup_insert_Some.
  intros [(-> & ->)|(Hne & Hlook')].
  - exists v. split; first eapply lookup_union_Some_l, lookup_insert.
    eapply of_to_val in Hval as ->.
    eapply typed_weakening; first eapply Hty; eauto.
    by eapply heap_ctx_insert.
  - eapply Hheap in Hlook' as (w & Hlook' & Hty').
    eexists; split.
    + rewrite lookup_union_r; eauto.
      rewrite lookup_insert_ne //=.
    + eapply typed_weakening; first eapply Hty'; eauto.
      by eapply heap_ctx_insert.
Qed.

Lemma heap_type_update h Σ e v l B :
  heap_type h Σ →
  Σ !! l = Some B →
  TY Σ; 0; ∅ ⊢ e : B →
  to_val e = Some v →
  heap_type (<[l:=v]> h) Σ.
Proof.
  intros Hheap Hlook Hty Hval l' A Hlook'.
  eapply Hheap in Hlook' as Hlook''.
  destruct Hlook'' as (w & Hold & Hval').
  destruct (decide (l = l')); subst.
  - exists v. split; first eapply lookup_insert.
    eapply of_to_val in Hval as ->.
    rewrite Hlook in Hlook'. by injection Hlook' as ->.
  - rewrite lookup_insert_ne //=. eauto.
Qed.



Lemma typed_preservation_base_step Σ e e' h h' A:
  heap_ctx_wf 0 Σ →
  TY Σ; 0; ∅ ⊢ e : A →
  heap_type h Σ →
  base_step (e, h) (e', h') →
  ∃ Σ', Σ ⊆ Σ' ∧ heap_type h' Σ' ∧ heap_ctx_wf 0 Σ' ∧ TY Σ'; 0; ∅ ⊢ e' : A.
Proof.
  intros Hwf' Hty Hhty Hstep. inversion Hstep as [ | | | op e1 v v' h1 Heq Heval | op e1 v1 e2 v2 v3 h1 Heq1 Heq2 Heval | | |  | | | | | | | ]; subst.
  - eapply app_inversion in Hty as (B & H1 & H2).
    destruct x as [|x].
    { eapply lam_anon_inversion in H1 as (C & D & [= -> ->] & Hwf & Hty).
      exists Σ. do 3 (split; first done). done. }
    eapply lam_inversion in H1 as (C & D & Heq & Hwf & Hty).
    injection Heq as -> ->.
    exists Σ. do 3 (split; first done).
    eapply typed_substitutivity; eauto.
  - eapply type_app_inversion in Hty as (B & C & -> & Hwf & Hty).
    eapply type_lam_inversion in Hty as (A & Heq & Hty).
    injection Heq as ->. exists Σ. split_and!; [done.. | ]. by eapply typed_subst_type_closed.
  - eapply type_unpack_inversion in Hty as (B & x' & -> & Hwf & Hty1 & Hty2).
    eapply type_pack_inversion in Hty1 as (B' & C & [= <-] & Hty1 & ? & ?).
    exists Σ. split_and!; [done.. | ].
    eapply typed_substitutivity.
    { done. }
    { apply Hty1. }
    rewrite fmap_empty in Hty2.
    eapply typed_subst_type_closed'; eauto.
    replace A with A.[ids] by by asimpl.
    enough (A.[ids] = A.[ren (+1)]) as -> by done.
    eapply type_wf_subst_dom; first done. intros; lia.
  - (* unop *)
    eapply unop_inversion in Hty as (A1 & Hop & Hty).
    assert ((A1 = Int ∧ A = Int) ∨ (A1 = Bool ∧ A = Bool)) as [(-> & ->) | (-> & ->)].
    { inversion Hop; subst; eauto. }
    + eapply canonical_values_int in Hty as [n ->]; last by eapply is_val_spec; eauto.
      simpl in Heq. injection Heq as <-.
      exists Σ; split_and!; [done..|].
      inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
    + eapply canonical_values_bool in Hty as [b ->]; last by eapply is_val_spec; eauto.
      simpl in Heq. injection Heq as <-.
      exists Σ; split_and!; [done..|].
      inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
  - (* binop *)
    eapply binop_inversion in Hty as (A1 & A2 & Hop & Hty1 & Hty2).
    assert (A1 = Int ∧ A2 = Int ∧ (A = Int ∨ A = Bool)) as (-> & -> & HC).
    { inversion Hop; subst; eauto. }
    eapply canonical_values_int in Hty1 as [n ->]; last by eapply is_val_spec; eauto.
    eapply canonical_values_int in Hty2 as [m ->]; last by eapply is_val_spec; eauto.
    simpl in Heq1, Heq2. injection Heq1 as <-. injection Heq2 as <-.
    simpl in Heval.
    exists Σ; split_and!; [done..|].
    inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
  - exists Σ; split_and!; [done..|].
    by eapply if_inversion in Hty as (H1 & H2 & H3).
  - exists Σ; split_and!; [done..|].
    by eapply if_inversion in Hty as (H1 & H2 & H3).
  - exists Σ; split_and!; [done..|].
    by eapply fst_inversion in Hty as (B & (? & ? & [= <- <-] & ? & ?)%pair_inversion).
  - exists Σ; split_and!; [done..|].
    by eapply snd_inversion in Hty as (B & (? & ? & [= <- <-] & ? & ?)%pair_inversion).
  - exists Σ; split_and!; [done..|].
    eapply case_inversion in Hty as (B & C & (? & ? & [= <- <-] & Hty & ?)%injl_inversion & ? & ?).
    eauto.
  - exists Σ; split_and!; [done..|].
    eapply case_inversion in Hty as (B & C & (? & ? & [= <- <-] & Hty & ?)%injr_inversion & ? & ?).
    eauto.
  - (* unroll *)
    exists Σ; split_and!; [done..|].
    eapply unroll_inversion in Hty as (B & -> & Hty).
    eapply roll_inversion in Hty as (C & Heq & Hty). injection Heq as ->. done.
  - (* new *)
    (* FIXME: exercise *)
    admit.
  - (* load *)
    (* FIXME exercise *)
    admit.
  - (* store *)
    (* FIXME exercise *)
    admit.
(*Qed.*)
Admitted.

Lemma typed_preservation Σ e e' h h' A:
  heap_ctx_wf 0 Σ →
  TY Σ; 0; ∅ ⊢ e : A →
  heap_type h Σ →
  contextual_step (e, h) (e', h') →
  ∃ Σ', Σ ⊆ Σ' ∧ heap_type h' Σ' ∧ heap_ctx_wf 0 Σ' ∧ TY Σ'; 0; ∅ ⊢ e' : A.
Proof.
  intros Hwf Hty Hheap Hstep. inversion Hstep as [K e1' e2' σ1 σ2 e1 e2 -> -> Hstep']; subst.
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply typed_preservation_base_step in H1 as (Σ' & Hsub & Hheap' & Hwf' & Hty'); eauto.
  eexists; repeat split; try done.
  eapply fill_typing_compose, ectx_typing_weaking; eauto.
Qed.

Lemma typed_preservation_steps Σ e e' h h' A:
  heap_ctx_wf 0 Σ →
  TY Σ; 0; ∅ ⊢ e : A →
  heap_type h Σ →
  rtc contextual_step (e, h) (e', h') →
  ∃ Σ', Σ ⊆ Σ' ∧ heap_type h' Σ' ∧ heap_ctx_wf 0 Σ' ∧ TY Σ'; 0; ∅ ⊢ e' : A.
Proof.
  intros Hwf Hty Hheap Hsteps. remember (e, h) as c1. remember (e', h') as c2.
  induction Hsteps as [|? [] ? Hstep Hsteps IH] in Σ, h, h',e, e', Heqc1, Heqc2, Hwf, Hty, Hheap |-*.
  - rewrite Heqc1 in Heqc2. injection Heqc2 as -> ->. eauto.
  - subst; eapply typed_preservation in Hty as (Σ' & Hsub' & Hheap' & Hwf' & Hty'); [|eauto..].
    eapply IH in Hty' as (Σ'' & Hsub'' & Hheap'' & Hwf'' & Hty''); [|eauto..].
    exists Σ''; repeat split; eauto. by trans Σ'.
Qed.

Lemma type_safety Σ e1 e2 h1 h2 A:
  heap_ctx_wf 0 Σ →
  TY Σ; 0; ∅ ⊢ e1 : A →
  heap_type h1 Σ →
  rtc contextual_step (e1, h1) (e2, h2) →
  is_val e2 ∨ reducible e2 h2.
Proof.
  intros Hwf Hy Hheap Hsteps.
  eapply typed_preservation_steps in Hsteps as (Σ' & Hsub & Hheap' & Hwf' & Hty'); eauto.
  eapply typed_progress; eauto.
Qed.

(* applies to terms containing no free locations (like the erasure of source terms) *)
Corollary closed_type_safety e e' h A:
  TY ∅; 0; ∅ ⊢ e : A →
  rtc contextual_step (e, ∅) (e', h) →
  is_val e' ∨ reducible e' h.
Proof.
  intros Hty Hsteps. eapply type_safety; eauto.
  intros ??. set_solver.
Qed.

(** Derived typing rules *)
Lemma typed_unroll' Σ n Γ e A B:
  TY Σ; n; Γ ⊢ e : (μ: A) →
  B = A.[(μ: A)%ty/] →
  TY Σ; n; Γ ⊢ (unroll e) : B.
Proof.
  intros ? ->. by eapply typed_unroll.
Qed.

Lemma typed_tapp' Σ n Γ A B C e :
  TY Σ; n; Γ ⊢ e : (∀: A) →
  type_wf n B →
  C = A.[B/] →
  TY Σ; n; Γ ⊢ e <> : C.
Proof.
 intros; subst C; by eapply typed_tapp.
Qed.
