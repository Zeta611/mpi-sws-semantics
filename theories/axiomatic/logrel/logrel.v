From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.heap_lang Require Import metatheory.
From semantics.axiomatic Require Export invariant_lib.
From semantics.axiomatic.logrel Require Import notation persistent_pred.
From semantics.axiomatic.logrel Require Import syntactic.
From semantics.axiomatic.heap_lang Require Export primitive_laws proofmode.
From iris.prelude Require Import options.


(** * Logical relation for SystemF + Mu + State in Iris *)

Implicit Types
  (Γ : gmap string type)
  (γ : gmap string val)
  (A B : type)
.

Section logrel.
(** With the [heapGS Σ] assumption, we require the Iris mechanisms for manipulating the heap to be available.
  (In the previous developments, we assumed this as a global axiom for ease of presentation, but obviously, one should not do that :))

  Below, you will frequently see [iProp Σ], instead of plain [iProp]. This indicates Iris's parameterization over [Σ].
  You will see more on what this means in the coming weeks.
 *)
Context `{heapGS Σ}.

Implicit Types
  (P Q : iProp Σ)
  (v w : val)
  (e : expr).

(** ** Defining the semantic types *)
(** Semantic types are, essentially, persistent predicates [val → iProp] *)
Definition semtype := persistent_pred val (iPropI Σ).
Definition semtypeO := persistent_predO val (iPropI Σ).
(** Smart constructor for semantic types *)
Definition mk_semtype (pred : val → iProp Σ) {Pers : ∀ v, Persistent (pred v)} : semtype :=
  @PersPred _ _ pred Pers.
Global Instance semtype_pers (τ : semtypeO) : ∀ v, Persistent (τ v) := _.

(** Type variable environments are represented in De Bruijn style *)
(** You will, as seen previously, see function arrows [-n>], lambdas [λne], and liftings of types (like [natO]) below.
  This is to account for Iris's algebraic structure to internalize step-indexing.
  You will learn more about this in a few weeks, but can for now ignore it: the pattern of where it is needed is very systematic.

  The same also holds true for the [Nonexpansive] and [Proper] obligations in the definitions below: you can ignore them for now, [solve_proper] will deal with them.
  (Essentially, they say that the definitions don't mess with the step-index in the wrong way.)
 *)
Definition envO := natO -n> semtypeO.

Implicit Types
  (τ : semtype)
  (σ : envO -n> semtypeO).

(** [consCtx] lift's Autosubst's [.:] cons operation to OFEs, to make it compatible with Iris. *)
Program Definition consCtx : semtypeO -n> envO -n> envO :=
  λne τ δ, OfeMor (τ .: δ).
Next Obligation.
  intros. intros ???.
  intros []; simpl; solve_proper.
Qed.
Next Obligation.
  intros ? ??? ?[]?; simpl; solve_proper.
Qed.
(** We make [consCtx] opaque so that it is not inadequately reduced. Instead, use the unfolding equation [consCtx_unfold]. *)
Lemma consCtx_unfold τ δ :
  consCtx τ δ = OfeMor (τ .: δ).
Proof. done. Qed.
Opaque consCtx.
Notation "τ '.::' δ" := (consCtx τ δ) (at level 30).

Section defs.
(** The expression relation *)
Program Definition expr_interp : semtypeO -n> exprO -n> iPropO Σ :=
  λne τ e, (WP e {{ v, τ v }})%I.
Solve Obligations with solve_proper.

Definition int_interp : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, (∃ n : Z, ⌜v = #n⌝))%I.
Definition bool_interp : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, (∃ b : bool, ⌜v = #b⌝))%I.
Definition unit_interp : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, ⌜v = #()⌝)%I.

Program Definition fun_interp (σ1 : envO -n> semtypeO) (σ2 : envO -n> semtypeO) : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, (∀ w, □ (σ1 δ w -∗ expr_interp (σ2 δ) (v w))))%I.
Solve Obligations with solve_proper.

(** Type variables *)
Program Definition var_interp (x : var) : envO -n> semtypeO :=
  λne δ, δ x.
Solve Obligations with solve_proper.

Program Definition all_interp σ : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, □ (∀ τ, expr_interp (σ (τ .:: δ)) (TApp v)))%I.
Solve Obligations with solve_proper.

Program Definition exist_interp σ : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, ∃ w, ⌜v = PackV w⌝ ∗ ∃ τ, (σ (τ .:: δ)) w)%I.
Solve Obligations with solve_proper.

(** Recursive types are defined via Iris's fixpoint mechanism *)
Program Definition mu_rec σ δ (rec : semtypeO) : semtypeO :=
  mk_semtype (λ v, (∃ w, ⌜v = RollV w⌝ ∗ ▷ (σ (rec .:: δ)) w)%I).
Instance mu_rec_contractive σ δ : Contractive (mu_rec σ δ).
Proof. solve_contractive. Qed.
Program Definition mu_interp σ : envO -n> semtypeO :=
  λne δ, fixpoint (mu_rec σ δ).
Next Obligation. intros ?? ???. apply fixpoint_ne. solve_proper. Qed.

(** The unfolding equation for recursive types *)
Lemma mu_interp_unfold σ δ v :
  mu_interp σ δ v ⊣⊢ mu_rec σ δ (mu_interp σ δ) v.
Proof. f_equiv. apply fixpoint_unfold. Qed.

(** References and their invariant *)
Definition logN : namespace := nroot .@ "logrel".
Program Definition ref_inv (l : loc) : semtypeO -n> iPropO Σ :=
  λne τ, (∃ w, l ↦ w ∗ τ w)%I.
Solve Obligations with solve_proper.
Program Definition ref_interp σ : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, ∃ l : loc, ⌜v = #l⌝ ∗ inv (logN) (ref_inv l (σ δ)))%I.
Solve Obligations with solve_proper.

Program Definition prod_interp σ1 σ2 : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, ∃ w1 w2, ⌜v = (w1, w2)%V⌝ ∗ σ1 δ w1 ∗ σ2 δ w2)%I.
Solve Obligations with solve_proper.

Program Definition sum_interp σ1 σ2 : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v, (∃ w, ⌜v = InjLV w⌝ ∗ σ1 δ w) ∨ (∃ w, ⌜v = InjRV w⌝ ∗ σ2 δ w))%I.
Solve Obligations with solve_proper.

(** The interpretation into semantic types. This also serves as the value relation. *)
Fixpoint type_interp (A : type) : envO -n> semtypeO :=
  match A with
  | TVar x => var_interp x
  | TUnit => unit_interp
  | TInt => int_interp
  | TBool => bool_interp
  | TFun A B => fun_interp (type_interp A) (type_interp B)
  | TForall A => all_interp (type_interp A)
  | TExists A => exist_interp (type_interp A)
  | TMu A => mu_interp (type_interp A)
  | TRef A => ref_interp (type_interp A)
  | TProd A B => prod_interp (type_interp A) (type_interp B)
  | TSum A B => sum_interp (type_interp A) (type_interp B)
  end.
Notation 𝒱 := type_interp.

(** The context relation *)
Program Definition context_interp Γ γ : envO -n> iPropO Σ :=
  λne δ, ([∗ map] x ↦ A; v ∈ Γ; γ, 𝒱 A δ v)%I.
Next Obligation.
  solve_proper.
Qed.
Global Instance context_interp_pers Γ γ δ : Persistent (context_interp Γ γ δ).
Proof. apply _. Qed.
Notation 𝒢 := context_interp.

Lemma context_interp_dom_eq Γ γ δ :
  context_interp Γ γ δ -∗ ⌜dom Γ = dom γ⌝.
Proof. iApply big_sepM2_dom. Qed.

Lemma context_interp_empty δ :
  ⊢ 𝒢 ∅ ∅ δ.
Proof.
  by iApply big_sepM2_empty.
Qed.

Lemma context_interp_insert Γ γ δ A v x :
  𝒱 A δ v -∗
  𝒢 Γ γ δ -∗
  𝒢 (<[x := A]> Γ) (<[x := v]> γ) δ.
Proof.
  iIntros "Hv Hγ". iApply (big_sepM2_insert_2 with "[Hv] [Hγ]"); done.
Qed.

Lemma context_interp_lookup Γ γ δ A x :
  ⌜Γ !! x = Some A⌝ -∗
  𝒢 Γ γ δ -∗
  ∃ v, ⌜γ !! x = Some v⌝ ∧ 𝒱 A δ v.
Proof.
  iIntros (Hlook) "Hγ".
  iPoseProof (big_sepM2_lookup_l with "Hγ") as "Ha"; done.
Qed.
End defs.

Notation 𝒱 := type_interp.
Notation 𝒢 := context_interp.
Notation ℰ := expr_interp.

Implicit Types
  (*(x : string)*)
  (δ : envO)
.

Section boring_lemmas.
  (* ad-hoc tactic to solve the trivial cases *)
  Ltac try_solve_eq :=
  match goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- mk_semtype _ ≡ mk_semtype _ => intros ?; simpl
  | |- ofe_mor_car _ _ (ofe_mor_car _ _ consCtx _) _ ≡ _ => rewrite !consCtx_unfold; intros []; try done
  | |- _ =>
      match goal with
      (* don't [f_equiv] when we should apply the IH *)
      | |- ofe_mor_car _ _ (type_interp _) _ ≡ ofe_mor_car _ _ (type_interp _) _ => idtac
      | |- _ => f_equiv
      end
  end.

  Lemma type_interp_ext B δ δ' :
    (∀ n, δ n ≡ δ' n) →
    𝒱 B δ ≡ 𝒱 B δ'.
  Proof.
    intros Hd. induction B; intros ?; simpl; f_equiv; eauto; try apply fixpoint_proper; solve_proper.
  Qed.

  Lemma type_interp_move_ren B δ s :
    𝒱 B (λne n, δ (s n)) ≡ 𝒱 (rename s B) δ.
  Proof.
    induction B in δ, s |-*; intros ?; simpl; eauto; repeat try_solve_eq; try done.
    - (* universal *) rewrite -IHB; f_equiv. repeat try_solve_eq.
    - (* existential *) rewrite -IHB; f_equiv. repeat try_solve_eq.
    - (* recursive *) unfold mu_interp. apply fixpoint_proper. unfold mu_rec.
      intros ?. repeat try_solve_eq. rewrite -IHB.
      f_equiv. rewrite !consCtx_unfold; intros []; done.
  Qed.

  Lemma type_interp_move_subst B δ s :
    𝒱 B (λne n, 𝒱 (s n) δ) ≡ 𝒱 (B.[s]) δ.
  Proof.
    induction B in s, δ |-*; simpl; eauto; repeat try_solve_eq; try done.
    - (* universal *)
      etransitivity; last apply IHB.
      apply type_interp_ext.
      intros []; rewrite !consCtx_unfold; simpl; first done.
      unfold up; simpl. etransitivity; last apply type_interp_move_ren.
      simpl. f_equiv. done.
    - (* existential *)
      etransitivity; last apply IHB.
      apply type_interp_ext. intros []; rewrite !consCtx_unfold; simpl; first done.
      unfold up; simpl. etransitivity; last apply type_interp_move_ren.
      simpl. f_equiv. done.
    - (* recursive *)
      apply fixpoint_proper; intros ?; unfold mu_rec. repeat try_solve_eq.
      rewrite -IHB. f_equiv.
      rewrite !consCtx_unfold. intros []; simpl; first done.
      replace (up s (S n)) with (rename (+1) (s n)) by by asimpl.
      rewrite -type_interp_move_ren. f_equiv. simpl. intros ?; done.
  Qed.

  Lemma type_interp_move_single_subst A B δ v :
    𝒱 B ((𝒱 A δ) .:: δ) v ⊣⊢ 𝒱 (B.[A/]) δ v.
  Proof.
    f_equiv. etransitivity; last apply type_interp_move_subst.
    apply type_interp_ext. intros []; rewrite consCtx_unfold; simpl; done.
  Qed.

  Lemma expr_interp_move_single_subst A B δ e :
    ℰ (𝒱 B ((𝒱 A δ) .:: δ)) e ⊣⊢ ℰ (𝒱 (B.[A/]) δ) e.
  Proof.
    f_equiv. f_equiv. intros ?. apply type_interp_move_single_subst.
  Qed.

  Lemma type_interp_cons A δ v τ :
    𝒱 A δ v ⊣⊢ 𝒱 A.[ren (+1)] (τ .:: δ) v.
  Proof.
    f_equiv. etransitivity; last apply type_interp_move_subst.
    apply type_interp_ext. intros []; rewrite consCtx_unfold; simpl; done.
  Qed.

  Lemma expr_interp_cons A δ e τ :
    ℰ (𝒱 A δ) e ⊣⊢ ℰ (𝒱 A.[ren (+1)] (τ .:: δ))e.
  Proof.
    f_equiv. f_equiv. intros ?. apply type_interp_cons.
  Qed.

  Lemma context_interp_cons Γ γ δ τ :
    𝒢 Γ γ δ -∗
    𝒢 (⤉ Γ) γ (τ .:: δ) .
  Proof.
    iIntros "Hctx".
    iApply big_sepM2_fmap_l.
    iApply (big_sepM2_mono with "Hctx").
    iIntros (k A v HA Hv) "Hv". by rewrite type_interp_cons.
  Qed.
End boring_lemmas.

Definition sem_typed (n : nat) Γ e A : Prop :=
  ⊢ ∀ δ γ, 𝒢 Γ γ δ -∗ ℰ (𝒱 A δ) (subst_map γ e).
Notation "'TY' Δ ;  Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).

Opaque context_interp.

(** ** Compatibility lemmas *)
Notation sub := heap_lang.subst.

(* The following tactic will be useful for applying bind:
  [smart_wp_bind e v "Hv" He]
  will bind the subexpression [e],
  apply the semantic typing assumption [He] for it,
  and then introduce the resulting value [v] and interpretation ["Hv"] for [v].
 *)
Local Tactic Notation "smart_wp_bind"
    uconstr(e) ident(v) constr(Hv) uconstr(Hp) :=
  wp_bind e;
  iApply (wp_wand); [iApply Hp; trivial|];
  simpl; iIntros (v) Hv.

Lemma compat_var Δ Γ (x : string) A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ x : A.
Proof.
  iIntros (Hlook δ γ) "#Hctx/=".
  iPoseProof (context_interp_lookup with "[//] Hctx") as "(%v & -> & Hv)".
  by iApply wp_value.
Qed.

Lemma compat_int Δ Γ (z : Z) :
  TY Δ; Γ ⊨ #z : TInt.
Proof.
  iIntros (δ γ) "Hctx /=".
  iApply wp_value. eauto.
Qed.

Lemma compat_bool Δ Γ (b : bool) :
  TY Δ; Γ ⊨ #b : TBool.
Proof.
  iIntros (δ γ) "Hctx/=".
  iApply wp_value. eauto.
Qed.

Lemma compat_unit Δ Γ :
  TY Δ; Γ ⊨ #() : TUnit.
Proof.
  iIntros (δ γ) "Hctx /=".
  iApply wp_value. eauto.
Qed.

Lemma compat_beta Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : (A → B) →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (e1 e2) : B.
Proof.
  iIntros (He1 He2 δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v2 "Hv2" He2.
  (* more explicit alternative: *)
  (*wp_bind (subst_map _ e2).*)
  (*iApply wp_wand. { by iApply He2. }*)
  (*iIntros (v2) "Hv2".*)
  smart_wp_bind (subst_map _ _) v1 "Hv1" He1.
  iApply ("Hv1" with "Hv2").
Qed.

Lemma compat_lambda Δ Γ (x : string) e A B :
  TY Δ; (<[x := A]> Γ) ⊨ e : B →
  TY Δ; Γ ⊨ (λ: x, e) : (A → B).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  wp_pures. iApply wp_value. iIntros (w) "!> Hw".
  wp_pures.
  iPoseProof (He $! δ (<[x := w]> γ) with "[Hw]") as "He".
  { iApply (context_interp_insert with "Hw Hctx"). }
  simpl. rewrite -subst_map_insert.
  iApply "He".
Qed.

Lemma compat_lambda_anon Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  wp_pures. iApply wp_value. iIntros (w) "!> Hw".
  wp_pures. iApply (He with "Hctx").
Qed.

Lemma compat_rec Δ Γ (f x : string) e A B :
  x ≠ f →
  TY Δ; (<[x := A]> (<[f := (A → B)%ty]> Γ)) ⊨ e : B →
  TY Δ; Γ ⊨ (rec: f x := e) : (A → B).
Proof.
  iIntros (? He δ γ) "#Hctx/=".
  wp_pures. iApply wp_value. iIntros (w) "!> Hw".
  set (r := (RecV _ _ _)). iLöb as "IH" forall (w).
  unfold r. wp_pures.
  rewrite subst_subst_ne; last done.
  rewrite -subst_map_insert.
  rewrite -delete_insert_ne; last done.
  rewrite -subst_map_insert.
  iApply He.
  rewrite insert_commute; last done.
  iApply context_interp_insert.
  { simpl. iIntros (w') "!>". by iApply "IH". }
  by iApply (context_interp_insert with "Hw").
Qed.

Lemma compat_binop Δ Γ e1 e2 A1 A2 B op :
  bin_op_typed op A1 A2 B →
  TY Δ; Γ ⊨ e1 : A1 →
  TY Δ; Γ ⊨ e2 : A2 →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : B.
Proof.
  iIntros (Hop He1 He2 δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v2 "Hv2" He2.
  smart_wp_bind (subst_map _ _) v1 "Hv1" He1.
  inversion Hop; iDestruct "Hv1" as "(% & ->)"; iDestruct "Hv2" as "(% & ->)";
    wp_pures; iApply wp_value; eauto with iFrame.
Qed.

Lemma compat_unop Δ Γ e A B op :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ (UnOp op e) : B.
Proof.
  iIntros (Hop He δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v "Hv" He.
  inversion Hop; iDestruct "Hv" as "(% & ->)";
    wp_pures; iApply wp_value; eauto with iFrame.
Qed.

Lemma compat_tlam Δ Γ e A :
  TY S Δ; (⤉ Γ) ⊨ e : A →
  TY Δ; Γ ⊨ (Λ, e) : (∀: A).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  wp_pures. iApply wp_value. iIntros "!>" (τ).
  wp_pures. iApply wp_wand.
  { iApply He. by iApply context_interp_cons. }
  eauto.
Qed.

Lemma compat_tapp Δ Γ e A B :
  TY Δ; Γ ⊨ e : (∀: A) →
  TY Δ; Γ ⊨ (TApp e) : (A.[B/]).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v "Hv" He.
  iSpecialize ("Hv" $! (type_interp B δ)).
  iApply (wp_wand with "Hv").
  iIntros (v'). rewrite -type_interp_move_single_subst.
  eauto.
Qed.

Lemma compat_pack Δ Γ e A B :
  TY Δ; Γ ⊨ e : A.[B/] →
  TY Δ; Γ ⊨ (Pack e) : (∃: A).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  smart_wp_bind _ v "Hv" He.
  iExists v. iSplitR; first done.
  iExists (type_interp B δ).
  rewrite type_interp_move_single_subst. done.
Qed.

Lemma compat_unpack Δ Γ A B e e' x :
  TY Δ; Γ ⊨ e : (∃: A) →
  TY S Δ; <[x:=A]> (⤉Γ) ⊨ e' : B.[ren (+1)] →
  TY Δ; Γ ⊨ (unpack e as BNamed x in e') : B.
Proof.
  iIntros (He He' δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v "Hv" He.
  iDestruct "Hv" as "(%w & -> & %τ & Hw)".
  wp_pures. rewrite -subst_map_insert.
  iApply (wp_wand with "[Hw]").
  { iApply He'. iApply (context_interp_insert with "Hw").
    by iApply context_interp_cons.
  }
  iIntros (v) "Hv". by iApply type_interp_cons.
Qed.

Lemma compat_if Δ Γ e0 e1 e2 A :
  TY Δ; Γ ⊨ e0 : TBool →
  TY Δ; Γ ⊨ e1 : A →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (if: e0 then e1 else e2) : A.
Proof.
  iIntros (He0 He1 He2 δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v0 "(%b & ->)" He0.
  destruct b; wp_pures.
  - by iApply He1.
  - by iApply He2.
Qed.

Lemma compat_pair Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : A →
  TY Δ; Γ ⊨ e2 : B →
  TY Δ; Γ ⊨ (e1, e2) : A × B.
Proof.
  (* FIXME exercise *)
(*Qed.*)
Admitted.

Lemma compat_fst Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Fst e : A.
Proof.
  (* FIXME exercise *)
(*Qed.*)
Admitted.

Lemma compat_snd Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Snd e : B.
Proof.
  (* FIXME exercise *)
(*Qed.*)
Admitted.

Lemma compat_injl Δ Γ e A B :
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ InjL e : A + B.
Proof.
  (* FIXME exercise *)
(*Qed.*)
Admitted.

Lemma compat_injr Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ InjR e : A + B.
Proof.
  (* FIXME exercise *)
(*Qed.*)
Admitted.

Lemma compat_case Δ Γ e e1 e2 A B C :
  TY Δ; Γ ⊨ e : B + C →
  TY Δ; Γ ⊨ e1 : (B → A) →
  TY Δ; Γ ⊨ e2 : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 : A.
Proof.
  (* FIXME exercise *)
(*Qed.*)
Admitted.

Lemma compat_roll Δ Γ e A :
  TY Δ; Γ ⊨ e : (A.[(μ: A)%ty/]) →
  TY Δ; Γ ⊨ (roll e) : (μ: A).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  smart_wp_bind _ v "#Hv" He.
  rewrite mu_interp_unfold /mu_rec /=.
  iExists v. iSplitR; first done.
  iNext. by rewrite -type_interp_move_single_subst.
Qed.

Lemma compat_unroll Δ Γ e A :
  TY Δ; Γ ⊨ e : (μ: A) →
  TY Δ; Γ ⊨ (unroll e) : (A.[(μ: A)%ty/]).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  rewrite lookup_delete.
  smart_wp_bind (subst_map _ _) v "Hv" He.
  simpl. rewrite mu_interp_unfold /mu_rec /=.
  iDestruct "Hv" as "(%w & -> & Hv)".
  (* crucial: we take a step to strip the later *)
  wp_pures. iApply wp_value.
  by rewrite -type_interp_move_single_subst.
Qed.

Lemma compat_new Δ Γ e A :
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ ref e : (TRef A).
Proof.
  iIntros (He δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v "Hv" He.
  wp_alloc l as "Hl".
  iApply (inv_alloc (logN) (ref_inv l (𝒱 A δ)) with "[Hl Hv]").
  { simpl. eauto with iFrame. }
  iIntros "#Hinv". iApply wp_value.
  eauto with iFrame.
Qed.

Lemma compat_load Δ Γ e A :
  TY Δ; Γ ⊨ e : TRef A →
  TY Δ; Γ ⊨ !e : A.
Proof.
  iIntros (He δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v "Hv" He.
  iDestruct "Hv" as "(%l & -> & Hinv)".
  iApply (inv_open with "Hinv"); first solve_ndisj.
  iIntros "(%w & >Hl & #Hv)".
  wp_load. iApply wp_value. eauto with iFrame.
Qed.

Lemma compat_store Δ Γ e1 e2 A :
  TY Δ; Γ ⊨ e1 : TRef A →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (e1 <- e2) : TUnit.
Proof.
  iIntros (He1 He2 δ γ) "#Hctx/=".
  smart_wp_bind (subst_map _ _) v2 "Hv2" He2.
  smart_wp_bind (subst_map _ _) v1 "Hv1" He1.
  iDestruct "Hv1" as "(%l & -> & Hinv)".
  iApply (inv_open with "Hinv"); first solve_ndisj.
  iIntros "(%w & >Hl & Hv1)".
  wp_store. iApply wp_value. eauto with iFrame.
Qed.

Local Hint Resolve compat_var compat_lambda compat_lambda_anon compat_tlam compat_int compat_bool compat_unit compat_if compat_beta compat_tapp compat_pack compat_unpack compat_binop compat_unop compat_pair compat_fst compat_snd compat_injl compat_injr compat_case compat_roll compat_unroll compat_new compat_store compat_load: core.

Lemma fundamental Δ Γ e A :
  (syn_typed Δ Γ e A) →
  (TY Δ; Γ ⊨ e : A).
Proof.
  induction 1 as [ | | | | | | | | | | | ? ? ? ? ? ? ? IH1 ? IH2 | | | | | | | | ? ? ?? ??????IH0 ? IH1 ? IH2  | | | | ?????? IH1 ? IH2| ].
  (* for some reason, [eauto] is exceedingly slow on some of these cases... *)
  1-11: eauto.
  { eapply compat_beta; [apply IH1 | apply IH2]. }
  1-7: eauto.
  { eapply compat_case; [apply IH0 | apply IH1 | apply IH2]. }
  1-3: eauto.
  { eapply compat_store; [apply IH1 | apply IH2 ]. }
  all: eauto.
Qed.

End logrel.

Global Opaque context_interp.
Notation 𝒱 := type_interp.
Notation 𝒢 := context_interp.
Notation ℰ := expr_interp.
Notation "'TY' Δ ;  Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).


(** ** MutBit *)
(** We once again prove safety of MutBit *)
Section mutbit.
  Context `{heapGS Σ}.

  Definition assert e := (if: e then #() else #0 #0)%E.

  Definition mutbit_t : type :=
    (TUnit → TUnit) × (TUnit → TBool).

  Definition mymutbit : expr :=
    let: "x" := ref #0 in
    ((λ: "y", assert ((!"x" = #0) || (!"x" = #1));;
              "x" <- #1 - (! "x")),
     (λ: "y", assert ((!"x" = #0) || (!"x" = #1));;
              #0 < !"x")).

  Definition mutbitN := nroot .@ "mutbit".

  Lemma mymutbit_typed :
    TY 0; ∅ ⊨ mymutbit : mutbit_t.
  Proof.
    iIntros (δ γ) "#Hctx".
    iPoseProof (context_interp_dom_eq with "Hctx") as "%Hdom".
    rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_iff_L in Hdom.
    subst γ. rewrite subst_map_empty. unfold mymutbit. simpl.
    wp_alloc l as "Hl". wp_pures.
    iApply (inv_alloc mutbitN (l ↦ #0 ∨ l ↦ #1) with "[$Hl]"). iIntros "#HInv".
    iApply wp_value. iExists _, _. iSplitR; first done. iSplit.
    - (* flip *)
      iIntros (w) "!> ->".
      wp_pures. iApply (inv_open with "HInv"); first set_solver. iIntros "[>Hl | >Hl]".
      + wp_load; wp_load; wp_store.
        iApply wp_value. eauto with iFrame.
      + wp_load. wp_load. wp_load. wp_store.
        iApply wp_value; eauto with iFrame.
    - (* get *)
      iIntros (w) "!> ->".
      wp_pures. iApply (inv_open with "HInv"); first set_solver. iIntros "[>Hl | >Hl]".
      + wp_load. wp_load. wp_pures. iApply wp_value. eauto with iFrame.
      + wp_load. wp_load. wp_load. wp_pures. iApply wp_value. eauto with iFrame.
  Qed.
End mutbit.
