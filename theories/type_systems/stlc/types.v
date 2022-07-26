From stdpp Require Import base relations tactics.
From iris Require Import prelude.
From semantics.ts.stlc Require Import lang notation.
From semantics.lib Require Import sets maps.

(** ** Syntactic typing *)
(** In the Coq formalization, we exclusively define runtime typing (Curry-style). *)
(** It will be an exercise to consider Church-style typing. *)

Inductive type : Set :=
  | Int
  | Fun (A B : type).

Definition typing_context := gmap string type.
Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A : type)
  (x: string).

(** We define notation for types in a new scope with delimiter [ty].
  See below for an example. *)
Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "→" := Fun : FType_scope.
Notation "(→)" := Fun (only parsing) : FType_scope.

(** Typing rules *)
(** We need to reserve the notation beforehand to already use it when defining the
   typing rules. *)
Reserved Notation "Γ ⊢ e : A" (at level 74, e, A at next level).
Inductive syn_typed : typing_context → expr → type → Prop :=
  | typed_var Γ x A :
      (* lookup the variable in the context *)
      Γ !! x = Some A →
      Γ ⊢ (Var x) : A
  | typed_lam Γ x e A B :
      (* add a new type assignment to the context *)
     (<[ x := A]> Γ) ⊢ e : B →
      Γ ⊢ (Lam (BNamed x) e) : (A → B)
  | typed_int Γ z :
      Γ ⊢ (LitInt z) : Int
  | typed_app Γ e1 e2 A B :
      Γ ⊢ e1 : (A → B) →
      Γ ⊢ e2 : A →
      Γ ⊢ e1 e2 : B
  | typed_add Γ e1 e2 :
      Γ ⊢ e1 : Int →
      Γ ⊢ e2 : Int →
      Γ ⊢ e1 + e2 : Int
where "Γ ⊢ e : A" := (syn_typed Γ e%E A%ty) : FType_scope.
(** Add constructors to [eauto]'s hint database. *)
#[export] Hint Constructors syn_typed : core.
Local Open Scope FType_scope.

(** a small example *)
Goal ∅ ⊢ (λ: "x", 1 + "x")%E : (Int → Int).
Proof. eauto. Qed.

(** We derive some inversion lemmas -- this is cleaner than directly
  using the [inversion] tactic everywhere.*)
Lemma var_inversion Γ (x: string) A: Γ ⊢ x : A → Γ !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Γ (x: binder) e C:
  Γ ⊢ (λ: x, e) : C →
  ∃ A B y, C = (A → B)%ty ∧ x = BNamed y ∧ <[y:=A]> Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lit_int_inversion Γ (n: Z) A: Γ ⊢ n : A → A = Int.
Proof. inversion 1; subst; auto. Qed.

Lemma app_inversion Γ e1 e2 B:
  Γ ⊢ e1 e2 : B →
  ∃ A,  Γ ⊢ e1 : (A → B) ∧  Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma plus_inversion Γ e1 e2 B:
  Γ ⊢ e1 + e2 : B →
  B = Int ∧ Γ ⊢ e1 : Int ∧ Γ ⊢ e2 : Int.
Proof. inversion 1; subst; eauto. Qed.


Lemma syn_typed_closed Γ e A X :
  Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  induction 1 as [ | ?????? IH | | | ] in X |-*; simpl; intros Hx; try done.
  { (* var *) apply bool_decide_pack, Hx. apply elem_of_dom; eauto. }
  { (* lam *) apply IH.
    intros y. rewrite elem_of_dom lookup_insert_is_Some.
    intros [<- | [? Hy]]; first by apply elem_of_cons; eauto.
    apply elem_of_cons. right. eapply Hx. by apply elem_of_dom.
  }
  (* everything else *)
  all: repeat match goal with
              | |- Is_true (_ && _)  => apply andb_True; split
              end.
  all: naive_solver.
Qed.

Lemma typed_weakening Γ Δ e A:
  Γ ⊢ e : A →
  Γ ⊆ Δ →
  Δ ⊢ e : A.
Proof.
  induction 1 as [| Γ x e A B Htyp IH | | | ] in Δ; intros Hsub; eauto.
  - econstructor. by eapply lookup_weaken.
  - econstructor. eapply IH. by eapply insert_mono.
Qed.

(** Preservation of typing under substitution *)
Lemma typed_substitutivity e e' Γ x A B :
  ∅ ⊢ e' : A →
  <[x := A]> Γ ⊢ e : B →
  Γ ⊢ subst x e' e : B.
Proof.
  intros He'. revert B Γ; induction e as [y | y | | |]; intros B Γ; simpl.
  - intros Hp%var_inversion; destruct decide; subst; eauto.
    + rewrite lookup_insert in Hp. injection Hp as ->.
      eapply typed_weakening; first done. apply map_empty_subseteq.
    + rewrite lookup_insert_ne in Hp; last done. auto.
  - intros (C & D & z & -> & -> & Hty)%lam_inversion.
    econstructor. destruct decide as [|Heq]; simplify_eq.
    + by rewrite insert_insert in Hty.
    + rewrite insert_commute in Hty; last naive_solver. eauto.
  - intros (C & Hty1 & Hty2)%app_inversion; eauto.
  - intros ->%lit_int_inversion. eauto.
  - intros (-> & Hty1 & Hty2)%plus_inversion; eauto.
Qed.

(** Canonical value lemmas *)
Lemma canonical_values_arr Γ e A B:
  Γ ⊢ e : (A → B) →
  is_val e →
  ∃ x e', e = (λ: x, e')%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_int Γ e:
  Γ ⊢ e : Int →
  is_val e →
  ∃ n: Z, e = n.
Proof.
  inversion 1; simpl; naive_solver.
Qed.


(** Progress lemma *)
Lemma typed_progress e A:
  ∅ ⊢ e : A → is_val e ∨ contextual_reducible e.
Proof.
  remember ∅ as Γ. induction 1 as [| | | Γ e1 e2 A B Hty IH1 _ IH2 | Γ e1 e2 Hty1 IH1 Hty2 IH2].
  - subst. naive_solver.
  - left. done.
  - left. done.
  - destruct (IH2 HeqΓ) as [H2|H2]; [destruct (IH1 HeqΓ) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (x & e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step (AppLCtx HoleCtx v)). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step (AppRCtx e1 HoleCtx)). done.
  - destruct (IH2 HeqΓ) as [H2|H2]; [destruct (IH1 HeqΓ) as [H1|H1]|].
    + right. eapply canonical_values_int in Hty1 as [n1 ->]; last done.
      eapply canonical_values_int in Hty2 as [n2 ->]; last done.
      eexists. eapply base_contextual_step. eapply PlusS; eauto.
    + right. eapply is_val_spec in H2 as [v Heq].
      replace e2 with (of_val v); last by eapply of_to_val.
      destruct H1 as [e1' Hstep].
      eexists. eapply (fill_contextual_step (PlusLCtx HoleCtx v)). done.
    + right. destruct H2 as [e2' H2].
      eexists. eapply (fill_contextual_step (PlusRCtx e1 HoleCtx)). done.
Qed.

(** Contextual typing *)
Definition ectx_typing (K: ectx) (A B: type) :=
  ∀ e, ∅ ⊢ e : A → ∅ ⊢ (fill K e) : B.

Lemma fill_typing_decompose K e A:
  ∅ ⊢ fill K e : A →
  ∃ B, ∅ ⊢ e : B ∧ ectx_typing K B A.
Proof.
  unfold ectx_typing; induction K in e,A |-*; simpl; eauto.
  all: inversion 1; subst; edestruct IHK as [B [Hit Hty]]; eauto.
Qed.

Lemma fill_typing_compose K e A B:
  ∅ ⊢ e : B →
  ectx_typing K B A →
  ∅ ⊢ fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.

(** Base preservation *)
Lemma typed_preservation_base_step e e' A:
  ∅ ⊢ e : A →
  base_step e e' →
  ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [| e1 e2 n1 n2 n3 Heq1 Heq2 Heval]; subst.
  - eapply app_inversion in Hty as (B & Hty1 & Hty2).
    eapply lam_inversion in Hty1 as (B' & A' & y & Heq1 & Heq2 & Hty).
    simplify_eq. eapply typed_substitutivity; eauto.
  - eapply plus_inversion in Hty as (-> & Hty1 & Hty2).
    econstructor.
Qed.

(** Preservation *)
Lemma typed_preservation e e' A:
  ∅ ⊢ e : A →
  contextual_step e e' →
  ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply typed_preservation_base_step.
Qed.

Lemma typed_safety e1 e2 A:
  ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ contextual_reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed.
