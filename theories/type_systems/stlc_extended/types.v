From stdpp Require Import base relations.
From iris Require Import prelude.
From semantics.lib Require Import maps.
From semantics.ts.stlc_extended Require Import lang notation.

(** ** Syntactic typing *)
Inductive type : Type :=
  | Int
  | Fun (A B : type)
  | Prod (A B : type)
  | Sum (A B : type).

Definition typing_context := gmap string type.
Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr).

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "→" := Fun : FType_scope.
Notation "(→)" := Fun (only parsing) : FType_scope.
Infix "×" := Prod (at level 70) : FType_scope.
Notation "(×)" := Prod (only parsing) : FType_scope.
Infix "+" := Sum : FType_scope.
Notation "(+)" := Sum (only parsing) : FType_scope.

Reserved Notation "Γ ⊢ e : A" (at level 74, e, A at next level).

Inductive bin_op_typed : bin_op → type → type → type → Prop :=
  (* FIXME: add the typing rules for binary operators here *)
.
#[export] Hint Constructors bin_op_typed : core.

Inductive syn_typed : typing_context → expr → type → Prop :=
  | typed_var Γ x A :
      Γ !! x = Some A →
      Γ ⊢ (Var x) : A
  | typed_lam Γ x e A B :
      (<[ x := A]> Γ) ⊢ e : B →
      Γ ⊢ (Lam (BNamed x) e) : (A → B)
  | typed_lam_anon Γ e A B :
      Γ ⊢ e : B →
      Γ ⊢ (Lam BAnon e) : (A → B)
  | typed_int Γ z : Γ ⊢ (Lit $ LitInt z) : Int
  | typed_app Γ e1 e2 A B :
      Γ ⊢ e1 : (A → B) →
      Γ ⊢ e2 : A →
      Γ ⊢ (e1 e2)%E : B
  (* FIXME: provide the new typing rules *)
where "Γ ⊢ e : A" := (syn_typed Γ e%E A%ty).
#[export] Hint Constructors syn_typed : core.

(** Examples *)
Goal ∅ ⊢ (λ: "x", "x")%E : (Int → Int).
Proof. eauto. Qed.

Lemma syn_typed_closed Γ e A X :
  Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  (* FIXME: you will need to add the new cases to the intro pattern *)
  induction 1 as [ | ?????? IH | | | ] in X |-*; simpl; intros Hx; try done.
  { (* var *) apply bool_decide_pack, Hx. apply elem_of_dom; eauto. }
  { (* lam *) apply IH.
    intros y. rewrite elem_of_dom lookup_insert_is_Some.
    intros [<- | [? Hy]]; first by apply elem_of_cons; eauto.
    apply elem_of_cons. right. eapply Hx. by apply elem_of_dom.
  }
  { (* anon lam *) naive_solver. }
  (* everything else *)
  all: repeat match goal with
              | |- Is_true (_ && _)  => apply andb_True; split
              end.
  all: try naive_solver.
Qed.

Lemma typed_weakening Γ Δ e A:
  Γ ⊢ e : A →
  Γ ⊆ Δ →
  Δ ⊢ e : A.
Proof.
  (* FIXME: you will need to add the new cases to the intro pattern *)
  induction 1 as [| Γ x e A B Htyp IH | | | ] in Δ |-*; intros Hsub; eauto.
  - (* var *) econstructor. by eapply lookup_weaken.
  - (* lam *) econstructor. eapply IH; eauto. by eapply insert_mono.
Qed.

(** Typing inversion lemmas *)
Lemma var_inversion Γ (x: string) A: Γ ⊢ x : A → Γ !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion Γ (x: string) e C:
  Γ ⊢ (λ: x, e) : C →
  ∃ A B, C = (A → B)%ty ∧ <[x:=A]> Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lam_anon_inversion Γ e C:
  Γ ⊢ (λ: <>, e) : C →
  ∃ A B, C = (A → B)%ty ∧ Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma app_inversion Γ e1 e2 B:
  Γ ⊢ e1 e2 : B →
  ∃ A, Γ ⊢ e1 : (A → B) ∧ Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

(* FIXME: add inversion lemmas for the new typing rules.
  They will be very useful for the proofs below!
*)

Lemma typed_substitutivity e e' Γ (x: string) A B :
  ∅ ⊢ e' : A →
  (<[x := A]> Γ) ⊢ e : B →
  Γ ⊢ lang.subst x e' e : B.
Proof.
  intros He'. revert B Γ; induction e as [| y | y | | | | | |  | | ]; intros B Γ; simpl.
  - inversion 1; subst; auto.
  - intros Hp % var_inversion.
    destruct (decide (x = y)).
    + subst. rewrite lookup_insert in Hp. injection Hp as ->.
      eapply typed_weakening; [done| ]. apply map_empty_subseteq.
    + rewrite lookup_insert_ne in Hp; last done. auto.
  - destruct y as [ | y].
    { intros (A' & C & -> & Hty) % lam_anon_inversion.
      econstructor. destruct decide as [Heq|].
      + congruence.
      + eauto.
    }
    intros (A' & C & -> & Hty) % lam_inversion.
    econstructor. destruct decide as [Heq|].
    + injection Heq as [= ->]. by rewrite insert_insert in Hty.
    + rewrite insert_commute in Hty; last naive_solver. eauto.
  - intros (C & Hty1 & Hty2) % app_inversion. eauto.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
  - (* FIXME *) admit.
(*Qed.*)
Admitted.

(** Canonical values *)
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
  ∃ n: Z, e = (#n)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

(* FIXME: add canonical forms lemmas for the new types *)

(** Progress *)
Lemma typed_progress e A:
  ∅ ⊢ e : A → is_val e ∨ reducible e.
Proof.
  remember ∅ as Γ.
  (* FIXME: you will need to extend the intro pattern *)
  induction 1 as [| | | | Γ e1 e2 A B Hty IH1 _ IH2 ].
  - subst. naive_solver.
  - left. done.
  - left. done.
  - (* int *)left. done.
  - (* app *)
    destruct (IH2 HeqΓ) as [H2|H2]; [destruct (IH1 HeqΓ) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (x & e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. destruct H1 as [e1' Hstep].
      eexists. eauto.
    + right. destruct H2 as [e2' H2].
      eexists. eauto.
  (* FIXME: prove the new cases *)
(*Qed.*)
Admitted.

Definition ectx_typing (K: ectx) (A B: type) :=
  ∀ e, ∅ ⊢ e : A → ∅ ⊢ (fill K e) : B.

Lemma fill_typing_decompose K e A:
  ∅ ⊢ fill K e : A →
  ∃ B, ∅ ⊢ e : B ∧ ectx_typing K B A.
Proof.
  unfold ectx_typing; induction K in e,A |-*; simpl; eauto.
  all: inversion 1; subst; edestruct IHK as [? [Hit Hty]]; eauto.
Qed.

Lemma fill_typing_compose K e A B:
  ∅ ⊢ e : B →
  ectx_typing K B A →
  ∅ ⊢ fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.

Lemma typed_preservation_base_step e e' A:
  ∅ ⊢ e : A →
  base_step e e' →
  ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep.
  destruct Hstep as [  ]; subst.
  - eapply app_inversion in Hty as (B & H1 & H2).
    destruct x as [|x].
    { eapply lam_anon_inversion in H1 as (C & D & [= -> ->] & Hty). done. }
    eapply lam_inversion in H1 as (C & D & Heq & Hty).
    injection Heq as -> ->.
    eapply typed_substitutivity; eauto.
  (* FIXME: extend this for the new cases *)
(*Qed.*)
Admitted.

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

Lemma type_safety e1 e2 A:
  ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed.
