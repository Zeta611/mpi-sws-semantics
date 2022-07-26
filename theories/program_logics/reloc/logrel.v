From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.heap_lang Require Export metatheory.
From semantics.pl.reloc Require Export notation src_rules.
From semantics.pl.reloc Require Export persistent_bipred.
From Autosubst Require Import Autosubst.
From iris.prelude Require Import options.

Section logrel.
Context `{relocGS Σ}.

Implicit Types
  (e : expr)
  (v : val)
  (K : list ectx_item).

(** Semantic types are, essentially, persistent predicates [val → iProp] *)
Definition semtype := persistent_bipred val (iPropI Σ).
Definition semtypeO := persistent_bipredO val (iPropI Σ).
(** Smart constructor for semantic types *)
Definition mk_semtype (pred : val → val → iProp Σ) {Pers : ∀ v w, Persistent (pred v w)} : semtype :=
  @PersBiPred _ _ pred Pers.
Global Instance semtype_pers (τ : semtypeO) : ∀ v w, Persistent (τ v w) := _.

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

(** A useful shortcut which also keeps the (persistent!) [src_ctx] around, to have it readily in hand for the invariant. *)
Definition src_expr e := (src_ctx ∗ exprS e)%I.

(** This is, essentially, the expression relation *)
Implicit Types (Ψ : val → val → iProp Σ).
Program Definition refines e e' Ψ : iProp Σ :=
  ∀ K,
    src_expr (fill K e') -∗
    WP e {{ v, ∃ v', src_expr (fill K (of_val v')) ∗ Ψ v v' }}.

(** You can ignore the following two lemmas. They state that [refines] is compatible with Iris's notion of equivalence *)
Global Instance refines_ne n :
  Proper ((=) ==> (=) ==> ((=) ==> (=) ==> dist n) ==> (dist n)) (refines).
Proof.
  intros e1 e2 -> ? ? -> p1 p2 Heq.
  unfold refines. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
  f_equiv. intros ?. f_equiv. apply Heq; done.
Qed.
Global Instance refines_equiv :
  Proper ((=) ==> (=) ==> ((=) ==> (=) ==> equiv) ==> (equiv)) (refines).
Proof.
  intros e1 e2 -> ? ? -> p1 p2 Heq.
  unfold refines. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
  f_equiv. intros ?. f_equiv. apply Heq; done.
Qed.

(** Value inclusion *)
Lemma refines_value v w Ψ :
  Ψ v w -∗ refines (of_val v) (of_val w) Ψ.
Proof.
  iIntros "Hvw" (K) "Hsrc". iApply wp_value. iExists w. iFrame.
Qed.
(** Bind *)
Lemma refines_bind e1 e2 K1 K2 Ψ :
  refines e1 e2 (λ v1 v2, refines (fill K1 v1) (fill K2 v2) Ψ) -∗ refines (fill K1 e1) (fill K2 e2) Ψ.
Proof.
  iIntros "Hrfn" (K) "Hsrc".
  iSpecialize ("Hrfn" $! (K2 ++ K)). rewrite fill_app.
  iSpecialize ("Hrfn" with "Hsrc").
  iApply (wp_bind). iApply (wp_wand with "Hrfn").
  iIntros (v) "(%v' & Hsrc & Hrfn)". rewrite fill_app.
  by iApply "Hrfn".
Qed.

(** Semantic types *)
Definition int_interp : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', (∃ n : Z, ⌜v = #n⌝ ∗ ⌜v' = #n⌝))%I.
Definition bool_interp : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', (∃ b : bool, ⌜v = #b⌝ ∗ ⌜v' = #b⌝))%I.
Definition unit_interp : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', ⌜v = #()⌝ ∗ ⌜v' = #()⌝)%I.

Program Definition fun_interp (σ1 : envO -n> semtypeO) (σ2 : envO -n> semtypeO) : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', (∀ w w', □ (σ1 δ w w' -∗ refines (v w) (v' w') (σ2 δ))))%I.
Solve Obligations with solve_proper.

(** Type variables *)
Program Definition var_interp (x : var) : envO -n> semtypeO :=
  λne δ, δ x.
Solve Obligations with solve_proper.

Program Definition all_interp σ : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', □ (∀ τ, refines (TApp v) (TApp v') (σ (τ .:: δ))))%I.
Solve Obligations with solve_proper.

Program Definition exist_interp σ : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', ∃ w w', ⌜v = PackV w⌝ ∗ ⌜v' = PackV w'⌝ ∗ ∃ τ, (σ (τ .:: δ)) w w')%I.
Solve Obligations with solve_proper.

(** Recursive types are defined via Iris's fixpoint mechanism *)
Program Definition mu_rec σ δ (rec : semtypeO) : semtypeO :=
  mk_semtype (λ v v', (∃ w w', ⌜v = RollV w⌝ ∗ ⌜v' = RollV w'⌝ ∗ ▷ (σ (rec .:: δ)) w w')%I).
Instance mu_rec_contractive σ δ : Contractive (mu_rec σ δ).
Proof. solve_contractive. Qed.
Program Definition mu_interp σ : envO -n> semtypeO :=
  λne δ, fixpoint (mu_rec σ δ).
Next Obligation. intros ?? ???. apply fixpoint_ne. solve_proper. Qed.

(** The unfolding equation for recursive types *)
Lemma mu_interp_unfold σ δ v v' :
  mu_interp σ δ v v' ⊣⊢ mu_rec σ δ (mu_interp σ δ) v v'.
Proof. f_equiv. apply fixpoint_unfold. Qed.

(** References and their invariant *)
Program Definition ref_inv (l l' : loc) : semtypeO -n> iPropO Σ :=
  λne τ, (∃ w w', l ↦ w ∗ l' ↦ₛ w' ∗ τ w w')%I.
Solve Obligations with solve_proper.
Program Definition ref_interp σ : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', ∃ l l' : loc, ⌜v = #l⌝ ∗ ⌜v' = #l'⌝ ∗ inv logN (ref_inv l l' (σ δ)))%I.
Solve Obligations with solve_proper.

Program Definition prod_interp σ1 σ2 : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', ∃ w1 w1' w2 w2', ⌜v = (w1, w2)%V⌝ ∗ ⌜v' = (w1', w2')%V⌝ ∗ σ1 δ w1 w1' ∗ σ2 δ w2 w2')%I.
Solve Obligations with solve_proper.

Program Definition sum_interp σ1 σ2 : envO -n> semtypeO :=
  λne δ, mk_semtype (λ v v', (∃ w w', ⌜v = InjLV w⌝ ∗ ⌜v' = InjLV w'⌝ ∗ σ1 δ w w') ∨
                             (∃ w w', ⌜v = InjRV w⌝ ∗ ⌜v' = InjRV w'⌝ ∗ σ2 δ w w'))%I.
Solve Obligations with solve_proper.
End defs.
End logrel.

(** Before we prove the fundamental lemma, we are first going to setup some automation to work with the source, see [proofmode.v] *)

