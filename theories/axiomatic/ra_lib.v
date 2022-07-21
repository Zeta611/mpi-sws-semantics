From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.bi Require Import fractional.
From semantics.axiomatic.heap_lang Require Import primitive_laws proofmode.
From iris.base_logic Require Import own.
From iris.prelude Require Import options.

(** Library for defining Leibniz RAs *)

Definition lra_included {A : Type} `{Op A} (x y : A) := ∃ z, y = x ⋅ z.
Infix "≼" := lra_included.

Record LRAMixin (A : Type) `{!PCore A} `{!Op A} `{!Valid A} : Prop := mk_LRA
{
  mixin_lra_assoc : Assoc (=) (op (A := A));
  mixin_lra_comm : Comm (=) (op (A := A));
  mixin_lra_pcore_l : ∀ x cx : A, pcore x = Some cx → cx ⋅ x = x;
  mixin_lra_pcore_idemp : ∀ x cx : A, pcore x = Some cx → pcore cx = Some cx;
  mixin_lra_pcore_mono : ∀ x y cx : A, x ≼ y → pcore x = Some cx → ∃ cy : A, pcore y = Some cy ∧ cx ≼ cy;
  mixin_lra_valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x
}.
Structure lra : Type := Lra
{
  lra_car :> Type;
  lra_pcore : PCore lra_car;
  lra_op : Op lra_car;
  lra_valid : Valid lra_car;
  lra_mixin : LRAMixin lra_car;
}.
Global Arguments Lra _ {_ _ _} _.
Global Arguments lra_car : simpl never.
Global Arguments lra_pcore : simpl never.
Global Arguments lra_op : simpl never.
Global Arguments lra_valid : simpl never.
Global Arguments lra_mixin : simpl never.
Add Printing Constructor lra.
Global Hint Extern 0 (PCore _) => refine (lra_pcore _); shelve : typeclass_instances.
Global Hint Extern 0 (Op _) => refine (lra_op _); shelve : typeclass_instances.
Global Hint Extern 0 (Valid _) => refine (lra_valid _); shelve : typeclass_instances.

Section lifting.
  Context {A : lra}.
  Global Instance lra_comm : Comm (=) (op (A := A)).
  Proof. eapply mixin_lra_comm, A. Qed.
  Global Instance lra_assoc : Assoc (=) (op (A := A)).
  Proof. eapply mixin_lra_assoc, A. Qed.
  Lemma lra_pcore_l (x cx : A) : pcore x = Some cx → cx ⋅ x = x.
  Proof. eapply mixin_lra_pcore_l, A. Qed.
  Lemma lra_pcore_idemp (x cx : A) : pcore x = Some cx → pcore cx = Some cx.
  Proof. eapply mixin_lra_pcore_idemp, A. Qed.
  Lemma lra_pcore_mono (x y cx : A) : x ≼ y → pcore x = Some cx → ∃ cy : A, pcore y = Some cy ∧ cx ≼ cy.
  Proof. eapply mixin_lra_pcore_mono, A. Qed.
  Lemma lra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x.
  Proof. eapply mixin_lra_valid_op_l, A. Qed.
End lifting.

Record ULRAMixin (A : Type) `{Unit A} `{!PCore A} `{!Op A} `{!Valid A} : Prop := mk_ULRA
{
  mixin_ulra_unit_left_id : LeftId (eq (A := A)) ε (⋅);
  mixin_ulra_unit_valid : ✓ (ε : A);
  mixin_ulra_unit_pcore : pcore (ε : A) = Some ε;
}.

Structure ulra : Type := Ulra
{
  ulra_car :> Type;
  ulra_pcore : PCore ulra_car;
  ulra_op : Op ulra_car;
  ulra_valid : Valid ulra_car;
  ulra_unit : Unit ulra_car;
  ulra_lra_mixin : LRAMixin ulra_car;
  ulra_mixin : ULRAMixin ulra_car;
}.

Global Arguments Ulra _ {_ _ _ _} _ _.
Global Arguments ulra_car : simpl never.
Global Arguments ulra_pcore : simpl never.
Global Arguments ulra_op : simpl never.
Global Arguments ulra_valid : simpl never.
Global Arguments ulra_unit : simpl never.
Global Arguments ulra_lra_mixin : simpl never.
Global Arguments ulra_mixin : simpl never.
Add Printing Constructor ulra.

Global Hint Extern 0 (Unit _) => refine (ulra_unit _); shelve : typeclass_instances.
Coercion ulra_lraR (A : ulra) : lra :=
  Lra A (ulra_lra_mixin A).
Canonical Structure ulra_lraR.

Section lifting.
  Context {A : ulra}.
  Implicit Types x y : A.
  Lemma ulra_unit_valid : ✓ (ε : A).
  Proof. eapply mixin_ulra_unit_valid, A. Qed.
  Global Instance ulra_unit_left_id : LeftId (=) ε (@op A _).
  Proof. eapply mixin_ulra_unit_left_id, A. Qed.
  Lemma ulra_unit_pcore : pcore (ε:A) = Some ε.
  Proof. eapply mixin_ulra_unit_pcore, A. Qed.
End lifting.

Definition opMLRA {A : lra} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opMLRA (at level 50, left associativity) : stdpp_scope.

Definition lra_update {A : lra} (x y : A) :=
  ∀ (f : option A), ✓ (x ⋅? f) → ✓ (y ⋅? f).

Definition lra_updateP {A : lra} (x : A) (P : A → Prop) :=
  ∀ (f : option A), ✓ (x ⋅? f) → ∃ y, P y ∧ ✓ (y ⋅? f).

Definition lra_exclusive {A : lra} (a : A) :=
  ∀ b, ¬ ✓ (a ⋅ b).

Definition lra_local_update {A : lra} (p1 p2 : A * A) :=
  ∀ c, ✓ p1.1 ∧ p1.1 = p1.2 ⋅? c → ✓ p2.1 ∧ p2.1 = p2.2 ⋅? c.

(** Lifting our RA definition to Cmra *)
Lemma LRA_RAMixin {A} `{!PCore A} `{!Op A} `{!Valid A} :
  let H : Equiv A := equivL in
  LRAMixin A → RAMixin A.
Proof.
  intros Hequiv. assert (Equivalence Hequiv).
  { subst Hequiv. apply _. }
  simpl. intros [Asso Com PcoreL PcoreIdemp PcoreMono ValidOpL].
  constructor; eauto; try solve_proper.
  - intros ??? ->%leibniz_equiv ->. eauto.
  - intros ?? ->%PcoreIdemp. done.
Qed.

Notation cmra_of_lra A mix := (discreteR A (LRA_RAMixin mix)) (only parsing).

Section total_updates.
  Local Set Default Proof Using "Type*".
  Context `{CmraDiscrete A}.

  Lemma cmra_discrete_update (x y : A) :
    x ~~> y ↔ ∀ z, ✓ (cmra.opM x z) → ✓ (cmra.opM y z).
  Proof.
    split => Hup.
    - intros z Hv. apply cmra_valid_validN. intros n. apply Hup.
      apply cmra_valid_validN. done.
    - intros n mz. rewrite -!cmra_discrete_valid_iff. apply Hup.
  Qed.
End total_updates.

Section upd_iff.
  Context {A : Type} `{PCore A} `{Op A} `{Valid A}.
  Context {Hra : LRAMixin A}.
  (* is that fine? or will this screw up canonical structure inference somehow? *)
  Local Canonical Structure leib := leibnizO A.
  Let Ara := Lra A Hra.
  Let Acmra := discreteR A (LRA_RAMixin Hra).

  Global Instance A_discrete : CmraDiscrete (Acmra).
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma ra_update_iff (a b : Acmra) :
    lra_update (a : Ara) b ↔ cmra_update a b.
  Proof.
    split.
    - intros Ha. apply cmra_discrete_update. apply Ha.
    - rewrite cmra_discrete_update. done.
  Qed.

  Context `{inG Σ Acmra}.
  Lemma own_lra_update γ (a b : Acmra) :
    lra_update (a : Ara) (b : Ara) →
    own γ a -∗ |==> own γ b.
  Proof.
    rewrite ra_update_iff. intros ?. by iApply own_update.
  Qed.
End upd_iff.

