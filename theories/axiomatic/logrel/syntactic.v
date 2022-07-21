From iris.heap_lang Require Import lang notation.
From iris.heap_lang Require Export metatheory.
From semantics.axiomatic.logrel Require Import notation.
From Autosubst Require Export Autosubst.
From stdpp Require Import gmap.
From iris.prelude Require Import options.

(** ** Syntactic typing *)
(** We use De Bruijn indices with the help of the Autosubst library. *)
Inductive type : Type :=
  (** [var] is the type of variables of Autosubst -- it unfolds to [nat] *)
  | TVar : var → type
  | TInt
  | TBool
  | TUnit
  (** The [{bind 1 of type}] tells Autosubst to put a De Bruijn binder here *)
  | TForall : {bind 1 of type} → type
  | TExists : {bind 1 of type} → type
  | TFun (A B : type)
  | TMu : {bind 1 of type} → type
  | TRef (A : type)
  | TProd (A B : type)
  | TSum (A B : type)
.

Implicit Types
  (Γ : gmap string type)
  (γ : gmap string val)
  (A B : type)
.

(** Autosubst instances.
  This lets Autosubst do its magic and derive all the substitution functions, etc.
 *)
Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Notation "'Int'" := (TInt) : FType_scope.
Notation "'Bool'" := (TBool) : FType_scope.
Notation "'Unit'" := (TUnit) : FType_scope.
Notation "'Ref'" := (TRef) : FType_scope.
Notation "# x" := (TVar x) : FType_scope.
Infix "→" := TFun : FType_scope.
Notation "(→)" := TFun (only parsing) : FType_scope.
Notation "∀: τ" :=
  (TForall τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Infix "×" := TProd (at level 70) : FType_scope.
Notation "(×)" := TProd (only parsing) : FType_scope.
Infix "+" := TSum : FType_scope.
Notation "(+)" := TSum (only parsing) : FType_scope.
Notation "μ: A" :=
  (TMu A%ty)
  (at level 100, A at level 200) : FType_scope.

(** Shift all the indices in the context by one,
   used when inserting a new type interpretation in Δ. *)
(* [<$>] is notation for the [fmap] operation that maps the substitution over the whole map. *)
(* [ren] is Autosubst's renaming operation -- it renames all type variables according to the given function,
  in this case [(+1)] to shift the variables up by 1. *)
Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)) <$> Γ) (at level 10, format "⤉ Γ").

Inductive bin_op_typed : bin_op → type → type → type → Prop :=
  | plus_op_typed : bin_op_typed PlusOp TInt TInt TInt
  | minus_op_typed : bin_op_typed MinusOp TInt TInt TInt
  | mul_op_typed : bin_op_typed MultOp TInt TInt TInt
  | lt_op_typed : bin_op_typed LtOp TInt TInt TBool
  | le_op_typed : bin_op_typed LeOp TInt TInt TBool
  | eq_op_typed : bin_op_typed EqOp TInt TInt TBool.
Inductive un_op_typed : un_op → type → type → Prop :=
  | neg_op_typed : un_op_typed NegOp TBool TBool
  | minus_un_op_typed : un_op_typed MinusUnOp TInt TInt.

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
      type_wf n (A → B)
  | type_wf_Prod n A B :
      type_wf n A →
      type_wf n B →
      type_wf n (A × B)
  | type_wf_Sum n A B :
      type_wf n A →
      type_wf n B →
      type_wf n (A + B)
  | type_wf_mu n A :
      type_wf (S n) A →
      type_wf n (μ: A)
  | type_wf_ref n A :
      type_wf n A →
      type_wf n (Ref A)
.
#[export] Hint Constructors type_wf : core.

(** NOTE: This type system is somewhat non-standard: it does not satisfy preservation!

  The reason is that we don't assign types to lambdas below the [Val] constructor (e.g. [Val (RecV ...)]).
  The trouble is that substitution does not descend below the [Val] constructor,
   which means that the typing context would need to be completely ignored by the [Val] typing (and that would similarly kill preservation).

  Note however that the [Val] constructor is quite convenient when working on program verification in Iris.
  Also, in our logical relation, (which does not care about preservation), the [Val] constructor lets us get rid of all closedness requirements on lambdas which we'd otherwise need:
    in the logical relation, we can first substitute in all the values via parallel substitution, and only after that
    the [Rec f x e] reduces to a [Val (RecV f x e)], which after that is automatically closed.

  For using the type system, this is not a major restriction: Instead of using [Val $ RecV f x e] we can always just use [Rec f x e] (which will reduce in one step to [Val $ RecV f x e].
 *)
Reserved Notation "'TY' Δ ;  Γ ⊢ e : A" (at level 74, e, A at next level).
Inductive syn_typed : nat → (gmap string type) → expr → type → Prop :=
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
      TY n; Γ ⊢ (TApp e ) : (A.[B/])
  | typed_pack n Γ A B e :
      type_wf n B →
      type_wf (S n) A →
      TY n; Γ ⊢ e : (A.[B/]) →
      TY n; Γ ⊢ (Pack e) : (∃: A)
  | typed_unpack n Γ A B e e' x :
      type_wf n B → (* we should not leak the existential! *)
      TY n; Γ ⊢ e : (∃: A) →
      (* As we descend under a type variable binder for the typing of [e'],
          we need to shift the indices in [Γ] and [B] up by one.
        On the other hand, [A] is already defined under this binder, so we need not shift it.
      *)
      TY (S n); (<[x := A]>(⤉Γ)) ⊢ e' : (B.[ren (+1)]) →
      TY n; Γ ⊢ (unpack e as BNamed x in e') : B
  | typed_int n Γ (z : Z) : TY n; Γ ⊢ (#z) : Int
  | typed_bool n Γ (b : bool) : TY n; Γ ⊢ (#b) : Bool
  | typed_unit n Γ : TY n; Γ ⊢ (#()) : Unit
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
  | typed_load n Γ e A :
      TY n; Γ ⊢ e : (Ref A) →
      TY n; Γ ⊢ !e : A
  | typed_store n Γ e1 e2 A :
      TY n; Γ ⊢ e1 : (Ref A) →
      TY n; Γ ⊢ e2 : A →
      TY n; Γ ⊢ (e1 <- e2) : Unit
  | typed_new n Γ e A :
      TY n; Γ ⊢ e : A →
      TY n; Γ ⊢ (ref e) : Ref A
where "'TY'  Δ ;  Γ ⊢ e : A" := (syn_typed Δ Γ e%E A%ty).
#[export] Hint Constructors syn_typed : core.
