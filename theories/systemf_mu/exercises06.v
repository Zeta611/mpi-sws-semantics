From stdpp Require Import gmap base relations tactics.
From iris Require Import prelude.
From semantics.systemf_mu Require Import lang notation types pure tactics logrel.
From Autosubst Require Import Autosubst.

(** * Exercise Sheet 6 *)

Notation sub := lang.subst.

Implicit Types
  (e : expr)
  (v : val)
  (A B : type)
.

(** ** Exercise 5: Keep Rollin' *)
(** This exercise is slightly tricky.
  We strongly recommend you to first work on the other exercises.
  You may use the results from this exercise, in particular the fixpoint combinator and its typing, in other exercises, however (which is why it comes first in this Coq file).
 *)
Section recursion_combinator.
  Variable (f x: string). (* the template of the recursive function *)
  Hypothesis (Hfx: f ≠ x).

  (** Recursion Combinator *)
  (* First, setup a definition [Rec] satisfying the reduction lemmas below. *)

  (** You may find an auxiliary definition [rec_body] helpful *)
  Definition rec_body (t: expr) : expr :=
    (* FIXME *)
    roll (λ: f x, #0).

  Definition Rec (t: expr): val :=
    λ: x, rec_body t. (* FIXME *)

  Lemma closed_rec_body t :
    is_closed [] t → is_closed [] (rec_body t).
  Proof. simplify_closed. Qed.
  Lemma closed_Rec t :
    is_closed [] t → is_closed [] (Rec t).
  Proof. simplify_closed. Qed.
  Lemma is_val_Rec t:
    is_val (Rec t).
  Proof. done. Qed.

   Lemma Rec_red (t e: expr):
    is_val e →
    is_val t →
    is_closed [] e →
    is_closed [] t →
    rtc contextual_step ((Rec t) e) (t (Rec t) e).
  Proof.
    (* FIXME *)
  Admitted.

  Lemma rec_body_typing n Γ (A B: type) t :
    Γ !! x = None →
    Γ !! f = None →
    type_wf n A →
    type_wf n B →
    TY n; Γ ⊢ t : ((A → B) → (A → B)) →
    TY n; Γ ⊢ rec_body t : (μ: #0 → rename (+1) A → rename (+1) B).
  Proof.
    (* FIXME *)
  Admitted.

  Lemma Rec_typing n Γ A B t:
    type_wf n A →
    type_wf n B →
    Γ !! x = None →
    Γ !! f = None →
    TY n; Γ ⊢ t : ((A → B) → (A → B)) →
    TY n; Γ ⊢ (Rec t) : (A → B).
  Proof.
    (* FIXME *)
  Admitted.

End recursion_combinator.

Definition Fix (f x: string) (e: expr) : val := (Rec f x (Lam f%string (Lam x%string e))).
(** We "seal" the definition to make it opaque to the [solve_typing] tactic.
  We do not want [solve_typing] to unfold the definition, instead, we should manually
  apply the typing rule below.

  You do not need to understand this in detail -- the only thing of relevance is that
  you can use the equality [Fix_eq] to unfold the definition of [Fix].
*)
Definition Fix_aux : seal (Fix). Proof. by eexists. Qed.
Definition Fix' := Fix_aux.(unseal).
Lemma Fix_eq : Fix' = Fix.
Proof. rewrite -Fix_aux.(seal_eq) //. Qed.
Arguments Fix' _ _ _ : simpl never.

(* the actual fixpoint combinator *)
Notation "'fix:' f x := e" := (Fix' f x e)%E
  (at level 200, f, x at level 1, e at level 200,
   format "'[' 'fix:'  f  x   :=  '/  ' e ']'") : val_scope.
Notation "'fix:' f x := e" := (Fix' f x e)%E
  (at level 200, f, x at level 1, e at level 200,
   format "'[' 'fix:'  f  x   :=  '/  ' e ']'") : expr_scope.


Lemma fix_red (f x: string) (e e': expr):
  is_closed [x; f] e →
  is_closed [] e' →
  is_val e' →
  f ≠ x →
  rtc contextual_step ((fix: f x := e) e')%V (sub x e' (sub f (fix: f x := e)%V e)).
Proof.
  (* FIXME *)
Admitted.

Lemma fix_typing n Γ (f x: string) (A B: type) (e: expr):
  type_wf n A →
  type_wf n B →
  f ≠ x →
  TY n; <[x := A]> (<[f := (A → B)%ty]> Γ) ⊢ e : B →
  TY n; Γ ⊢ (fix: f x := e) : (A → B).
Proof.
  (* FIXME *)
Admitted.

(** ** Exercise 1: Encode arithmetic expressions *)

Definition aexpr : type := #0 (* FIXME *).

Definition num_val (v : val) : val := #0 (* FIXME *).
Definition num_expr (e : expr) : expr := #0 (* FIXME *).

Definition plus_val (v1 v2 : val) : val := #0 (* FIXME *).
Definition plus_expr (e1 e2 : expr) : expr := #0 (* FIXME *).

Definition mul_val (v1 v2 : val) : val := #0 (* FIXME *).
Definition mul_expr (e1 e2 : expr) : expr := #0 (* FIXME *).

Lemma num_expr_typed n Γ e :
  TY n; Γ ⊢ e : Int →
  TY n; Γ ⊢ num_expr e : aexpr.
Proof.
  intros. solve_typing.
  (* FIXME *)
(*Qed.*)
Admitted.
Lemma plus_expr_typed n Γ e1 e2 :
  TY n; Γ ⊢ e1 : aexpr →
  TY n; Γ ⊢ e2 : aexpr →
  TY n; Γ ⊢ plus_expr e1 e2 : aexpr.
Proof.
  (*intros; solve_typing.*)
(*Qed.*)
Admitted.
Lemma mul_expr_typed n Γ e1 e2 :
  TY n; Γ ⊢ e1 : aexpr →
  TY n; Γ ⊢ e2 : aexpr →
  TY n; Γ ⊢ mul_expr e1 e2 : aexpr.
Proof.
  (*intros; solve_typing.*)
(*Qed.*)
Admitted.

Definition eval_aexpr : val :=
  #0 (* FIXME *).
Lemma eval_aexpr_typed Γ n :
  TY n; Γ ⊢ eval_aexpr : (aexpr → Int).
Proof.
(*Qed.*)
(* FIXME *)
Admitted.


(** Exercise 3: Lists *)

Definition list_t (A : type) : type :=
  ∃: (#0 (* mynil *)
    × (A.[ren (+1)] → #0 → #0) (* mycons *)
    × (∀: #1 → #0 → (A.[ren (+2)] → #1 → #0) → #0)) (* mylistcase *)
  .

Definition mylist_impl : val :=
  #0 (* FIXME *)
  .

Lemma mylist_impl_sem_typed A :
  type_wf 0 A →
  ∀ k, 𝒱 (list_t A) δ_any k mylist_impl.
Proof.
  (* FIXME *)
Admitted.
