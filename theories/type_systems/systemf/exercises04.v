From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf Require Import lang notation parallel_subst types logrel tactics.

Section church_encodings.
  (** Exercise 1 (LN Exercise 24): Church encoding, sum types *)
  (* a) Define your encoding *)
  Definition sum_type (A B : type) : type := #0 (* FIXME *).

  (* b) Implement inj1, inj2, case *)
  Definition injl_val (v : val) : val := #0 (* FIXME *).
  Definition injl_expr (e : expr) : expr := #0 (* FIXME *).
  Definition injr_val (v : val) : val := #0 (* FIXME *).
  Definition injr_expr (e : expr) : expr := #0 (* FIXME *).

  (* You may want to use the variables x1, x2 for the match arms to fit the typing statements below. *)
  Definition match_expr (e : expr) (e1 e2 : expr) : expr :=
    #0 (* FIXME *).

  (* c) Reduction behavior *)
  (* Some lemmas about substitutions might be useful. Look near the end of the lang.v file! *)
  Lemma match_expr_red_injl e e1 e2 (vl v' : val) :
    is_closed [] vl →
    is_closed ["x1"] e1 →
    big_step e (injl_val vl) →
    big_step (subst' "x1" vl e1) v' →
    big_step (match_expr e e1 e2) v'.
  Proof.
    (* FIXME *)
  (*Qed.*)
  Admitted.

  Lemma match_expr_red_injr e e1 e2 (vl v' : val) :
    is_closed [] vl →
    big_step e (injr_val vl) →
    big_step (subst' "x2" vl e2) v' →
    big_step (match_expr e e1 e2) v'.
  Proof.
    intros. bs_step_det.
    (* FIXME *)
  Admitted.

  Lemma injr_expr_red e v :
    big_step e v →
    big_step (injr_expr e) (injr_val v).
  Proof.
    intros. bs_step_det.
    (* FIXME *)
  Admitted.

  Lemma injl_expr_red e v :
    big_step e v →
    big_step (injl_expr e) (injl_val v).
  Proof.
    intros. bs_step_det.
    (* FIXME *)
  Admitted.


  (* d) Typing rules *)
  Lemma sum_injl_typed n Γ (e : expr) A B :
    type_wf n B →
    type_wf n A →
    TY n; Γ ⊢ e : A →
    TY n; Γ ⊢ injl_expr e : sum_type A B.
  Proof.
    intros. solve_typing.
    (* FIXME *)
  Admitted.

  Lemma sum_injr_typed n Γ e A B :
    type_wf n B →
    type_wf n A →
    TY n; Γ ⊢ e : B →
    TY n; Γ ⊢ injr_expr e : sum_type A B.
  Proof.
    intros. solve_typing.
    (* FIXME *)
  Admitted.

  Lemma sum_match_typed n Γ A B C e e1 e2 :
    type_wf n A →
    type_wf n B →
    type_wf n C →
    TY n; Γ ⊢ e : sum_type A B →
    TY n; <["x1" := A]> Γ ⊢ e1 : C →
    TY n; <["x2" := B]> Γ ⊢ e2 : C →
    TY n; Γ ⊢ match_expr e e1 e2 : C.
  Proof.
    intros. solve_typing.
    (* FIXME *)
  Admitted.

  (** Exercise 2 (LN Exercise 25): church encoding, list types *)
  Definition list_type (A : type) : type := #0 (* FIXME *).

  (* a) Implement nil and cons. *)
  Definition nil_val : val := #0 (* FIXME *).
  Definition cons_val (v1 v2 : val) : val := #0 (* FIXME *).
  Definition cons_expr (e1 e2 : expr) : expr :=
    #0 (* FIXME *).

  (* b) Define typing rules and prove them *)
  Lemma nil_typed n Γ A :
    type_wf n A →
    TY n; Γ ⊢ nil_val : list_type A.
  Proof.
    intros. solve_typing.
    (* FIXME *)
  Admitted.

  Lemma cons_typed n Γ (e1 e2 : expr) A :
    type_wf n A →
    TY n; Γ ⊢ e2 : list_type A →
    TY n; Γ ⊢ e1 : A →
    TY n; Γ ⊢ cons_expr e1 e2 : list_type A.
  Proof.
    intros. repeat solve_typing.
    (* FIXME *)
  Admitted.

  (* c) Define a function head of type list A → A + 1 *)
  Definition head_expr : val := #0 (* FIXME *).

  Lemma head_typed n Γ A :
    type_wf n A →
    TY n; Γ ⊢ head_expr : (list_type A → (A + Unit)).
  Proof.
    intros. solve_typing.
    (* FIXME *)
  Admitted.

  (* d) Define a function [tail] of type list A → list A *)
  Definition tail_val : val :=
    #0 (* FIXME *).

  Lemma tail_typed n Γ A :
    type_wf n A →
    TY n; Γ ⊢ tail_val : (list_type A → list_type A).
  Proof.
    intros. repeat solve_typing.
    (* FIXME *)
  Admitted.

End church_encodings.

Section free_theorems.

  (** Exercise 4 (LN Exercise 27): Free Theorems I *)
  (* a) State a free theorem for the type ∀ α, β. α → β → α × β *)
  Lemma free_thm_1 :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: ∀: #1 → #0 → #1 × #0) →
    True. (* FIXME: state your free theorem *)
  Proof.
    (* FIXME *)
  Admitted.

  (* b) State a free theorem for the type ∀ α, β. α × β → α *)
  Lemma free_thm_2 :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: ∀: #1 × #0 → #1) →
    True. (* FIXME: state your free theorem *)
  Proof.
    (* FIXME *)
  Admitted.

  (* c) State a free theorem for the type ∀ α, β. α → β *)
  Lemma free_thm_3 :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: ∀: #1 → #0) →
    True (* FIXME *).
  Proof.
    (* FIXME *)
  Admitted.


  (** Exercise 5 (LN Exercise 28): Fre Theorems II *)
  Lemma free_theorem_either :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: #0 → #0 → #0) →
    ∀ (v1 v2 : val), is_closed [] v1 → is_closed [] v2 →
      big_step (f <> v1 v2) v1 ∨ big_step (f <> v1 v2) v2.
  Proof.
    (* FIXME *)
  Admitted.

  (** Exercise 6 (LN Exercise 29): Free Theorems III *)
  (* Hint: you might want to use the fact that our reduction is deterministic.
    However, if you do so, be sure to state this fact formally and prove it.
  *)

  Lemma free_theorems_magic :
    ∀ (A A1 A2 : type) (f g : val),
    type_wf 0 A → type_wf 0 A1 → type_wf 0 A2 →
    is_closed [] f → is_closed [] g →
    TY 0; ∅ ⊢ f : (∀: (A1 → A2 → #0) → #0) →
    TY 0; ∅ ⊢ g : (A1 → A2 → A) →
    ∀ v, big_step (f <> g) v →
    ∃ (v1 v2 : val), big_step (g v1 v2) v.
  Proof.
    (* TODO *)
    (* Hint: you may find the following lemmas useful:
        - [sem_val_rel_cons]
        - [type_wf_closed]
        - [val_rel_is_closed]
        - [big_step_preserve_closed]
    *)
  Abort.

End free_theorems.
