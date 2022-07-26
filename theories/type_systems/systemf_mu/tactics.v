From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts maps sets.
From semantics.ts.systemf_mu Require Export lang notation types.

Ltac map_solver :=
  repeat match goal with
         | |-  (⤉ _) !! _ = Some _ =>
             rewrite fmap_insert
         | |- <[ ?p := _ ]> _ !! ?p = Some _ =>
             apply lookup_insert
         | |- <[ _ := _ ]> _ !! _ = Some _ =>
             rewrite lookup_insert_ne; [ | congruence]
         end.
Ltac solve_typing :=
  intros;
  repeat match goal with
  | |- TY _ ; _ ⊢ ?e : ?A => first [eassumption | econstructor]
  (* heuristic to solve tapp goals where we need to pick the right type for the substitution *)
  | |- TY _ ; _ ⊢ ?e <> : ?A => eapply typed_tapp'; [solve_typing | | asimpl; reflexivity]
  | |- TY _ ; _ ⊢ Unroll ?e : ?A => eapply typed_unroll'; [solve_typing | asimpl; reflexivity]
  | |- bin_op_typed _ _ _ _ => econstructor
  | |- un_op_typed _ _ _ _ => econstructor
  | |- type_wf _ ?e => assert_fails (is_evar e); eassumption
  | |- type_wf _ ?e => assert_fails (is_evar e); econstructor
  | |- type_wf _ (subst _ ?A) => eapply type_wf_subst; [ | intros; simpl]
  | |- type_wf _ ?e => assert_fails (is_evar e); eapply type_wf_mono; [eassumption | lia]
  (* conditions spawned by the tyvar case of [type_wf] *)
  | |- _ < _ => lia
  (* conditions spawned by the variable case *)
  | |- _ !! _ = Some _ => map_solver
  end.

Tactic Notation "unify_type" uconstr(A) :=
  match goal with
  | |- TY ?n; ?Γ ⊢ ?e : ?B => unify A B
  end.
Tactic Notation "replace_type" uconstr(A) :=
  match goal with
  | |- TY ?n; ?Γ ⊢ ?e : ?B => replace B%ty with A%ty; cycle -1; first try by asimpl
  end.


Ltac simplify_list_elem :=
  simpl;
  repeat match goal with
         | |- ?x ∈ ?y :: ?l => apply elem_of_cons; first [left; reflexivity | right]
         | |- _ ∉ [] => apply not_elem_of_nil
         | |- _ ∉ _ :: _ => apply not_elem_of_cons; split
  end; try fast_done.
Ltac simplify_list_subseteq :=
  simpl;
  repeat match goal with
         | |- ?x :: _ ⊆ ?x :: _ => apply list_subseteq_cons_l
         | |- ?x :: _ ⊆ _ => apply list_subseteq_cons_elem; first solve [simplify_list_elem]
         | |- elements _ ⊆ elements _ => apply elements_subseteq; set_solver
         | |- [] ⊆ _ => apply list_subseteq_nil
         | |- ?x :b: _ ⊆ ?x :b: _ => apply list_subseteq_cons_binder
         (* NOTE: this might make the goal unprovable *)
         (*| |- elements _ ⊆ _ :: _ => apply list_subseteq_cons_r*)
         end;
  try fast_done.

(* Try to solve [is_closed] goals using a number of heuristics (that shouldn't make the goal unprovable) *)
Ltac simplify_closed :=
  simpl; intros;
  repeat match goal with
  | |- closed _ _ => unfold closed; simpl
  | |- Is_true (is_closed [] _) => first [assumption | done]
  | |- Is_true (is_closed _ (lang.subst _ _ _)) => rewrite subst_is_closed_nil; last solve[simplify_closed]
  | |- Is_true (is_closed ?X ?v) => assert_fails (is_evar X); eapply is_closed_weaken
  | |- Is_true (is_closed _ _) => eassumption
  | |- Is_true (_ && true) => rewrite andb_true_r
  | |- Is_true (true && _) => rewrite andb_true_l
  | |- Is_true (?a && ?a) => rewrite andb_diag
  | |- Is_true (_ && _)  => simpl; rewrite !andb_True; split_and!
  | |- _ ⊆ ?A => match type of A with | list _ => simplify_list_subseteq end
  | |- _ ∈ ?A => match type of A with | list _ => simplify_list_elem end
  | |- _ ≠ _ => congruence
  | H : closed _ _ |- _ => unfold closed in H; simpl in H
  | H: Is_true (_ && _) |- _ => simpl in H; apply andb_True in H
  | H : _ ∧ _ |- _ => destruct H
  | |- Is_true (bool_decide (_ ∈ _)) => apply bool_decide_pack; set_solver
  end; try fast_done.
