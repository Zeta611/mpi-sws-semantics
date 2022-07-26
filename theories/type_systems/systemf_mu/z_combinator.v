From iris Require Import prelude.
From semantics.ts.systemf_mu Require Import lang notation parallel_subst types tactics logrel pure.
From semantics.lib Require Import maps.

Lemma sem_expr_rel_lambda_val A B δ k x e :
  is_closed [] (Lam x e) →
  ℰ (A → B) δ k (Lam x e) →
  𝒱 (A → B) δ k (LamV x e).
Proof.
  intros Hcl.
  destruct k as [ | k]; first last.
  { apply (sem_expr_rel_of_val _ _ _ (LamV x e)). lia. }
  intros _. simp type_interp.
  eexists _, _; split_and!; [done | done | ].
  intros v' kd _. assert (0 - kd = 0) as -> by lia.
  (* NOTE: this crucially uses that the expression relation at zero is trivial *)
  apply sem_expr_rel_zero_trivial.
Qed.

Section Z.
Context (e : expr).

Definition g : val := λ: "f", let: "f" := λ: "x", "f" "f" "x" in λ: "x", e.
Definition Z : val := λ: "x", g g "x".

Lemma Z_safe n (Γ : typing_context) (A B : type) :
  Γ !! "x" = None →
  Γ !! "f" = None →
  is_closed ("f" :: "x" :: elements (dom Γ)) e →
  TY n; (<["f" := (A → B)%ty]> (<["x" := A]> Γ)) ⊨ e : B →
  TY n; Γ ⊨ Z : (A → B).
Proof.
  intros ?? Hcl He θ δ k Hctx.
  simpl.
  rewrite lookup_delete_ne; last done. rewrite !lookup_delete.
  rewrite delete_idemp.
  rewrite (delete_commute _ "x" "f").
  rewrite delete_idemp.
  set (θ' := (delete (M := gmap.gmap _ _) "f" (delete "x" (M := gmap.gmap _ _) θ))).
  specialize (sem_context_rel_dom_eq _ _ _ _ Hctx) as Hdom.
  assert (is_closed ["x"; "f"; "f"; "x"] (subst_map θ' e)).
  { (* boring, ignore this *)
    apply is_closed_subst_map.
    - eapply subst_is_closed_weaken_nil.
      eapply (subst_is_closed_subseteq _ _ θ); last by eapply sem_context_rel_closed.
      subst θ'. etrans; eapply delete_subseteq.
    - eapply is_closed_weaken; first done.
      apply sem_context_rel_subset in Hctx.
      simplify_list_subseteq.
      subst θ'.
      apply stdpp.sets.elem_of_subseteq.
      intros x Hel%elem_of_elements.
      destruct (decide (x = "x")) as [ -> | ?]; first simplify_list_elem.
      destruct (decide (x = "f")) as [ -> | ?]; first simplify_list_elem.
      do 4 right. apply elem_of_elements.
      rewrite !dom_delete -Hdom !elem_of_difference !elem_of_singleton //.
  }

  (* we initiate Löb induction *)
  set (g' := (λ: "f", let: "f" := λ: "x", "f" "f" "x" in λ: "x", subst_map θ' e)%E).
  induction k as [ k IH] using lt_wf_ind.

  apply (sem_val_expr_rel _ _ _ (LamV _ _)).
  simp type_interp. eexists _, _. split_and!; [done |simplify_closed | ].
  intros v' kd Hv'. simpl. fold g'.
  eapply semantic_app; first last.
  { apply sem_val_expr_rel. done. }

  eapply expr_det_steps_closure.
  { econstructor 2.
    { unfold g'. apply det_step_beta. done. }
    simpl. fold g'.
    econstructor 2.
    { apply det_step_beta. done. }
    simpl.
    econstructor.
  }
  apply (sem_val_expr_rel _ _ _ (LamV _ _)).

  simp type_interp. eexists _, _. split_and!; [done | | ].
  { apply is_closed_subst; first by simplify_closed.
    simpl. eapply is_closed_weaken; first done.
    simplify_list_subseteq.
  }
  intros v2 kd2 Hv2.

  set (θ'' := (<[ "x" := of_val v2 ]> $ <["f" := (λ: "x", g' g' "x")]> $ θ)%E).
  replace (subst' "x" _ _) with (subst_map θ'' e).
  2: {
    (* boring, ignore this *)
    rewrite subst_subst_map.
    2: eapply subst_is_closed_subseteq; [ apply delete_subseteq | by eapply sem_context_rel_closed ].
    rewrite -delete_insert_ne; last done.
    simpl. rewrite subst_subst_map; first done.

    eapply subst_is_closed_insert; first by simplify_closed.
    eapply subst_is_closed_subseteq; [ apply delete_subseteq | by eapply sem_context_rel_closed].
  }
  eapply He.

  rewrite insert_commute; last done.
  econstructor.
  { done. }
  apply (sem_context_rel_insert _ _ _ _ (LamV _ _)).
  { eapply sem_expr_rel_lambda_val; first by simplify_closed.
    destruct k.
    { simpl. replace (0 - kd2) with 0 by lia. apply sem_expr_rel_zero_trivial. }
    eapply IH. lia.
    eapply sem_context_rel_mono; last done. lia.
  }
  eapply sem_context_rel_mono; last done. lia.
Qed.
End Z.


(** Variant for the combinator we saw earlier in the lecture. *)
Section fixa.
Definition Fix' : val := λ: "z" "y", "y" (λ: "x", "z" "z" "y" "x").
Definition Fix (s : val) : val := λ: "x", Fix' Fix' s "x".
Arguments Fix : simpl never.

Lemma Z_safe' (A B : type) (s : val) :
  closed [] s →
  TY 0; ∅ ⊨ s : ((A → B) → A → B) →
  TY 0; ∅ ⊨ (Fix s) : (A → B).
Proof.
  intros Hcl HF θ δ k Hctx.
  simpl.
  rewrite !lookup_delete.
  rewrite (delete_commute _ "x" "y").
  rewrite (delete_commute _ "x" "z").
  rewrite !lookup_delete.
  rewrite (delete_commute _ "y" "z").
  rewrite delete_idemp.
  rewrite !lookup_delete.
  erewrite subst_map_is_closed; [ | done | ].
  2: { intros. apply not_elem_of_nil. }

  apply (sem_val_expr_rel _ _ _ (LamV _ _)).

  simp type_interp. eexists _, _. split_and!; [done |simplify_closed | ].
  intros v' kd Hv'. simpl.
  eapply semantic_app; first last.
  { apply sem_val_expr_rel. done. }
  simpl. rewrite subst_is_closed_nil; last done.

  eapply semantic_app; first last.
  { erewrite <-(subst_map_is_closed _ (of_val s) θ); [ | done | ].
    - eapply HF. eapply sem_context_rel_mono; last done. lia.
    - intros. apply not_elem_of_nil.
  }

  (* Factor this into a separate lemma ? *)
  clear Hv' v' HF. generalize (k - kd) => k0.
  clear kd.
  induction k0 as [ k0 IH] using lt_wf_ind.

  eapply expr_det_steps_closure.
  { do_det_step. simpl. econstructor. }
  apply (sem_val_expr_rel _ _ _ (LamV _ _)).

  simp type_interp. eexists _, _. split_and!; [done | | ].
  { done. }
  intros vF kd2 Hv2. simpl.
  generalize Hv2 => HF.

  simp type_interp in Hv2.
  destruct Hv2 as (x & e & -> & ? & Hv2).
  eapply expr_det_steps_closure. { do_det_step. econstructor. }
  eapply (Hv2 (LamV _ _)).

  simp type_interp. eexists _, _. split_and!; [done |simplify_closed | ].
  intros v' kd Hv'. simpl.
  eapply semantic_app; first last.
  { apply sem_val_expr_rel. done. }
  simpl.
  replace (if decide (BNamed "x" = x) then e else lang.subst "x" v' e)%E with e.
  2: { destruct decide; first done.
      erewrite lang.subst_is_closed; [done | done | ].
      destruct x; simpl; simplify_list_elem; congruence.
  }

  eapply semantic_app; first last.
  { eapply (sem_val_expr_rel  _ _ _ (LamV _ _)).
    eapply val_rel_mono; last done. lia.
  }
  destruct k0 as [ | k0]; last (eapply IH; lia).
  simpl. rewrite Nat.sub_0_l.
  eapply sem_expr_rel_zero_trivial.
Qed.

End fixa.
