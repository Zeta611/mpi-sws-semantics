From stdpp Require Import prelude.
From iris Require Import prelude.
From semantics.stlc_extended Require Import lang.
From semantics.lib Require Import maps.

Fixpoint subst_map (xs : gmap string expr) (e : expr) : expr :=
  match e with
  | Lit l => Lit l
  | Var y => match xs !! y with Some es => es | _ =>  Var y end
  | App e1 e2 => App (subst_map xs e1) (subst_map xs e2)
  | Lam x e => Lam x (subst_map (binder_delete x xs) e)
  | BinOp op e1 e2 => BinOp op (subst_map xs e1) (subst_map xs e2)
  | Pair e1 e2 => Pair (subst_map xs e1) (subst_map xs e2)
  | Fst e => Fst (subst_map xs e)
  | Snd e => Snd (subst_map xs e)
  | InjL e => InjL (subst_map xs e)
  | InjR e => InjR (subst_map xs e)
  | Case e e1 e2 => Case (subst_map xs e) (subst_map xs e1) (subst_map xs e2)
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  induction e; simpl; f_equal; eauto.
  all: destruct x; simpl; [done | by rewrite !delete_empty..].
Qed.

Lemma subst_map_is_closed X e xs :
  is_closed X e →
  (∀ x : string, x ∈ dom xs → x ∉ X) →
  subst_map xs e = e.
Proof.
  intros Hclosed Hd.
  induction e in xs, X, Hd, Hclosed |-*; simpl in *;try done.
  all: repeat match goal with
  | H : Is_true (_ && _)  |- _ => apply andb_True in H as [ ? ? ]
              end.
  { (* Var *)
    apply bool_decide_spec in Hclosed.
    assert (xs !! x = None) as ->; last done.
    destruct (xs !! x) as [s | ] eqn:Helem; last done.
    exfalso; eapply Hd; last apply Hclosed.
    apply elem_of_dom; eauto.
  }
  { (* lambdas *)
    erewrite IHe; [done | done |].
    intros y. destruct x as [ | x]; first apply Hd.
    simpl.
    rewrite dom_delete elem_of_difference not_elem_of_singleton.
    intros [Hnx%Hd Hneq]. rewrite elem_of_cons. intros [? | ?]; done.
  }
  (* all other cases *)
  all: repeat match goal with
       | H : ∀ _ _, _ → _ → subst_map _ _ = _ |- _ => erewrite H; clear H
       end; done.
Qed.

Lemma subst_map_subst map x (e e' : expr) :
  is_closed [] e' →
  subst_map map (subst x e' e) = subst_map (<[x:=e']>map) e.
Proof.
  intros He'.
  revert x map; induction e; intros xx map; simpl;
  try (f_equal; eauto).
  - case_decide.
    + simplify_eq/=. rewrite lookup_insert.
      rewrite (subst_map_is_closed []); [done | apply He' | ].
      intros ? ?. apply not_elem_of_nil.
    + rewrite lookup_insert_ne; done.
  - destruct x; simpl; first done.
    + case_decide.
      * simplify_eq/=. by rewrite delete_insert_delete.
      * rewrite delete_insert_ne; last by congruence. done.
Qed.

Definition subst_is_closed (X : list string) (map : gmap string expr) :=
  ∀ x e, map !! x = Some e → closed X e.
Lemma subst_is_closed_subseteq X map1 map2 :
  map1 ⊆ map2 → subst_is_closed X map2 → subst_is_closed X map1.
Proof.
  intros Hsub Hclosed2 x e Hl. eapply Hclosed2, map_subseteq_spec; done.
Qed.

Lemma subst_subst_map x es map e :
  subst_is_closed [] map →
  subst x es (subst_map (delete x map) e) =
  subst_map (<[x:=es]>map) e.
Proof.
  revert map es x; induction e; intros map v0 xx Hclosed; simpl;
  try (f_equal; eauto).
  - destruct (decide (xx=x)) as [->|Hne].
    + rewrite lookup_delete // lookup_insert //. simpl.
      rewrite decide_True //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (_ !! x) as [rr|] eqn:Helem.
      * apply Hclosed in Helem.
        by apply subst_is_closed_nil.
      * simpl. rewrite decide_False //.
  - destruct x; simpl; first by auto.
    case_decide.
    + simplify_eq. rewrite delete_idemp delete_insert_delete. done.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_commute. apply IHe.
      eapply subst_is_closed_subseteq; last done.
      apply map_delete_subseteq.
Qed.

Lemma subst'_subst_map b (es : expr) map e :
  subst_is_closed [] map →
  subst' b es (subst_map (binder_delete b map) e) =
  subst_map (binder_insert b es map) e.
Proof.
  destruct b; first done.
  apply subst_subst_map.
Qed.

Lemma closed_subst_weaken e map X Y :
  subst_is_closed [] map →
  (∀ x, x ∈ X → x ∉ dom map → x ∈ Y) →
  closed X e →
  closed Y (subst_map map e).
Proof.
  induction e in X, Y, map |-*; rewrite /closed; simpl; intros Hmclosed Hsub Hcl; first done.
  all: repeat match goal with
  | H : Is_true (_ && _)  |- _ => apply andb_True in H as [ ? ? ]
              end.
  { (* vars *)
    destruct (map !! x) as [es | ] eqn:Heq.
    + apply is_closed_weaken_nil. by eapply Hmclosed.
    + apply bool_decide_pack. apply Hsub; first by eapply bool_decide_unpack.
      by apply not_elem_of_dom.
  }
  { (* lambdas *)
    eapply IHe; last done.
    + eapply subst_is_closed_subseteq; last done.
      destruct x; first done. apply map_delete_subseteq.
    + intros y. destruct x as [ | x]; first by apply Hsub.
      rewrite !elem_of_cons. intros [-> | Hy] Hn; first by left.
      destruct (decide (y = x)) as [ -> | Hneq]; first by left.
      right. eapply Hsub; first done. set_solver.
  }
  (* all other cases *)
  all: repeat match goal with
         | |- Is_true (_ && _) => apply andb_True; split
              end.
  all: naive_solver.
Qed.
