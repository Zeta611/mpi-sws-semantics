From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.base_logic Require Export invariants.
From semantics.pl.heap_lang Require Export primitive_laws_nolater.
From semantics.pl.heap_lang Require Import adequacy proofmode.


Module hoare.
  (* We make "ghost_state" an axiom for now to simplify the Coq development.
   In the future, we will quantify over it. *)
  Axiom ghost_state: heapGS heapΣ.
  #[export] Existing Instance ghost_state.

  (* the type of preconditions and postconditions *)
  Notation iProp := (iProp heapΣ).
  Implicit Types
    (P Q R: iProp)
    (φ ψ: Prop)
    (e: expr)
    (v: val).

  Lemma ent_equiv P Q :
    (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof. apply bi.equiv_entails. Qed.

  (* Rules for entailment *)
  Lemma ent_refl P:
    P ⊢ P.
  Proof. eauto. Qed.

  Lemma ent_trans P Q R:
    (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. by intros ->. Qed.

  (* NOTE: True = ⌜True⌝ *)

  (* NOTE: False = ⌜False⌝ *)

  Lemma ent_prove_pure P φ:
    φ → P ⊢ ⌜φ⌝.
  Proof. eauto. Qed.

  Lemma ent_assume_pure P Q φ:
    (P ⊢ ⌜φ⌝) →
    (φ → P ⊢ Q) →
    P ⊢ Q.
  Proof.
    iIntros (Hent Hpost) "P". iPoseProof (Hent with "P") as "%".
    by iApply Hpost.
  Qed.

  Lemma ent_and_elim_r P Q :
    P ∧ Q ⊢ Q.
  Proof.
    iIntros "[_ $]".
  Qed.

  Lemma ent_and_elim_l P Q :
    P ∧ Q ⊢ P.
  Proof.
    iIntros "[$ _ ]".
  Qed.

  Lemma ent_and_intro P Q R :
    (P ⊢ Q) →
    (P ⊢ R) →
    P ⊢ Q ∧ R.
  Proof.
    iIntros (HQ HR) "HP". iSplit.
    + by iApply HQ.
    + by iApply HR.
  Qed.

  Lemma ent_or_introl P Q :
    P ⊢ P ∨ Q.
  Proof. eauto. Qed.

  Lemma ent_or_intror P Q :
    Q ⊢ P ∨ Q.
  Proof. eauto. Qed.

  Lemma ent_or_elim P Q R :
    (P ⊢ R) →
    (Q ⊢ R) →
    P ∨ Q ⊢ R.
  Proof.
    iIntros (HP HQ) "[HP | HQ]"; [by iApply HP | by iApply HQ].
  Qed.

  Lemma ent_all_intro {X} P Φ :
    (∀ x : X, P ⊢ Φ x) →
    P ⊢ ∀ x : X, Φ x.
  Proof.
    iIntros (Hx) "HP". iIntros(x).
    by iApply Hx.
  Qed.

  Lemma ent_all_elim {X} (x : X) (Φ : _ → iProp) :
    (∀ x, Φ x) ⊢ Φ x.
  Proof. eauto. Qed.

  Lemma ent_exist_intro {X} (x : X) P Φ :
    (P ⊢ Φ x) →
    P ⊢ ∃ x, Φ x.
  Proof.
    iIntros (HP) "HP". iExists x. by iApply HP.
  Qed.

  Lemma ent_exist_elim {X} Φ Q :
    (∀ x : X, (Φ x ⊢ Q)) →
    (∃ x, Φ x) ⊢ Q.
  Proof.
    iIntros (HQ) "(%x & Hx)". by iApply HQ.
  Qed.

  (** Separating conjunction rules *)
  Lemma ent_sep_comm P Q:
    P ∗ Q ⊣⊢ Q ∗ P.
  Proof. iSplit; iIntros "[$ $]". Qed.

  Lemma ent_sep_assoc P1 P2 P3:
    P1 ∗ (P2 ∗ P3) ⊣⊢ (P1 ∗ P2) ∗ P3.
  Proof.
    iSplit.
    - iIntros "[$ [$ $]]".
    - iIntros "[[$ $] $]".
  Qed.

  Lemma ent_sep_split P P' Q Q':
    (P ⊢ Q) → (P' ⊢ Q') →  (P ∗ P') ⊢ Q ∗ Q'.
  Proof.
    by intros -> ->.
  Qed.

  Lemma ent_sep_true P :
    P ⊢ True ∗ P.
  Proof.
    iIntros "$".
  Qed.

  Lemma ent_sep_weaken P Q:
    P ∗ Q ⊢ P.
  Proof.
    iIntros "[$ _]".
  Qed.

  Lemma ent_pointsto_sep l v w :
    l ↦ v ∗ l ↦ w ⊢ False.
  Proof.
    iIntros "[Ha Hb]".
    iPoseProof (mapsto_ne with "Ha Hb") as "%Hneq".
    done.
  Qed.

  Lemma ent_exists_sep {X} (Φ : X → iProp) P :
    (∃ x : X, Φ x) ∗ P ⊢ (∃ x : X, Φ x ∗ P).
  Proof.
    iIntros "((%x & Hx) & Hp)". eauto with iFrame.
  Qed.

  (** Magic wand rules *)
  Lemma ent_wand_intro P Q R :
    (P ∗ Q ⊢ R) →
    (P ⊢ Q -∗ R).
  Proof.
    iIntros (Hr) "HP HQ". iApply Hr. iFrame.
  Qed.

  Lemma ent_wand_elim P Q R :
    (P ⊢ Q -∗ R) →
    P ∗ Q ⊢ R.
  Proof.
    iIntros (Hr) "[HP HQ]". iApply (Hr with "HP HQ").
  Qed.


  (** Hoare rules *)
  Implicit Types
    (Φ Ψ: val → iProp).
  Definition hoare P (e: expr) Φ := P ⊢ WP e {{ Φ }}.

  Global Notation "{{ P } } e {{ Φ } }" := (hoare P%I e%E Φ%I)
    (at level 20, P, e, Φ at level 200,
    format "{{  P  } }  e  {{  Φ  } }") : stdpp_scope.

  Global Notation "{{ P } } e {{ v , Q } }" := (hoare P%I e%E (λ v, Q)%I)
    (at level 20, P, e, Q at level 200,
    format "{{  P  } }  e  {{  v ,  Q  } }") : stdpp_scope.

  (* Rules for Hoare triples *)
  Lemma hoare_value v Φ:
    {{ Φ v }} v {{ Φ }}.
  Proof.
    iIntros "H". by iApply wp_value.
  Qed.

  Lemma hoare_con P Q Φ Ψ e:
    (P ⊢ Q) →
    (∀ v, Ψ v ⊢ Φ v) →
    {{ Q }} e {{ Ψ }} →
    {{ P }} e {{ Φ }}.
  Proof.
    iIntros (Hpre Hpost Hhoare) "P".
    iApply wp_mono; eauto.
    iApply Hhoare. by iApply Hpre.
  Qed.


  Lemma hoare_bind K P Φ Ψ e:
    {{ P }} e {{ Ψ }} →
    (∀ v, {{ Ψ v }} fill K (Val v) {{ Φ }}) →
    {{ P }} (fill K e) {{ Φ }}.
  Proof.
    iIntros (Hexpr Hctx) "P".
    iApply wp_bind'.
    iApply wp_mono; eauto.
    by iApply Hexpr.
  Qed.

  Lemma hoare_pure P φ Φ e:
    (P ⊢ ⌜φ⌝) →
    (φ → {{ P }} e {{ Φ }}) →
    {{ P }} e {{ Φ }}.
  Proof.
    intros Hent Hhoare.
    iIntros "P". iPoseProof (Hent with "P") as "%".
    by iApply Hhoare.
  Qed.

  Lemma hoare_exist_pre {X} (Φ : X → _) Ψ e :
    (∀ x : X, {{ Φ x }} e {{ Ψ }}) →
    {{ ∃ x : X, Φ x }} e {{ Ψ }}.
  Proof.
    iIntros (Hs) "(%x & Hx)". by iApply Hs.
  Qed.

  Lemma hoare_pure_step P Ψ e1 e2 :
    pure_step e1 e2 →
    {{ P }} e2 {{ Ψ }} →
    {{ P }} e1 {{ Ψ }}.
  Proof.
    iIntros (Hpure He2) "HP".
    iApply (lifting.wp_pure_step_later _ _ _ _ _ True).
    - intros _. econstructor 2; [done | econstructor].
    - done.
    - iNext. iApply He2. done.
  Qed.

  Lemma hoare_pure_steps P Ψ e1 e2 :
    rtc pure_step e1 e2 →
    {{ P }} e2 {{ Ψ }} →
    {{ P }} e1 {{ Ψ }}.
  Proof.
    induction 1; eauto using hoare_pure_step.
  Qed.

  (** Pure step rules *)
  Lemma PureExec_1_equiv e1 e2 :
    (∃ ϕ, ϕ ∧ PureExec ϕ 1 e1 e2) ↔
    pure_step e1 e2.
  Proof.
    split.
    - intros (ϕ & H & Hp). by specialize (Hp H) as ?%nsteps_once_inv.
    - intros Hp. exists True. split; first done.
      intros _. econstructor; first done. constructor.
  Qed.

  Lemma PureExec_1_elim (ϕ : Prop) e1 e2 :
    ϕ → PureExec ϕ 1 e1 e2 →
    pure_step e1 e2.
  Proof.
    intros H Hp. apply PureExec_1_equiv. eauto.
  Qed.

  Lemma pure_step_fill K (e1 e2: expr):
    pure_step e1 e2 → pure_step (fill K e1) (fill K e2).
  Proof.
    intros Hp. apply PureExec_1_equiv.
    exists True. split; first done.
    apply pure_exec_ctx; first apply _.
    intros _. apply nsteps_once. done.
  Qed.

  Lemma rtc_pure_step_fill K (e1 e2: expr):
    rtc pure_step e1 e2 → rtc pure_step (fill K e1) (fill K e2).
  Proof.
    induction 1; first reflexivity.
    econstructor; last done. by eapply pure_step_fill.
  Qed.
  Lemma pure_step_add (n m : Z) :
    pure_step (#n + #m) (#(n + m)).
  Proof.
    eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_sub (n m : Z) :
    pure_step (#n - #m) (#(n - m)).
  Proof.
    eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_mul (n m : Z) :
    pure_step (#n * #m) (#(n * m)).
  Proof.
    eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_quot (n m : Z) :
    m ≠ 0 → pure_step (#n `quot` #m) (#(Z.quot n m)).
  Proof.
    intros _. eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_eq (n m : Z) :
    n = m → pure_step (#n = #m) #true.
  Proof.
    intros. eapply PureExec_1_elim; last apply _.
    unfold bin_op_eval. simpl.
    rewrite bool_decide_eq_true_2; subst; done.
  Qed.
  Lemma pure_step_neq (n m : Z) :
    n ≠ m → pure_step (#n = #m) #false.
  Proof.
    intros. eapply PureExec_1_elim; last apply _.
    unfold bin_op_eval. simpl.
    rewrite bool_decide_eq_false_2; first done.
    intros [= Heq]; done.
  Qed.
  Lemma pure_step_beta f x e v :
    pure_step ((rec: f x := e)%V v) (subst' x v (subst' f (rec: f x := e) e)).
  Proof.
    eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_if_true e1 e2 :
    pure_step (if: #true then e1 else e2) e1.
  Proof.
    eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_if_false e1 e2 :
    pure_step (if: #false then e1 else e2) e2.
  Proof.
    eapply PureExec_1_elim; last apply _. done.
  Qed.
  Lemma pure_step_match_injl v x1 x2 e1 e2 :
    pure_step (match: InjLV v with InjL x1 => e1 | InjR x2 => e2 end) ((λ: x1, e1) v).
  Proof.
    by eapply PureExec_1_elim; last apply _.
  Qed.
  Lemma pure_step_match_injr v x1 x2 e1 e2 :
    pure_step (match: InjRV v with InjL x1 => e1 | InjR x2 => e2 end) ((λ: x2, e2) v).
  Proof.
    by eapply PureExec_1_elim; last apply _.
  Qed.
  Lemma pure_step_fst v1 v2 :
    pure_step (Fst (v1, v2)%V) v1.
  Proof.
    by eapply PureExec_1_elim; last apply _.
  Qed.
  Lemma pure_step_snd v1 v2 :
    pure_step (Snd (v1, v2)%V) v2.
  Proof.
    by eapply PureExec_1_elim; last apply _.
  Qed.

  (** In our Coq formalization, a bit of an additional effort arises due to the handling of values:
    values are always represented using the [Val] constructor, and fully reduced expressions take an additional
    step of computation to get to a [Val].
    See for instance the constructors [PairS], [InjLS], [InjRS].

    Therefore, we need an additional rule, [pure_step_val].
   *)
  Lemma pure_step_val_fun f x e :
    rtc pure_step (rec: f x := e)%E (rec: f x := e)%V.
  Proof.
    eapply rtc_nsteps. exists 1. eapply pure_exec. done.
  Qed.
  Lemma pure_step_val_pair e1 e2 v1 v2 :
    rtc pure_step e1 v1 →
    rtc pure_step e2 v2 →
    rtc pure_step (e1, e2)%E (v1, v2)%V.
  Proof.
    etransitivity; first etransitivity.
    + by eapply rtc_pure_step_fill with (K := [PairRCtx _]).
    + by eapply rtc_pure_step_fill with (K := [PairLCtx _]).
    + simpl. eapply rtc_nsteps. exists 1. eapply pure_exec. done.
  Qed.
  Lemma pure_step_val_injl e1 v1 :
    rtc pure_step e1 v1 →
    rtc pure_step (InjL e1) (InjLV v1).
  Proof.
    etransitivity.
    + by eapply rtc_pure_step_fill with (K := [InjLCtx]).
    + simpl. eapply rtc_nsteps. exists 1. eapply pure_exec. done.
  Qed.
  Lemma pure_step_val_injr e1 v1 :
    rtc pure_step e1 v1 →
    rtc pure_step (InjR e1) (InjRV v1).
  Proof.
    etransitivity.
    + by eapply rtc_pure_step_fill with (K := [InjRCtx]).
    + simpl. eapply rtc_nsteps. exists 1. eapply pure_exec. done.
  Qed.
  Local Hint Resolve pure_step_val_fun pure_step_val_pair pure_step_val_injl pure_step_val_injr : core.

  (** For convenience: a lemma to cover all of these cases, with a precondition that
    can be easily solved by eatuto *)
  Inductive expr_is_val : expr → val → Prop :=
    | expr_is_val_base v:
      expr_is_val (Val v) v
    | expr_is_val_fun f x e:
      expr_is_val (rec: f x := e)%E (rec: f x := e)%V
    | expr_is_val_pair e1 e2 v1 v2:
      expr_is_val e1 v1 →
      expr_is_val e2 v2 →
      expr_is_val (e1, e2)%E (v1, v2)%V
    | expr_is_val_inj_l e v:
      expr_is_val e v →
      expr_is_val (InjL e)%E (InjLV v)%V
    | expr_is_val_inj_r e v:
      expr_is_val e v →
      expr_is_val (InjR e)%E (InjRV v)%V.
  #[export]
  Hint Constructors expr_is_val : core.
  Lemma expr_is_val_of_val v :
    expr_is_val (of_val v) v.
  Proof.
    destruct v; simpl; constructor.
  Qed.
  #[export]
  Hint Resolve expr_is_val_of_val : core.

  Lemma pure_step_val e v:
    expr_is_val e v →
    rtc pure_step e v.
  Proof.
    intros Hexpr. induction Hexpr; eauto. econstructor.
  Qed.

  Lemma hoare_new v :
    {{ True }} ref v {{ w, ∃ l : loc, ⌜w = #l⌝ ∗ l ↦ v }}.
  Proof.
    iIntros "_". wp_alloc l as "Hl". iApply wp_value. eauto with iFrame.
  Qed.

  Lemma hoare_load l v:
    {{ l ↦ v }} ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }}.
  Proof.
    iIntros "Hl". wp_load. iApply wp_value. iFrame. done.
  Qed.

  Lemma hoare_store l (v w: val):
    {{ l ↦ v }} #l <- w {{ _, l ↦ w }}.
  Proof.
    iIntros "Hl". wp_store. iApply wp_value. iFrame.
  Qed.

  Lemma hoare_frame P F Φ e:
    {{ P }} e {{ Φ }} →
    {{ P ∗ F }} e {{ v, Φ v ∗ F }}.
  Proof.
    iIntros (Hhoare) "[P $]". by iApply Hhoare.
  Qed.

  (* Prevent printing of magic wands *)
  Notation "P -∗ Q" := (bi_entails P Q) (only parsing) : stdpp_scope.


  (** Weakest precondition rules *)
  Lemma ent_wp_value Φ v :
    Φ v ⊢ WP of_val v {{ w, Φ w }}.
  Proof.
    iIntros "Hv". by iApply wp_value.
  Qed.

  Lemma ent_wp_wand' Φ Ψ e :
    (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Φ }} -∗ WP e {{ Ψ }}.
  Proof.
    iIntros "Hp Hwp". iApply (wp_wand with "Hwp Hp").
  Qed.

  Lemma ent_wp_wand Φ Ψ e :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e {{ Φ }} ⊢ WP e {{ Ψ }}.
  Proof.
    iIntros "[Hp Hwp]". iApply (wp_wand with "Hwp Hp").
  Qed.

  Lemma ent_wp_bind e K Φ :
    WP e {{ v, WP fill K (Val v) {{ Φ }} }} ⊢ WP fill K e {{ Φ }}.
  Proof.
    iApply wp_bind.
  Qed.

  Lemma ent_wp_pure_step e e' Φ :
    pure_step e e' →
    WP e' {{ Φ }} ⊢ WP e {{ Φ }}.
  Proof.
    iIntros (Hpure) "Hwp". iApply (lifting.wp_pure_step_later _ _ _ _ _ True 1); last iApply "Hwp"; last done.
    intros _. apply nsteps_once. apply Hpure.
  Qed.

  Lemma ent_wp_new v Φ :
    (∀ l : loc, l ↦ v -∗ Φ #l) ⊢ WP ref (Val v) {{ Φ }}.
  Proof.
    iIntros "Hs". wp_alloc l as "Hl". wp_value_head. by iApply "Hs".
  Qed.

  Lemma ent_wp_load l v Φ :
    l ↦ v ∗ (l ↦ v -∗ Φ v) ⊢ WP !#l {{ Φ }}.
  Proof.
    iIntros "(Hl & Hp)". wp_load. wp_value_head. by iApply "Hp".
  Qed.

  Lemma ent_wp_store l v w Φ :
    l ↦ w ∗ (l ↦ v -∗ Φ #()) ⊢ WP #l <- Val v {{ Φ }}.
  Proof.
    iIntros "(Hl & Hp)". wp_store. wp_value_head. by iApply "Hp".
  Qed.


  (** Persistency *)
  Lemma ent_pers_dup P :
    □ P ⊢ (□ P) ∗ (□ P).
  Proof.
    iIntros "#HP". eauto.
  Qed.

  Lemma ent_pers_elim P :
    □ P ⊢ P.
  Proof.
    iIntros "#$".
  Qed.

  Lemma ent_pers_mono P Q :
    (P ⊢ Q) →
    □ P ⊢ □ Q.
  Proof.
    iIntros (HPQ) "#HP !>". by iApply HPQ.
  Qed.

  Lemma ent_pers_pure (ϕ : Prop) :
    ⌜ϕ⌝ ⊢ (□ ⌜ϕ⌝ : iProp).
  Proof.
    iIntros "#$".
  Qed.

  Lemma ent_pers_and_sep P Q :
    (□ P) ∧ Q ⊢ (□ P) ∗ Q.
  Proof.
    iIntros "(#$ & $)".
  Qed.

  Lemma ent_pers_idemp P :
    □ P ⊢ □ □ P.
  Proof.
    iIntros "#$".
  Qed.

  Lemma ent_pers_all {X} (Φ : X → iProp) :
    (∀ x : X, □ Φ x) ⊢ □ ∀ x : X, Φ x.
  Proof.
    iIntros "#Hx" (x). iApply "Hx".
  Qed.

  Lemma ent_pers_exists {X} (Φ : X → iProp) :
    (□ ∃ x : X, Φ x) ⊢ ∃ x : X, □ Φ x.
  Proof.
    iIntros "(%x & #Hx)". iExists x. done.
  Qed.

  (** Invariants *)
  Implicit Type
    (F : iProp)
    (N : namespace)
    (E : coPset)
  .
  Lemma ent_inv_pers F N :
    inv N F ⊢ □ inv N F.
  Proof.
    iIntros "#$".
  Qed.
  Lemma ent_inv_alloc F P N E e Φ :
    (P ∗ inv N F ⊢ WP e @ E {{ Φ }}) →
    (P ∗ F ⊢ WP e @ E {{ Φ }}).
  Proof.
    iIntros (Ha) "[HP HF]".
    iMod (inv_alloc N with "HF") as "#Hinv".
    iApply Ha. iFrame "Hinv ∗".
  Qed.
  Lemma inv_alloc N F E e Φ :
    F -∗
    (inv N F -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "HF Hs".
    iMod (inv_alloc N with "HF") as "#Hinv".
    by iApply "Hs".
  Qed.

  (** We require a sidecondition here, namely that [F] is "timeless". All propositions we have seen up to now are in fact timeless.
    We will see propositions that do not satisfy this requirement and which need a stronger rule for invariants soon.
  *)
  Lemma ent_inv_open `{!Timeless F} P N E e Φ :
    (P ∗ F ⊢ WP e @ (E ∖ ↑N) {{ v, F ∗ Φ v }}) →
    ↑N ⊆ E →
    (P ∗ inv N F ⊢ WP e @ E {{ Φ }}).
  Proof.
    iIntros (Ha Hincl) "(HP & #Hinv)".
    iMod (inv_acc_timeless with "Hinv") as "(HF & Hcl)"; first done.
    iApply wp_fupd'. iApply wp_wand_r.
    iSplitR "Hcl". { iApply Ha. iFrame. }
    iIntros (v) "[HF Hphi]". iMod ("Hcl" with "HF"). done.
  Qed.
  Lemma inv_open `{!Timeless F} N E e Φ :
    ↑N ⊆ E →
    inv N F -∗
    (F -∗ WP e @ (E ∖ ↑N) {{ v, F ∗ Φ v }})%I -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hincl) "#Hinv Hs".
    iMod (inv_acc_timeless with "Hinv") as "(HF & Hcl)"; first done.
    iApply wp_fupd'. iApply wp_wand_r.
    iSplitR "Hcl". { iApply "Hs". iFrame. }
    iIntros (v) "[HF Hphi]". iMod ("Hcl" with "HF"). done.
  Qed.


  (** Later *)
  Lemma ent_later_intro P :
    P ⊢ ▷ P.
  Proof.
    iIntros "$".
  Qed.

  Lemma ent_later_mono P Q :
    (P ⊢ Q) →
    (▷ P ⊢ ▷ Q).
  Proof.
    iIntros (Hs) "HP!>". by iApply Hs.
  Qed.

  Lemma ent_löb P :
    (▷ P ⊢ P) →
    True ⊢ P.
  Proof.
    iIntros (Hs) "_".
    iLöb as "IH". by iApply Hs.
  Qed.

  Lemma ent_later_sep P Q :
    ▷ (P ∗ Q) ⊣⊢ (▷ P) ∗ (▷ Q).
  Proof.
    iSplit; iIntros "[$ $]".
  Qed.

  Lemma ent_later_exists `{Inhabited X} (Φ : X → iProp) :
    (▷ (∃ x : X, Φ x)) ⊣⊢ ∃ x : X, ▷ Φ x.
  Proof. apply bi.later_exist. Qed.

  Lemma ent_later_all {X} (Φ : X → iProp) :
    ▷ (∀ x : X, Φ x) ⊣⊢ ∀ x : X, ▷ Φ x.
  Proof. apply bi.later_forall. Qed.

  Lemma ent_later_pers P :
    ▷ □ P ⊣⊢ □ ▷ P.
  Proof.
    iSplit; iIntros "#H !> !>"; done.
  Qed.

  Lemma ent_later_wp_pure_step e e' Φ :
    pure_step e e' →
    ▷ WP e' {{ Φ }} ⊢ WP e {{ Φ }}.
  Proof.
    iIntros (Hpure%PureExec_1_equiv) "Hwp".
    destruct Hpure as (ϕ & Hphi & Hpure).
    iApply (lifting.wp_pure_step_later _ _ _ _ _ _ 1); done.
  Qed.

  Lemma ent_later_wp_new v Φ :
    ▷ (∀ l : loc, l ↦ v -∗ Φ #l) ⊢ WP ref v {{ Φ }}.
  Proof.
    iIntros "Hp". wp_alloc l as "Hl". iApply wp_value. by iApply "Hp".
  Qed.

  Lemma ent_later_wp_load l v Φ :
    l ↦ v ∗ ▷ (l ↦ v -∗ Φ v) ⊢ WP ! #l {{ Φ }}.
  Proof.
    iIntros "[Hl Hp]". wp_load. iApply wp_value. by iApply "Hp".
  Qed.

  Lemma ent_later_wp_store l v w Φ :
    l ↦ v ∗ ▷ (l ↦ w -∗ Φ #()) ⊢ WP #l <- w {{ Φ }}.
  Proof.
    iIntros "[Hl Hp]". wp_store. iApply wp_value. by iApply "Hp".
  Qed.
End hoare.

Module impred_invariants.
  Import hoare.
Implicit Type
  (F : iProp)
  (N : namespace)
  (E : coPset)
.

Lemma ent_inv_open P F N E e Φ :
  (P ∗ ▷ F ⊢ WP e @ (E ∖ ↑N) {{ v, ▷ F ∗ Φ v }}) →
  ↑N ⊆ E →
  (P ∗ inv N F ⊢ WP e @ E {{ Φ }}).
Proof.
  iIntros (Ha Hincl) "(HP & #Hinv)".
  iMod (inv_acc with "Hinv") as "(HF & Hcl)"; first done.
  iApply wp_fupd'. iApply wp_wand_r.
  iSplitR "Hcl". { iApply Ha. iFrame. }
  iIntros (v) "[HF Hphi]". iMod ("Hcl" with "HF"). done.
Qed.
Lemma inv_open N E F e Φ :
  ↑N ⊆ E →
  inv N F -∗
  (▷ F -∗ WP e @ (E ∖ ↑N) {{ v, ▷ F ∗ Φ v }})%I -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (Hincl) "#Hinv Hs".
  iMod (inv_acc with "Hinv") as "(HF & Hcl)"; first done.
  iApply wp_fupd'. iApply wp_wand_r.
  iSplitR "Hcl". { iApply "Hs". iFrame. }
  iIntros (v) "[HF Hphi]". iMod ("Hcl" with "HF"). done.
Qed.
End impred_invariants.
