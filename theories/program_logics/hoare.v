From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From semantics.pl Require Export hoare_lib.

Import hoare.
Implicit Types
  (P Q: iProp)
  (φ ψ: Prop)
  (e: expr)
  (v: val).

(** * Hoare logic *)

(** Entailment rules *)
(*Check ent_equiv.*)
(*Check ent_refl.*)
(*Check ent_trans.*)
(* NOTE: True = ⌜True⌝ *)
(* NOTE: False = ⌜False⌝ *)
(*Check ent_prove_pure.*)
(*Check ent_assume_pure.*)
(*Check ent_and_elim_r.*)
(*Check ent_and_elim_l.*)
(*Check ent_and_intro.*)
(*Check ent_or_introl.*)
(*Check ent_or_intror.*)
(*Check ent_or_elim.*)
(*Check ent_all_intro.*)
(*Check ent_all_elim.*)
(*Check ent_exist_intro.*)
(*Check ent_exist_elim.*)

(** Derived entailment rules *)
Lemma ent_weakening P Q R :
  (P ⊢ R) →
  P ∧ Q ⊢ R.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_true P :
  P ⊢ True.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_false P :
  False ⊢ P.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_and_comm P Q :
  P ∧ Q ⊢ Q ∧ P.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_or_comm P Q :
  P ∨ Q ⊢ Q ∨ P.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_all_comm {X} (Φ : X → X → iProp) :
  (∀ x y, Φ x y) ⊢ (∀ y x, Φ x y).
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_exist_comm {X} (Φ : X → X → iProp) :
  (∃ x y, Φ x y) ⊢ (∃ y x, Φ x y).
Proof.
  (* FIXME: exercise *)
Admitted.

(** Derived Hoare rules *)
Lemma hoare_con_pre P Q Φ e:
  (P ⊢ Q) →
  {{ Q }} e {{ Φ }} →
  {{ P }} e {{ Φ }}.
Proof.
  intros ??. eapply hoare_con; eauto.
Qed.

Lemma hoare_con_post P Φ Ψ e:
  (∀ v, Ψ v ⊢ Φ v) →
  {{ P }} e {{ Ψ }} →
  {{ P }} e {{ Φ }}.
Proof.
  intros ??. eapply hoare_con; last done; eauto.
Qed.

Lemma hoare_value_con P Φ v :
  (P ⊢ Φ v) →
  {{ P }} v {{ Φ }}.
Proof.
  intros H. eapply hoare_con; last apply hoare_value.
  - apply H.
  - eauto.
Qed.

Lemma hoare_value' P v :
  {{ P }} v {{ w, P ∗ ⌜w = v⌝}}.
Proof.
  eapply hoare_con; last apply hoare_value with (Φ := (λ v', P ∗ ⌜v' = v⌝)%I).
  - etrans; first apply ent_sep_true. rewrite ent_sep_comm. apply ent_sep_split; first done.
    by apply ent_prove_pure.
  - done.
Qed.

Lemma hoare_rec P Φ f x e v:
  ({{ P }} subst' x v (subst' f (rec: f x := e) e) {{Φ}}) →
  {{ P }} (rec: f x := e)%V v {{Φ}}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma hoare_let P Φ x e v:
  ({{ P }} subst' x v e {{Φ}}) →
  {{ P }} let: x := v in e {{Φ}}.
Proof.
  intros Ha. eapply hoare_pure_steps.
  { eapply (rtc_pure_step_fill [AppLCtx _]).
    apply pure_step_val. done.
  }
  eapply hoare_pure_step; last done.
  apply pure_step_beta.
Qed.

Lemma hoare_eq_num (n m: Z):
  {{ ⌜n = m⌝ }} #n = #m {{ u, ⌜u = #true⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma hoare_neq_num (n m: Z):
  {{ ⌜n ≠ m⌝ }} #n = #m {{ u, ⌜u = #false⌝ }}.
Proof.
  eapply hoare_pure; first reflexivity.
  intros Hneq. eapply hoare_pure_step.
  { apply pure_step_neq. done. }
  apply hoare_value_con.
  by apply ent_prove_pure.
Qed.

Lemma hoare_sub (z1 z2: Z):
  {{ True }} #z1 - #z2 {{ v, ⌜v = #(z1 - z2)⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma hoare_add (z1 z2: Z):
  {{ True }} #z1 + #z2 {{ v, ⌜v = #(z1 + z2)⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma hoare_if_false P e1 e2 Φ:
  {{ P }} e2 {{ Φ }} →
  ({{ P }} if: #false then e1 else e2 {{ Φ }}).
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma hoare_if_true P e1 e2 Φ:
  {{ P }} e1 {{ Φ }} →
  ({{ P }} if: #true then e1 else e2 {{ Φ }}).
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma hoare_pure_pre φ Φ e:
  {{ ⌜φ⌝ }} e {{ Φ }} ↔ (φ → {{ True }} e {{ Φ }}).
Proof.
  (* FIXME: exercise *)
Admitted.

(** Example: Fibonacci *)
Definition fib: val :=
  rec: "fib" "n" :=
    if: "n" = #0 then #0
    else if: "n" = #1 then #1
    else "fib" ("n" - #1) + "fib" ("n" - #2).

Lemma fib_zero:
  {{ True }} fib #0 {{ v, ⌜v = #0⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma fib_one:
  {{ True }} fib #1 {{ v, ⌜v = #1⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma fib_succ (z n m: Z):
  {{ True }} fib #(z - 1)%Z {{ v, ⌜v = #n⌝ }} →
  {{ True }} fib #(z - 2)%Z {{ v, ⌜v = #m⌝ }} →
  {{ ⌜z > 1⌝%Z }} fib #z {{ v, ⌜v = #(n + m)⌝ }}.
Proof.
  intros H1 H2. eapply hoare_pure_pre. intros Hgt.
  unfold fib.
  eapply hoare_pure_steps.
  { econstructor 2.
    { apply pure_step_beta. }
    simpl. econstructor 2. { apply (pure_step_fill [IfCtx _ _]). apply pure_step_neq. lia. }
    simpl. econstructor 2. { apply pure_step_if_false. }
    econstructor 2. { apply (pure_step_fill [IfCtx _ _]). apply pure_step_neq. lia. }
    simpl. econstructor 2. { apply pure_step_if_false. }
    fold fib. reflexivity.
  }
  eapply (hoare_bind [BinOpRCtx _ _]).
  { eapply (hoare_bind [AppRCtx _]). { apply hoare_sub. }
    intros v. eapply hoare_pure_pre. intros ->. apply H2.
  }
  intros v. apply hoare_pure_pre. intros ->. simpl.
  eapply (hoare_bind [BinOpLCtx _ _]).
  { eapply (hoare_bind [AppRCtx _]). { apply hoare_sub. }
    intros v. eapply hoare_pure_pre. intros ->. apply H1.
  }
  intros v. apply hoare_pure_pre. intros ->. simpl.
  eapply hoare_pure_step. { apply pure_step_add. }
  eapply hoare_value_con. by apply ent_prove_pure.
Qed.

Lemma fib_succ_oldschool (z n m: Z):
  {{ True }} fib #(z - 1)%Z {{ v, ⌜v = #n⌝ }} →
  {{ True }} fib #(z - 2)%Z {{ v, ⌜v = #m⌝ }} →
  {{ ⌜z > 1⌝%Z }} fib #z {{ v, ⌜v = #(n + m)⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Fixpoint Fib (n: nat) :=
  match n with
  | 0 => 0
  | S n =>
    match n with
    | 0 => 1
    | S m => Fib n + Fib m
    end
  end.

Lemma fib_computes_Fib (n: nat):
  {{ True }} fib #n {{ v, ⌜v = #(Fib n)⌝ }}.
Proof.
  induction (lt_wf n) as [n _ IH].
  destruct n as [|[|n]].
  - simpl. eapply fib_zero.
  - simpl. eapply fib_one.
  - replace (Fib (S (S n)): Z) with (Fib (S n) + Fib n)%Z by (simpl; lia).
    edestruct (hoare_pure_pre (S (S n) > 1))%Z as [H1 _]; eapply H1; last lia.
    eapply fib_succ.
    + replace (S (S n) - 1)%Z with (S n: Z) by lia. eapply IH. lia.
    + replace (S (S n) - 2)%Z with (n: Z) by lia. eapply IH. lia.
Qed.

(** ** Example: gcd *)
Definition mod_val : val :=
  λ: "a" "b", "a" - ("a" `quot` "b") * "b".
Definition euclid: val :=
  rec: "euclid" "a" "b" :=
    if: "b" = #0 then "a" else "euclid" "b" (mod_val "a" "b").

Lemma quot_diff a b :
  (0 ≤ a)%Z → (0 < b)%Z → (0 ≤ a - a `quot` b * b < b)%Z.
Proof.
  intros. split.
  - rewrite Z.mul_comm -Z.rem_eq; last lia. apply Z.rem_nonneg; lia.
  - rewrite Z.mul_comm -Z.rem_eq; last lia.
    specialize (Z.rem_bound_pos_pos a b ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma Z_nonneg_ind (P : Z → Prop) :
  (∀ x, (0 ≤ x)%Z → (∀ y, (0 ≤ y < x)%Z → P y) → P x) →
   ∀ x, (0 ≤ x)%Z → P x.
Proof.
  intros IH x Hle. generalize Hle.
  revert x Hle. refine (Z_lt_induction (λ x, (0 ≤ x)%Z → P x) _).
  naive_solver.
Qed.

Lemma mod_spec (a b : Z) :
  {{ ⌜(b > 0)%Z⌝ ∧ ⌜(a >= 0)%Z⌝ }}
    mod_val #a #b
  {{ cv, ∃ (c k : Z), ⌜cv = #c ∧ (0 <= k)%Z ∧ (a = b * k + c)%Z ∧ (0 <= c < b)%Z⌝ }}.
Proof.
  eapply (hoare_pure _ (b > 0 ∧ a >= 0)%Z).
  { eapply ent_assume_pure. { eapply ent_and_elim_l. }
    intros ?. eapply ent_assume_pure. { eapply ent_and_elim_r. }
    intros ?. eapply ent_assume_pure. { eapply ent_and_elim_l. }
    intros ?. apply ent_prove_pure. done.
  }
  intros (? & ?).
  unfold mod_val. eapply hoare_pure_step.
  { apply pure_step_fill with (K := [AppLCtx _]). apply pure_step_beta. }
  fold mod_val. simpl.
  apply hoare_let. simpl.
  eapply hoare_pure_step.
  { apply pure_step_fill with (K := [BinOpLCtx _ _; BinOpRCtx _ _]).
    apply pure_step_quot. lia.
  }
  simpl. eapply hoare_pure_step.
  { apply pure_step_fill with (K := [BinOpRCtx _ _]). apply pure_step_mul. }
  simpl. eapply hoare_pure_step.
  { apply pure_step_sub. }
  eapply hoare_value_con.
  eapply ent_exist_intro. apply ent_exist_intro with (x := (a `quot` b)%Z).
  (* MATH *)
  apply ent_prove_pure. split; last split; last split.
  - reflexivity.
  - apply Z.quot_pos; lia.
  - lia.
  - apply quot_diff; lia.
Qed.

Lemma gcd_step (b c k : Z) :
  Z.gcd b c = Z.gcd (b * k + c) b.
Proof.
  rewrite Z.add_comm (Z.gcd_comm _ b) Z.mul_comm Z.gcd_add_mult_diag_r. done.
Qed.

Lemma euclid_step_gt0 (a b : Z) :
  (∀ c : Z,
    {{ ⌜(0 ≤ c < b)%Z⌝}}
      euclid #b #c
    {{ d, ⌜d = #(Z.gcd b c)⌝ }}) →
  {{ ⌜(b > 0)%Z⌝ ∧ ⌜(a >= 0)%Z⌝}} euclid #a #b {{ c, ⌜c = #(Z.gcd a b)⌝ }}.
Proof.
  intros Ha.
  eapply (hoare_pure _ (a >= 0 ∧ b > 0)%Z).
  { eapply ent_assume_pure. { eapply ent_and_elim_l. }
    intros ?. eapply ent_assume_pure. { eapply ent_and_elim_r. }
    intros ?. eapply ent_assume_pure. { eapply ent_and_elim_l. }
    intros ?. apply ent_prove_pure. done.
  }
  intros (? & ?).
  unfold euclid. eapply hoare_pure_step.
  { apply (pure_step_fill [AppLCtx _]). apply pure_step_beta. }
  fold euclid. simpl. apply hoare_let. simpl.
  eapply hoare_pure_step.
  { apply (pure_step_fill [IfCtx _ _]). apply pure_step_neq. lia. }
  simpl. apply hoare_if_false.

  eapply hoare_bind with (K := [AppRCtx _]).
  { apply mod_spec. }
  intros v. simpl.
  apply hoare_exist_pre. intros d.
  apply hoare_exist_pre. intros k.
  apply hoare_pure_pre.
  intros (-> & ? & -> & ?).
  eapply hoare_con; last apply Ha.
  { apply ent_prove_pure. split_and!; lia. }
  { simpl. intros v. eapply ent_assume_pure; first done. intros ->.
    apply ent_prove_pure. f_equiv. f_equiv. apply gcd_step.
  }
Qed.

Lemma euclid_step_0 (a : Z) :
  {{ True }} euclid #a #0 {{ v, ⌜v = #a⌝ }}.
Proof.
  unfold euclid. eapply hoare_pure_step.
  { apply (pure_step_fill [AppLCtx _]). apply pure_step_beta. }
  fold euclid. simpl. apply hoare_let. simpl.
  eapply hoare_pure_step.
  { apply (pure_step_fill [IfCtx _ _]). apply pure_step_eq. lia. }
  simpl. apply hoare_if_true.
  apply hoare_value_con. by apply ent_prove_pure.
Qed.

Lemma euclid_proof (a b : Z) :
  {{ ⌜(0 ≤ a ∧ 0 ≤ b)%Z⌝ }} euclid #a #b {{ c, ⌜c = #(Z.gcd a b)⌝ }}.
Proof.
  eapply hoare_pure_pre. intros (Ha & Hb).
  revert b Hb a Ha. refine (Z_nonneg_ind _ _).
  intros b Hb IH a Ha.
  destruct (decide (b = 0)) as [ -> | Hneq0].
  - eapply hoare_con; last apply euclid_step_0.
    { done. }
    { intros v. simpl. eapply ent_assume_pure; first done. intros ->.
      apply ent_prove_pure.
      rewrite Z.gcd_0_r Z.abs_eq; first done. lia.
    }
  - (* use a mod b < b *)
    eapply hoare_con; last apply euclid_step_gt0.
    { apply ent_and_intro; apply ent_prove_pure; lia. }
    { done. }
    intros c. apply hoare_pure_pre. intros.
    eapply hoare_con; last eapply IH; [ done | done | lia.. ].
Qed.

(** Exercise: Factorial *)
Definition fac : val :=
  rec: "fac" "n" :=
    if: "n" = #0 then #1
    else "n" * "fac" ("n" - #1).

Lemma fac_zero :
  {{ True }} fac #0 {{ v, ⌜v = #1⌝ }}.
Proof.
  unfold fac. apply hoare_rec. simpl.
  eapply hoare_pure_steps.
  { econstructor 2.
    { eapply pure_step_fill with (K := [IfCtx _ _]). by apply pure_step_eq. }
    simpl. econstructor 2. { apply pure_step_if_true. }
    reflexivity.
  }
  eapply hoare_value_con. by apply ent_prove_pure.
Qed.

Lemma fac_succ (n m : Z) :
  {{ True }} fac #(n - 1) {{ v, ⌜v = #m⌝ }} →
  {{ ⌜(n > 0)%Z⌝ }} fac #n {{ v, ⌜v = #(n * m)⌝ }}.
Proof.
  intros Hs. unfold fac. apply hoare_rec. simpl.
  apply hoare_pure_pre. intros Hn.
  eapply hoare_pure_steps.
  { econstructor 2.
    { eapply pure_step_fill with (K := [IfCtx _ _]).
      apply pure_step_neq. lia. }
    simpl. econstructor 2. { apply pure_step_if_false. }
    fold fac. econstructor 2.
    { eapply pure_step_fill with (K := [AppRCtx _; BinOpRCtx _ _]).
      apply pure_step_sub.
    }
    simpl. reflexivity.
  }
  eapply hoare_bind with (K := [BinOpRCtx _ _]). { apply Hs. }
  intros v. apply hoare_pure_pre. intros ->.
  simpl. eapply hoare_pure_step. { apply pure_step_mul. }
  eapply hoare_value_con. by apply ent_prove_pure.
Qed.

Fixpoint Fac (n : nat) :=
  match n with
  | 0 => 1
  | S n => (S n) * Fac n
  end.
Lemma fac_computes_Fac (n : nat) :
  {{ True }} fac #n {{ v, ⌜v = #(Fac n)⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

(** * Separation Logic *)
(*Check ent_sep_weaken.*)
(*Check ent_sep_true.*)
(*Check ent_sep_comm.*)
(*Check ent_sep_split.*)
(*Check ent_sep_assoc.*)
(*Check ent_pointsto_sep.*)
(*Check ent_exists_sep.*)

(* Note: the separating conjunction can be typed with `\sep` *)


Lemma ent_pointsto_disj l l' v w :
  l ↦ v ∗ l' ↦ w ⊢ ⌜l ≠ l'⌝.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_sep_exists {X} (Φ : X → iProp) P :
  (∃ x : X, Φ x ∗ P) ⊣⊢ (∃ x : X, Φ x) ∗ P.
Proof.
  (* FIXME: exercise *)
Admitted.


(** ** Example: Chains *)
Fixpoint chain_pre n l r : iProp :=
  match n with
  | 0 => ⌜l = r⌝
  | S n => ∃ t : loc, l ↦ #t ∗ chain_pre n t r
  end.
Definition chain l r : iProp := ∃ n, ⌜n > 0⌝ ∗ chain_pre n l r.

Lemma chain_single (l r : loc) :
  l ↦ #r ⊢ chain l r.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma chain_cons (l r t : loc) :
  l ↦ #r ∗ chain r t ⊢ chain l t.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma chain_trans (l r t : loc) :
  chain l r ∗ chain r t ⊢ chain l t.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma chain_sep_false (l r t : loc) :
  chain l r ∗ chain l t ⊢ False.
Proof.
  (* FIXME: exercise *)
Admitted.

Definition cycle l := chain l l.
Lemma chain_cycle l r :
  chain l r ∗ chain r l ⊢ cycle l.
Proof.
  apply chain_trans.
Qed.


(** New Hoare rules *)
(*Check hoare_frame.*)
(*Check hoare_new.*)
(*Check hoare_store.*)
(*Check hoare_load.*)

Lemma hoare_pure_pre_sep_l (ϕ : Prop) Q Φ e :
  (ϕ → {{ Q }} e {{ Φ }}) →
  {{ ⌜ϕ⌝ ∗ Q }} e {{ Φ }}.
Proof.
  intros He.
  eapply hoare_pure.
  { apply ent_sep_weaken. }
  intros ?.
  eapply hoare_con; last by apply He.
  - rewrite ent_sep_comm. apply ent_sep_weaken.
  - done.
Qed.

(* Enables rewriting with equivalences ⊣⊢ in pre/post condition *)
#[export] Instance hoare_proper :
  Proper (equiv ==> eq ==> (pointwise_relation val (⊢)) ==> impl) hoare.
Proof.
  intros P1 P2 HP%ent_equiv e1 e2 <- Φ1 Φ2 HΦ Hp.
  eapply hoare_con; last done.
  - apply HP.
  - done.
Qed.

Definition assert e := (if: e then #() else #0 #0)%E.

Lemma hoare_assert P e :
  {{ P }} e {{ v, ⌜v = #true⌝ }} →
  {{ P }} assert e {{ v, ⌜v = #()⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma frame_example (f : val) :
  (∀ l l' : loc, {{ l ↦ #0 }} f #l #l' {{ _, l ↦ #42 }}) →
  {{ True }}
    let: "x" := ref #0 in
    let: "y" := ref #42 in
    (f "x" "y";;
    assert (!"x" = !"y"))
  {{ _, True }}.
Proof.
  intros Hf.
  eapply hoare_bind with (K := [AppRCtx _]).
  { apply hoare_new. }
  intros v. simpl.
  apply hoare_exist_pre. intros l.
  apply hoare_pure_pre_sep_l. intros ->.
  eapply hoare_let. simpl.

  eapply hoare_bind with (K := [AppRCtx _]).
  { eapply hoare_con_pre. { apply ent_sep_true. }
    eapply hoare_frame. apply hoare_new. }
  intros v. simpl.

  rewrite -ent_sep_exists. apply hoare_exist_pre. intros l'.
  rewrite -ent_sep_assoc. eapply hoare_pure_pre_sep_l. intros ->.
  eapply hoare_let. simpl.
  eapply hoare_bind with (K := [AppRCtx _]).
  { rewrite ent_sep_comm. eapply hoare_frame. apply Hf. }
  intros v. simpl.

  apply hoare_let. simpl.
  eapply hoare_con_post; first last.
  { apply hoare_assert.
    eapply hoare_bind with (K := [BinOpRCtx _ _]).
    { rewrite ent_sep_comm. apply hoare_frame. apply hoare_load. }
    intros v'. simpl. rewrite -ent_sep_assoc. apply hoare_pure_pre_sep_l.
    intros ->.

    eapply hoare_bind with (K := [BinOpLCtx _ _]).
    { rewrite ent_sep_comm. apply hoare_frame. apply hoare_load. }
    intros v'. simpl. rewrite -ent_sep_assoc. apply hoare_pure_pre_sep_l.
    intros ->.

    eapply hoare_pure_step. { by apply pure_step_eq. }
    eapply hoare_value_con. by apply ent_prove_pure.
  }
  intros. apply ent_true.
Qed.

(** Exercise: swap *)
Definition swap : val :=
  λ: "l" "r", let: "t" := ! "r" in "r" <- !"l";; "l" <- "t".

Lemma swap_correct (l r: loc) (v w: val):
  {{ l ↦ v ∗ r ↦ w }} swap #l #r {{ _, l ↦ w ∗ r ↦ v }}.
Proof.
  (* FIXME: exercise *)
Admitted.



(** ** Case study: lists *)
Fixpoint is_ll (xs : list val) (v : val) : iProp :=
  match xs with
  | [] => ⌜v = NONEV⌝
  | x :: xs =>
    ∃ (l : loc) (w : val),
      ⌜v = SOMEV #l⌝ ∗ l ↦ (x, w) ∗ is_ll xs w
  end.

Definition new_ll : val :=
  λ: <>, NONEV.

Definition cons_ll : val :=
  λ: "h" "l", SOME (ref ("h", "l")).

Definition head_ll : val :=
  λ: "x", match: "x" with NONE => #() | SOME "r" => Fst (!"r") end.
Definition tail_ll : val :=
  λ: "x", match: "x" with NONE => #() | SOME "r" => Snd (!"r") end.

Definition len_ll : val :=
  rec: "len" "x" := match: "x" with NONE => #0 | SOME "r" => #1 + "len" (Snd !"r") end.

Definition app_ll : val :=
  rec: "app" "x" "y" :=
    match: "x" with NONE => "y" | SOME "r" =>
        let: "rs" := !"r" in
        "r" <- (Fst "rs", "app" (Snd "rs") "y");;
        SOME "r"
    end.


Lemma app_ll_correct xs ys v w :
  {{ is_ll xs v ∗ is_ll ys w }} app_ll v w {{ u, is_ll (xs ++ ys) u }}.
Proof.
  induction xs as [ | x xs IH] in v |-*.
  - simpl. apply hoare_pure_pre_sep_l. intros ->.
    eapply hoare_bind with (K := [AppLCtx _]).
    { apply hoare_rec. simpl.
      eapply hoare_pure_steps.
      { apply pure_step_val. done. }
      eapply hoare_value'.
    }
    intros v'. simpl. rewrite ent_sep_comm. apply hoare_pure_pre_sep_l. intros ->.

    apply hoare_rec. simpl.
    eapply hoare_pure_step. { apply pure_step_match_injl. }
    apply hoare_let. simpl. apply hoare_value.
  - simpl. rewrite -ent_sep_exists. apply hoare_exist_pre.
    intros l. rewrite -ent_sep_exists. apply hoare_exist_pre.
    intros w'. rewrite -ent_sep_assoc. apply hoare_pure_pre_sep_l. intros ->.

    eapply hoare_bind with (K := [AppLCtx _ ]).
    { apply hoare_rec. simpl.
      eapply hoare_pure_steps. {apply pure_step_val. done. }
      eapply hoare_value'.
    }
    intros v'. simpl. rewrite ent_sep_comm. apply hoare_pure_pre_sep_l. intros ->.

    apply hoare_rec. simpl.
    eapply hoare_pure_step. {apply pure_step_match_injr. }
    apply hoare_let. simpl.
    eapply hoare_bind with (K := [AppRCtx _]).
    { apply hoare_frame. apply hoare_frame. apply hoare_load. }
    intros v. simpl.
    rewrite -!ent_sep_assoc. apply hoare_pure_pre_sep_l. intros ->.
    apply hoare_let. simpl.

    eapply hoare_bind with (K := [PairRCtx _; StoreRCtx _; AppRCtx _]).
    { eapply hoare_bind with (K := [AppRCtx _; AppLCtx _]).
      { eapply hoare_pure_step. { apply pure_step_snd. }
        apply hoare_value'.
      }
      intros v. simpl. fold app_ll.
      rewrite ent_sep_comm. apply hoare_pure_pre_sep_l. intros ->.
      rewrite ent_sep_comm. eapply hoare_frame.
      apply IH.
    }
    intros v. simpl.
    eapply hoare_bind with (K := [PairLCtx _; StoreRCtx _; AppRCtx _]).
    { eapply hoare_pure_step. { apply pure_step_fst. }
      apply hoare_value'.
    }
    intros v'. simpl. rewrite ent_sep_comm. apply hoare_pure_pre_sep_l. intros ->.
    eapply hoare_bind with (K := [AppRCtx _]).
    { rewrite ent_sep_comm. apply hoare_frame.
      eapply hoare_bind with (K := [StoreRCtx _]).
      { eapply hoare_pure_steps.
        { eapply pure_step_val. eauto. }
        eapply hoare_value'.
      }
      intros v'. simpl. rewrite ent_sep_comm. apply hoare_pure_pre_sep_l. intros ->.
      apply hoare_store.
    }
    intros v'. simpl. apply hoare_let. simpl.
    eapply hoare_pure_steps.
    { eapply pure_step_val. eauto. }
    eapply hoare_value_con.
    eapply ent_exist_intro. eapply ent_exist_intro.
    etrans. { apply ent_sep_true. }
    eapply ent_sep_split.
    { apply ent_prove_pure. done. }
    apply ent_sep_split; reflexivity.
Qed.

(** Exercise: linked lists *)
Lemma new_ll_correct :
  {{ True }} new_ll #() {{ v, is_ll [] v }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma cons_ll_correct (v x : val) xs :
  {{ is_ll xs v }} cons_ll x v {{ u, is_ll (x :: xs) u }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma head_ll_correct (v x : val) xs :
  {{ is_ll (x :: xs) v }} head_ll v {{ w, ⌜w = x⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.


Lemma tail_ll_correct v x xs :
  {{ is_ll (x :: xs) v }} tail_ll v {{ w, is_ll xs w }}.
Proof.
  (* FIXME: exercise *)
Admitted.



Lemma len_ll_correct v xs :
  {{ is_ll xs v }} len_ll v {{ w, ⌜w = #(length xs)⌝ ∗ is_ll xs v }}.
Proof.
  (* FIXME: exercise *)
Admitted.


(** Exercise: Prove your strengthened specification for [tail]. *)
Lemma tail_ll_strengthened v x xs :
  {{ is_ll (x :: xs) v }} tail_ll v {{ w, False (* FIXME *) }}.
Proof.
  (* FIXME: exercise *)
Abort.

