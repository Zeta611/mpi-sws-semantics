From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang primitive_laws notation.
From iris.base_logic Require Import invariants.
From semantics.pl.heap_lang Require Import adequacy proofmode primitive_laws_nolater.
From semantics.pl Require Import hoare_lib.
From semantics.pl.program_logic Require Import notation.

(** ** Magic is in the air *)
Import hoare.
(*Check ent_wand_intro.*)
(*Check ent_wand_elim.*)

Section primitive.
Implicit Types (P Q R: iProp).

Lemma ent_or_sep_dist P Q R :
  (P ∨ Q) ∗ R ⊢ (P ∗ R) ∨ (Q ∗ R).
Proof.
  apply ent_wand_elim.
  apply ent_or_elim.
  - apply ent_wand_intro. apply ent_or_introl.
  - apply ent_wand_intro. apply ent_or_intror.
Qed.

Lemma ent_carry_res P Q :
  P ⊢ Q -∗ P ∗ Q.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.


Lemma ent_comm_premise P Q R :
  (Q -∗ P -∗ R) ⊢ P -∗ Q -∗ R.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma ent_sep_or_disj2 P Q R :
  (P ∨ R) ∗ (Q ∨ R) ⊢ (P ∗ Q) ∨ R.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.
End primitive.

(** ** Using the IPM *)
Implicit Types
  (P Q R: iProp)
  (Φ Ψ : val → iProp)
.

Lemma or_elim P Q R:
  (P ⊢ R) →
  (Q ⊢ R) →
  (P ∨ Q) ⊢ R.
Proof.
  iIntros (H1 H2) "[P|Q]".
  - by iApply H1.
  - by iApply H2.
Qed.

Lemma or_intro_l P Q:
  P ⊢ P ∨ Q.
Proof.
  iIntros "P". iLeft. iFrame "P".

  (* [iExact] corresponds to Coq's [exact] *)
  Restart.
  iIntros "P". iLeft. iExact "P".

  (* [iAssumption] can solve the goal if there is an exact match in the context *)
  Restart.
  iIntros "P". iLeft. iAssumption.

  (* This directly frames the introduced proposition. The IPM will automatically try to pick a disjunct. *)
  Restart.
  iIntros "$".
Qed.

Lemma or_sep P Q R: (P ∨ Q) ∗ R ⊢ (P ∗ R) ∨ (Q ∗ R).
Proof.
  (* we first introduce, destructing the separating conjunction *)
  iIntros "[HPQ HR]".
  iDestruct "HPQ" as "[HP | HQ]".
  - iLeft. iFrame.
  - iRight. iFrame.

  (* we can also split more explicitly *)
  Restart.
  iIntros "[HPQ HR]".
  iDestruct "HPQ" as "[HP | HQ]".
  - iLeft.
    (* [iSplitL] uses the given hypotheses to prove the left conjunct and the rest for the right conjunct *)
    (* symmetrically, [iSplitR] gives the specified hypotheses to the right *)
    iSplitL "HP". all: iAssumption.
  - iRight.
    (* if we don't give any hypotheses, everything will go to the left. *)
    iSplitL. (* now we're stuck... *)

  (* alternative: directly destruct the disjunction *)
  Restart.
  (* iFrame will also directly pick the disjunct *)
  iIntros "[[HP | HQ] HR]"; iFrame.
Abort.

(* Using entailments *)
Lemma or_sep P Q R: (P ∨ Q) ∗ R ⊢ (P ∗ R) ∨ (Q ∗ R).
Proof.
  iIntros "[HPQ HR]". iDestruct "HPQ" as "[HP | HQ]".
  - (* this will make the entailment ⊢ into a wand *)
    iPoseProof (ent_or_introl (P ∗ R) (Q ∗ R)) as "-#Hor".
    iApply "Hor". iFrame.
  - (* we can also directly apply the entailment *)
    iApply ent_or_intror.
    iFrame.
Abort.

(* Proving pure Coq propositions *)
Lemma prove_pure P : P ⊢ ⌜42 > 0⌝.
Proof.
  iIntros "HP".
  (* [iPureIntro] will switch to a Coq goal, of course losing access to the Iris context *)
  iPureIntro. lia.
Abort.

(* Destructing assumptions *)
Lemma destruct_ex {X} (p : X → Prop) (Φ : X → iProp) : (∃ x : X, ⌜p x⌝ ∗ Φ x) ⊢ False.
Proof.
  (* we can lead the identifier with a [%] to introduce to the Coq context *)
  iIntros "[%w Hw]".
  iDestruct "Hw" as  "[%Hw1 Hw2]".

  (* more compactly: *)
  Restart.
  iIntros "(%w & %Hw1 & Hw2)".

  Restart.
  (* we cannot introduce an existential to the Iris context *)
  Fail iIntros "(w & Hw)".

  Restart.
  iIntros "(%w & Hw1 & Hw2)".
  (* if we first introduce a pure proposition into the Iris context,
    we can later move it to the Coq context *)
  iDestruct "Hw1" as "%Hw1".
Abort.

(* Specializing assumptions *)
Lemma specialize_assum P Q R :
  ⊢
  P -∗
  R -∗
  (P ∗ R -∗ (P ∗ R) ∨ (Q ∗ R)) -∗
  (P ∗ R) ∨ (Q ∗ R).
Proof.
  iIntros "HP HR Hw".
  iSpecialize ("Hw" with "[HR HP]").
  { iFrame. }

  Restart.
  iIntros "HP HR Hw".
  (* we can also directly frame it *)
  iSpecialize ("Hw" with "[$HR $HP]").

  Restart.
  iIntros "HP HR Hw".
  (* we can let it frame all hypotheses *)
  iSpecialize ("Hw" with "[$]").

  Restart.
  (* we can also use [iPoseProof], and introduce the generated hypothesis with [as] *)
  iIntros "HP HR Hw".
  iPoseProof ("Hw" with "[$HR $HP]") as "$".

  Restart.
  iIntros "HP HR Hw".
  (* [iApply] can similarly be specialized *)
  iApply ("Hw" with "[$HP $HR]").

Abort.

(* Nested specialization *)
Lemma specialize_nested P Q R :
  ⊢
  P -∗
  (P -∗ R) -∗
  (R -∗ Q) -∗
  Q.
Proof.
  iIntros "HP HPR HRQ".
  (* we can use the pattern with round parentheses to specialize a hypothesis in a nested way *)
  iSpecialize ("HRQ" with "(HPR HP)").
  (* can finish the proof with [iExact] *)
  iExact "HRQ".

  (* of course, this also works for [iApply] *)
  Restart.
  iIntros "HP HPR HRQ". iApply ("HRQ" with "(HPR HP)").
Abort.

(* Existentials *)
Lemma prove_existential (Φ : nat → iProp) :
  ⊢ Φ 1337 -∗ ∃ n m, ⌜n > 41⌝ ∗ Φ m.
Proof.
  (* [iExists] can instantiate existentials *)
  iIntros "Ha".
  iExists 42.
  iExists 1337. iSplitR. { iPureIntro. lia. } iFrame.

  Restart.
  iIntros "Ha". iExists 42, 1337.
  (* [iSplit] works if the goal is a conjunction or one of the separating conjuncts is pure.
     In that case, the hypotheses will be available for both sides.  *)
  iSplit.

  Restart.
  iIntros "Ha". iExists 42, 1337. iSplitR; iFrame; iPureIntro. lia.
Abort.

(* specializing universals *)
Lemma specialize_universal (Φ : nat → iProp) :
  ⊢ (∀ n, ⌜n = 42⌝ -∗ Φ n) -∗ Φ 42.
Proof.
  iIntros "Hn".
  (* we can use [$!] to specialize Iris hypotheses with pure Coq terms *)
  iSpecialize ("Hn" $! 42).
  iApply "Hn". done.

  Restart.
  iIntros "Hn".
  (* we can combine this with [with] patterns. The [%] pattern will generate a pure Coq goal. *)
  iApply ("Hn" $! 42 with "[%]").
  done.

  Restart.
  iIntros "Hn".
  (* ...and ending the pattern with // will call done *)
  iApply ("Hn" $! 42 with "[//]").
Abort.

Section without_ipm.
  (** Prove the following entailments without using the IPM. *)

  Lemma ent_lem1 P Q :
    True ⊢ P -∗ Q -∗ P ∗ Q.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma ent_lem2 P Q :
    P ∗ (P -∗ Q) ⊢ Q.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma ent_lem3 P Q R :
    (P ∨ Q) ⊢ R -∗ (P ∗ R) ∨ (Q ∗ R).
  Proof.
    (* FIXME: exercise *)
  Admitted.
End without_ipm.

Lemma ent_lem1_ipm P Q :
  True ⊢ P -∗ Q -∗ P ∗ Q.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_lem2_ipm P Q :
  P ∗ (P -∗ Q) ⊢ Q.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_lem3_ipm P Q R :
  (P ∨ Q) ⊢ R -∗ (P ∗ R) ∨ (Q ∗ R).
Proof.
  (* FIXME: exercise *)
Admitted.


(** Weakest precondition rules *)

(*Check ent_wp_value.*)
(*Check ent_wp_wand.*)
(*Check ent_wp_bind.*)
(*Check ent_wp_pure_step.*)
(*Check ent_wp_new.*)
(*Check ent_wp_load.*)
(*Check ent_wp_store.*)

Lemma ent_wp_pure_steps e e' Φ :
  rtc pure_step e e' →
  WP e' {{ Φ }} ⊢ WP e {{ Φ }}.
Proof.
  iIntros (Hpure) "Hwp".
  iInduction Hpure as [|] "IH"; first done.
  iApply ent_wp_pure_step; first done. by iApply "IH".
Qed.

(*Print hoare.*)

(** We can re-derive the Hoare rules from the weakest pre rules. *)
Lemma hoare_frame' P R Φ e :
  {{ P }} e {{ Φ }} →
  {{ P ∗ R }} e {{ v, Φ v ∗ R }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma hoare_load l v :
  {{ l ↦ v }} !#l {{ w, ⌜w = v⌝ ∗ l ↦ v }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma hoare_store l (v w : val) :
  {{ l ↦ v }} #l <- w {{ _, l ↦ w }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma hoare_new (v : val) :
  {{ True }} ref v {{ w, ∃ l : loc, ⌜w = #l⌝ ∗ l ↦ v }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.


(** Linked lists using the IPM *)
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
  iIntros "[Hv Hw]".
  iRevert (v) "Hv Hw".
  (* We use the [iInduction] tactic which lifts Coq's induction into Iris.
    ["IH"] is the name the inductive hypothesis should get in the Iris context.
    Note that the inductive hypothesis is printed above another line [-----□].
    This is another kind of context which you will learn about soon; for now, just
    treat it the same as any other elements of the Iris context.
  *)
  iInduction xs as [ | x xs] "IH"; simpl; iIntros (v) "Hv Hw".
  Restart.
  (* simpler: use the [forall] clause of [iInduction] to let it quantify over [v] *)
  iIntros "[Hv Hw]".
  iInduction xs as [ | x xs] "IH" forall (v); simpl.
  - iDestruct "Hv" as "->". unfold app_ll. wp_pures. iApply wp_value. done.
  - iDestruct "Hv" as "(%l & %w' & -> & Hl & Hv)".
    (* Note: [wp_pures] does not unfold the definition *)
    wp_pures.
    unfold app_ll. wp_pures. fold app_ll. wp_load. wp_pures.
    wp_bind (app_ll _ _). iApply (ent_wp_wand' with "[Hl] [Hv Hw]"); first last.
    { iApply ("IH" with "Hv Hw"). }
    simpl. iIntros (v) "Hv". wp_store. wp_pures. iApply wp_value. eauto with iFrame.
Qed.

Lemma new_ll_correct :
  {{ True }} new_ll #() {{ v, is_ll [] v }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma cons_ll_correct (v x : val) xs :
  {{ is_ll xs v }} cons_ll x v {{ u, is_ll (x :: xs) u }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma head_ll_correct (v x : val) xs :
  {{ is_ll (x :: xs) v }} head_ll v {{ w, ⌜w = x⌝ }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma tail_ll_correct v x xs :
  {{ is_ll (x :: xs) v }} tail_ll v {{ w, is_ll xs w }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.

Lemma len_ll_correct v xs :
  {{ is_ll xs v }} len_ll v {{ w, ⌜w = #(length xs)⌝ ∗ is_ll xs v }}.
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.


(** ** Persistency *)
(*Check ent_pers_dup.*)
(*Check ent_pers_elim.*)
(*Check ent_pers_mono.*)
(*Check ent_pers_pure.*)
(*Check ent_pers_and_sep.*)
(*Check ent_pers_idemp.*)
(*Check ent_pers_all.*)
(*Check ent_pers_exists.*)

Lemma ent_pers_dup' P :
  □ P ⊢ (□ P) ∗ (□ P).
Proof.
  (* don't use the IPM *) 
  (* FIXME: exercise *)
Admitted.


(** Hoare triples, internalized *)
Definition hoare (P : iProp) (e : expr) (Φ : val → iProp) : iProp :=
  □ (P -∗ WP e {{ Φ }}).

Global Notation "{{ P } } e {{ Φ } }" := (hoare P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
  format "{{  P  } }  e  {{  Φ  } }") : stdpp_scope.

Global Notation "{{ P } } e {{ v , Q } }" := (hoare P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
  format "{{  P  } }  e  {{  v ,  Q  } }") : stdpp_scope.

(** Example: *)
Lemma double_int f :
  {{ True }} f #() {{ v, ∃ z : Z, ⌜v = #z⌝ }} ⊢ {{ True }} f #() + f #() {{ v, ∃ z : Z, ⌜v = #z⌝ }}.
Proof.
  iIntros "#Hf !> _".
  Restart.
  (* alternative: *)
  iIntros "#Hf". iModIntro. iIntros "_".
Abort.

(** We can rederive the previous rules for external Hoare triples. *)
Section hoare_external.
  Definition hoare_ext (P : iProp) (e : expr) (Φ : val → iProp) : Prop :=
    True ⊢ {{ P }} e {{ Φ }}.

  Notation "{{ P } } e {{ Φ } '}e'" := (hoare_ext P%I e%E Φ%I)
    (at level 20, P, e, Φ at level 200,
    format "{{  P  } }  e  {{  Φ  } }e") : stdpp_scope.

  Notation "{{ P } } e {{ v , Q } '}e'" := (hoare_ext P%I e%E (λ v, Q)%I)
    (at level 20, P, e, Q at level 200,
    format "{{  P  } }  e  {{  v ,  Q  } }e") : stdpp_scope.

  Lemma hoare_ext_value v Φ:
    {{ Φ v }} v {{ Φ }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_con P Q Φ Ψ e:
    (P ⊢ Q) →
    (∀ v, Ψ v ⊢ Φ v) →
    {{ Q }} e {{ Ψ }}e →
    {{ P }} e {{ Φ }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_bind K P Φ Ψ e:
    {{ P }} e {{ Ψ }}e →
    (∀ v, {{ Ψ v }} fill K (Val v) {{ Φ }}e) →
    {{ P }} (fill K e) {{ Φ }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_pure P φ Φ e:
    (P ⊢ ⌜φ⌝) →
    (φ → {{ P }} e {{ Φ }}e) →
    {{ P }} e {{ Φ }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_exist_pre {X} (Φ : X → _) Ψ e :
    (∀ x : X, {{ Φ x }} e {{ Ψ }}e) →
    {{ ∃ x : X, Φ x }} e {{ Ψ }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_pure_step P Ψ e1 e2 :
    pure_step e1 e2 →
    {{ P }} e2 {{ Ψ }}e →
    {{ P }} e1 {{ Ψ }}e.
  Proof.
      (* FIXME: exercise *)
    Admitted.

  Lemma hoare_ext_new v :
    {{ True }} ref (Val v) {{ w, ∃ l : loc, ⌜w = #l⌝ ∗ l ↦ v }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_load l v:
    {{ l ↦ v }} ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_store l (v w: val):
    {{ l ↦ v }} #l <- w {{ _, l ↦ w }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma hoare_ext_frame P F Φ e:
    {{ P }} e {{ Φ }}e →
    {{ P ∗ F }} e {{ v, Φ v ∗ F }}e.
  Proof.
    (* FIXME: exercise *)
  Admitted.
End hoare_external.

(** ** Invariants *)
(*Check ent_inv_pers.*)
(*Check ent_inv_alloc.*)

(* The following rule is more comvenient to use *)
(*Check inv_alloc.*)

(** We require a sidecondition here, namely that [F] is "timeless". All propositions we have seen up to now are in fact timeless.
  We will see propositions that do not satisfy this requirement and which need a stronger rule for invariants soon.
*)
(*Check ent_inv_open.*)
(*Check inv_open.*)


(** MyMutBit *)
Definition MyMutBit : expr :=
  let: "x" := ref #0 in
  (λ: "y", "x" <- #1 - !"x",
   λ: "y", #0 < !"x").

Definition MutBit v : iProp :=
  {{ True }} (Fst v) #() {{ w, ⌜w = #()⌝ }} ∗
  {{ True }} (Snd v) #() {{ w, ⌜w = #true⌝ ∨ ⌜w = #false⌝}}.

Definition mutbitN := nroot .@ "mutbit".
Lemma MyMutBit_proof :
  ⊢ {{ True }} MyMutBit {{ v, MutBit v }}.
Proof.
  iIntros "!> _". unfold MyMutBit. wp_alloc l as "Hl". wp_pures.
  iApply (inv_alloc mutbitN (l ↦ #0 ∨ l ↦ #1) with "[Hl]").
  { eauto with iFrame. }
  iIntros "#HInv".
  iApply wp_value. unfold MutBit. iSplit.
  - iIntros "!>_". wp_pures.
    iApply (inv_open with "HInv"); first set_solver.
    iIntros "[Hl | Hl]".
    + wp_load. wp_store. iApply wp_value. eauto with iFrame.
    + wp_load. wp_store. iApply wp_value. eauto with iFrame.
  - iIntros "!> _". wp_pures.
    iApply (inv_open with "HInv"); first set_solver.
    iIntros "[Hl | Hl]".
    + wp_load. wp_pures. iApply wp_value. eauto with iFrame.
    + wp_load. wp_pures. iApply wp_value. eauto with iFrame.
Qed.

(** Exercise: Abstract integers *)
Notation "'assert' e" := (if: e%E then #() else #0 #0)%E (at level 40) : expr_scope.
Definition MyInt : expr :=
  λ: "z",
  let: "x" := ref (if: #0 < "z" then (#0, "z") else (-"z", #0)) in
  ((λ: "y", let: "xv" := !"x" in assert (#0 ≤ Fst "xv");; assert (#0 ≤ Snd "xv");; Snd "xv" - Fst "xv"),
   (λ: "y", let: "xv" := !"x" in "x" <- (Snd "xv", Fst "xv"))).

Definition FlipInt v : iProp :=
  {{ True }} (Fst v) #() {{ w, ∃ z : Z, ⌜w = #z⌝ }} ∗
  {{ True }} (Snd v) #() {{ w, ⌜w = #()⌝ }}.

Definition flipintN := nroot .@ "flipint".
Lemma MyInt_proof (z : Z) :
  ⊢ {{ True }} MyInt #z {{ v, FlipInt v }}.
Proof.
  (* FIXME: exercise *)
Admitted.

(** Exercise: Magic Wands for Accessors *)
Definition lookup_ll : val :=
  rec: "lookup" "l" "i" :=
    match: "l" with
      NONE => NONE
    | SOME "l" =>
        if: "i" = #0 then SOME "l"
        else
          let: "lv" := !"l" in
          "lookup" (Snd "lv") ("i" - #1)
    end.

(**
  The lookup [!!!] is stdpp's [lookup_total] that, in contrast to [lookup],
  does not return an [option], but rather a default value.
  (It computes well using Coq's reduction tactics.)
 *)
Lemma lookup_ll_correct xs lv (n : nat) :
  ⊢ {{ is_ll xs lv ∗ ⌜n < length xs⌝ }}
      lookup_ll lv #n
    {{ v, ∃ (l : loc) next, ⌜v = SOMEV #l⌝ ∗ l ↦ (xs !!! n, next) ∗ (∀ w', l ↦ (w', next) -∗ is_ll (<[n := w']> xs) lv) }}.
Proof.
  (* FIXME: exercise *)
Admitted.

(* A derived version that does not wrap the result in an option value.
  (thus, at the language level, no case analysis on whether the value actually exists is possible)
*)
Definition lookup_ll_unsafe : val :=
  λ: "l" "i",
    match: lookup_ll "l" "i" with
      SOME "l" => "l"
    | NONE => NONE
    end.
Lemma lookup_ll_unsafe_correct xs lv (n : nat) :
  ⊢ {{ is_ll xs lv ∗ ⌜n < length xs⌝ }}
      lookup_ll_unsafe lv #n
    {{ v, ∃ (l : loc) next, ⌜v = #l⌝ ∗ l ↦ (xs !!! n, next) ∗ (∀ w', l ↦ (w', next) -∗ is_ll (<[n := w']> xs) lv) }}.
Proof.
  (* derive this from [lookup_ll_correct] *)
  (* FIXME: exercise *)
Admitted.
