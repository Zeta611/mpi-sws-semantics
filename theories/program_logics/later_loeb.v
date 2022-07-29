From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang primitive_laws notation.
From iris.base_logic Require Import invariants.
From semantics.pl.heap_lang Require Import adequacy proofmode primitive_laws_nolater.
From semantics.pl Require Import hoare_lib.
From semantics.pl.program_logic Require Import notation.
From semantics.pl Require Import ipm.

(** ** Step-indexing *)
Import hoare ipm.
Implicit Types
  (P Q R: iProp)
  (Φ Ψ : val → iProp)
.

(*Check ent_later_intro.*)
(*Check ent_later_mono.*)
(*Check ent_löb.*)
(*Check ent_later_sep.*)
(*Check ent_later_exists.*)
(*Check ent_later_all.*)
(*Check ent_later_pers.*)

(*Check ent_later_wp_pure_step.*)
(*Check ent_later_wp_new.*)
(*Check ent_later_wp_load.*)
(*Check ent_later_wp_store.*)

(* Exercise: Derive the old rules from the new ones. *)
Lemma ent_wp_pure_step_old e e' Φ :
  pure_step e e' →
  WP e' {{ Φ }} ⊢ WP e {{ Φ }}.
Proof.
  (* FIXME: exercise *)
Admitted.
Lemma ent_wp_new_old v Φ :
  (∀ l, l ↦ v -∗ Φ #l) ⊢ WP ref v {{ Φ }}.
Proof.
  (* FIXME: exercise *)
Admitted.
Lemma ent_wp_load_old l v Φ :
  l ↦ v ∗ (l ↦ v -∗ Φ v) ⊢ WP !#l {{ Φ }}.
Proof.
  (* FIXME: exercise *)
Admitted.
Lemma ent_wp_store_old l v w Φ :
  l ↦ v ∗ (l ↦ w -∗ Φ #()) ⊢ WP #l <- w {{ Φ }}.
Proof.
  (* FIXME: exercise *)
Admitted.

Lemma ent_later_and P Q :
  ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
Proof.
  specialize (ent_later_all (λ b : bool, if b then P else Q)). rewrite !ent_equiv.
  intros [Ha Hb]. split.
  - apply ent_and_intro.
    + etrans; first etrans; [ | apply Ha | ].
      * apply ent_later_mono. apply ent_all_intro. intros []; [apply ent_and_elim_l | apply ent_and_elim_r].
      * etrans; first apply (ent_all_elim true). apply ent_later_mono. done.
    + apply ent_later_mono. apply ent_and_elim_r.
  - etrans; first etrans; [ | apply Hb | ].
    + apply ent_all_intro. intros []; [apply ent_and_elim_l | apply ent_and_elim_r].
    + apply ent_later_mono. apply ent_and_intro.
      * apply (ent_all_elim true).
      * apply (ent_all_elim false).
Qed.

Lemma ent_later_or P Q :
  ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof.
  specialize (ent_later_exists (λ b : bool, if b then P else Q)). rewrite !ent_equiv.
  intros [Ha Hb]. split.
  - etrans; first etrans; [ | apply Ha | ].
    + apply ent_later_mono. apply ent_or_elim.
      * by apply (ent_exist_intro true).
      * by apply (ent_exist_intro false).
    + apply ent_exist_elim. intros []; [apply ent_or_introl | apply ent_or_intror].
  - etrans; first etrans; [ | apply Hb | ].
    + apply ent_or_elim.
      * by apply (ent_exist_intro true).
      * by apply (ent_exist_intro false).
    + apply ent_later_mono. apply ent_exist_elim.
      intros []; [apply ent_or_introl | apply ent_or_intror].
Qed.

Lemma ent_all_pers {X} (Φ : X → iProp) :
  □ (∀ x : X, Φ x) ⊢ ∀ x : X, □ Φ x.
Proof.
  apply ent_all_intro. intros x. apply ent_pers_mono. apply ent_all_elim.
Qed.

Lemma ent_wp_rec' Φ (Ψ : val → val → iProp) e :
  (⊢ ∀ v, {{ Φ v ∗ (∀ u, {{ Φ u }} (rec: "f" "x" := e) u {{ Ψ u }})}} subst "x" v (subst "f" (rec: "f" "x" := e) e) {{ Ψ v }}) →
  (⊢ ∀ v, {{ Φ v }} (rec: "f" "x" := e) v {{ Ψ v }}).
Proof.
  intros Ha. apply ent_löb.
  apply ent_all_intro. intros v.
  etrans. { apply ent_later_mono. apply ent_pers_all. }
  rewrite ent_later_pers. etrans; first apply ent_pers_idemp.
  apply ent_pers_mono.
  apply ent_wand_intro. etrans; last apply ent_wp_pure_steps.
  2: { apply rtc_pure_step_fill with (K := [AppLCtx _]). apply pure_step_val. done. }
  etrans; last apply ent_later_wp_pure_step.
  2: { apply pure_step_beta. }
  (* strip the later *)
  etrans. { apply ent_sep_split; first done. apply ent_later_intro. }
  rewrite -ent_later_pers. rewrite -ent_later_sep. apply ent_later_mono.
  (* use the assumption / get it into the right shape to use the hypothesis *)
  etrans.
  { apply ent_sep_split; last done. apply ent_all_pers. }
  rewrite ent_sep_comm. etrans; first apply ent_sep_true.
  apply ent_wand_elim.
  etrans; last apply ent_pers_elim.
  etrans; first apply Ha.
  apply (ent_all_elim v).
Qed.

(** Step-indexing in the IPM *)
Lemma ipm_later_sep_commuting P Q :
  ▷ (P ∗ Q) -∗ ▷ P ∗ ▷ Q.
Proof.
  (* automatically commutes the later around the separating conjunction *)
  iIntros "(HP & HQ)".

  Restart.
  iIntros "($ & $)".
Abort.

Lemma ipm_later_exists_commuting (Φ : nat → iProp) :
  ▷ (∃ n : nat, Φ n) -∗ ∃ n : nat, ▷ Φ n.
Proof.
  (* automatically commutes the later around the existential *)
  (* note: in general, this relies on the type that is existentially quantified over
    to be [Inhabited]. The IPM tactics will fail if an instance for that cannot be found. *)
  iIntros "(%n & Hn)".
Abort.

Lemma ipm_later_or_commuting P Q :
  ▷ (P ∨ Q) -∗ ▷ P ∨ ▷ Q.
Proof.
  (* automatically commutes the later around the or *)
  iIntros "[ HP | HQ ]".

  Restart.
  iIntros "[ $ | $ ]".
Abort.

Lemma ipm_later_next_1 P Q R `{!Persistent P} :
  ▷ P -∗ ▷ R -∗ ▷ Q.
Proof.
  iIntros "#HP HR".
  (* this will strip the later from all the assumptions *)
  iNext.
Abort.

(** The recursion lemma from above, proved with the IPM and Löb induction *)
Lemma ent_wp_rec v Φ (Ψ : val → val → iProp) e :
  (∀ v, (Φ v ∗ (∀ u, {{ Φ u }} (rec: "f" "x" := e) u {{ Ψ u }}) ⊢ WP subst "x" v (subst "f" (rec: "f" "x" := e) e) {{ Ψ v }})) →
  (Φ v ⊢ WP (rec: "f" "x" := e) v {{ Ψ v }}).
Proof.
  iIntros (Hs). iLöb as "IH" forall (v).
  iIntros "Hv".
  wp_pures. iApply Hs. iFrame "Hv".
  iIntros (v') "!> Hv'".
  by iApply "IH".
Qed.


(** The Z combinator *)
Section Z.
  Context (e : expr).
  Definition g : val := λ: "f", let: "f" := λ: "x", "f" "f" "x" in λ: "x", e.
  Definition Z_com : val := λ: "x", g g "x".

  Lemma Z_spec v Φ (Ψ : val → val → iProp) :
    (∀ v, (Φ v ∗ (∀ u, {{ Φ u }} Z_com u {{ Ψ u }}) ⊢ WP subst "x" v (subst "f" Z_com e) {{ Ψ v }})) →
    (Φ v ⊢ WP Z_com v {{ Ψ v }}).
  Proof.
    (* FIXME: exercise *)
  Admitted.
End Z.

Notation iPropO := (iPropO adequacy.heapΣ).
(** To define the recursive predicate [infinite_exec] formally (by taking a fixpoint), we need to invoke some machinery.
 *)
(** We first define the function of which we take the fixpoint (in [μ F. P], imagine that this is the function taking F and returning P).
 We use [exprO] instead of [expr], [iPropO] instead of [iProp], and [λne] and [-n>] to account for some of the details of Iris's algebraic step-indexed model which enables us to make this recursive definition.
  This will become clearer in a few weeks when we consider Iris's model.
 *)
Definition infinite_exec_pre (inf : exprO -n> iPropO) : exprO -n> iPropO :=
  (λne e, ∃ e', ⌜pure_step e e'⌝ ∗ ▷ inf e')%I.
(**
  Our recursive definition needs to be [Contractive], which essentially means that
  all recursive occurrences of the predicate are guarded by a ▷.
  This ensures that we can take the fixpoint.
   (For contractive definitions, Banach's fixpoint theorem ensures that there is a unique fixpoint).
*)
#[local] Instance infinite_exec_contractive : Contractive (infinite_exec_pre).
Proof. solve_contractive. Qed.
Definition infinite_exec := fixpoint infinite_exec_pre.

(* We prove a simple unfolding lemma for the recursive definition. *)
Lemma infinite_exec_unfold e :
  infinite_exec e ⊣⊢ infinite_exec_pre infinite_exec e.
Proof.
  apply (fixpoint_unfold infinite_exec_pre).
Qed.

Definition Omega : expr := ((λ: "x", "x" "x")%V (λ: "x", "x" "x")%V).
Lemma infinite_exec_Omega' :
  ⊢ infinite_exec Omega.
Proof.
  apply ent_löb. rewrite {2}infinite_exec_unfold /infinite_exec_pre /=.
  apply (ent_exist_intro Omega).
  etrans; first apply ent_sep_true. apply ent_sep_split; last done.
  apply ent_prove_pure. apply pure_step_beta.
Qed.

Lemma infinite_exec_Omega :
  ⊢ infinite_exec Omega.
Proof.
  iLöb as "IH".
  rewrite {2}infinite_exec_unfold /infinite_exec_pre /=.
  iExists Omega. iSplitR; last done.
  iPureIntro. apply pure_step_beta.
Qed.

Lemma infinite_wp_False' e :
  infinite_exec e ⊢ WP e {{ _, False }}.
Proof.
  (* FIXME: exercise *)
Admitted.
Lemma infinite_wp_False e :
  infinite_exec e ⊢ WP e {{ _, False }}.
Proof.
  (* FIXME: exercise *)
Admitted.



(** Diverge using higher-order state *)
Definition diverge_ho : expr :=
  let: "d" := ref (λ: "x", "x") in
  "d" <- (λ: "x", (!"d") "x");;
  !"d" #().

Lemma diverge_ho_diverges :
  ⊢ {{ True }} diverge_ho {{ _, False }}.
Proof.
  iIntros "_ !>". unfold diverge_ho.
  wp_alloc d as "Hd". wp_pures. wp_store.
  iLöb as "IH".
  wp_load. wp_pures. by iApply "IH".
Qed.

(** Landin *)
Definition landins_knot : val :=
  λ: "f",
    let: "x" := ref (λ: "x", #0) in
    let: "g" := (λ: "z", "f" (λ: "y", (!"x") "y") "z") in
    "x" <- "g";; "g".

Definition landinN := nroot .@ "landin".
Lemma landins_knot_spec (t : val) Φ Ψ :
  (∀ f : val, ⊢ {{ (∀ v : val, {{ Φ v }} f v {{ Ψ }}) }} t f {{ g, ∀ v, {{ Φ v }} g v {{ Ψ }} }}) →
  ⊢ {{ True }} landins_knot t {{ g, ∀ v, {{ Φ v }} g v {{ Ψ }} }}.
Proof.
  (* FIXME: exercise *)
Admitted.

(** * Impredicative invariants *)
Import impred_invariants.
(* [ent_inv_pers] and [ent_inv_alloc] hold unchanged *)
(* The opening rules that support impredicative invariants put a later ▷ around the contents [F]. *)
(*Check ent_inv_open.*)
(*Check inv_open.*)

Definition lazyintN := nroot .@ "lazyint".
Definition LazyInt (f : val) (n : Z) : iProp := WP (f #()) {{ w, ⌜w = #n⌝ }}%I.

Definition lazyint_add : val :=
  λ: "f" "g" <>,
    "f" #() + "g" #().
Lemma add_spec f n g m :
  ⊢ {{ LazyInt f n ∗ LazyInt g m }} lazyint_add f g {{ h, LazyInt h (n + m) }}.
Proof.
  iIntros "!> (Hf & Hg)". unfold lazyint_add. wp_pures.
  iApply ent_wp_value. unfold LazyInt. wp_pures.
  wp_bind (g _). iApply (ent_wp_wand' with "[Hf] Hg").
  iIntros (v) "->".
  wp_bind (f _). iApply (ent_wp_wand' with "[] Hf").
  iIntros (v) "->".
  wp_pures. by iApply ent_wp_value.
Qed.

Definition retrieve : val :=
  λ: "c", match: !"c" with
  InjL "cc" =>
    match: "cc" with
     InjL "f" => "c" <- InjR #();; InjL "f"
   | InjR "y" => InjR "y"
   end
 | InjR "cc" =>
   (* error case, we just diverge *)
   (rec: "rec" <> := "rec" #()) #()
  end.

Definition cache : val :=
  λ: "f",
  let: "c" := ref (InjL (InjL "f")) in
  λ: <>, let: "r" := retrieve "c" in
         match: "r" with
           InjL "f" => let: "y" := "f" #() in "c" <- InjL (InjR "y");; "y"
         | InjR "y" => "y"
         end.

Local Definition I (f: val) (n: Z) (l: loc) : iProp :=
  (((l ↦ InjLV (InjLV f) ∗ LazyInt f n) ∨ l ↦ InjLV (InjRV #n)) ∨ l ↦ InjRV #())%I.

Lemma retrieve_spec f n l N:
  ▷ I f n l ⊢ WP retrieve #l @ ⊤∖↑N {{ r, I f n l ∗ (⌜r = InjLV f⌝ ∗ LazyInt f n ∨ ⌜r = InjRV #n⌝) }}.
Proof.
  iIntros "I". unfold retrieve. wp_pure _.
  unfold I at 1. iDestruct "I" as "[[[Hl Hlzy]|Hl]|Hl]".
  - wp_load. wp_pures. wp_store. wp_pures. iApply wp_value.
    unfold I. eauto with iFrame.
  - wp_load. wp_pures. iApply wp_value.
    unfold I. eauto with iFrame.
  - wp_load. wp_pures. iClear "Hl".
    iLöb as "IH". wp_pure _. done.
Qed.

Lemma cache_spec f n :
  ⊢ {{ LazyInt f n }} cache f {{ g, □ LazyInt g n }}.
Proof.
  iIntros "!> Hlazy". unfold cache.
  wp_alloc l as "Hc". wp_pures.

  set (Name := lazyintN.@ l).
  iApply (inv_alloc Name (I f n l) with "[Hlazy Hc]").
  { unfold I. eauto with iFrame. }
  iIntros "#HInv".

  iApply wp_value.
  unfold LazyInt. iModIntro.
  wp_pures. wp_bind (retrieve _).
  iApply (inv_open with "HInv"); first set_solver.
  iIntros "I". iApply (wp_wand with "[I]").
  { by iApply retrieve_spec. }
  iIntros (r) "[I Hr]". iFrame "I".
  iDestruct "Hr" as "[[-> Hlzy]|->]"; wp_pures; last first.
  - iApply wp_value. done.
  - wp_bind (f _). iApply (wp_wand with "Hlzy").
    iIntros (v) "->". wp_pures.
    wp_bind (#l <- _)%E.
    iApply (inv_open with "HInv"); first set_solver.
    iIntros "I"; iDestruct "I" as "[[[>Hl Hlzy]|>Hl]|>Hl]"; wp_store;
      iApply wp_value; iSplitL; unfold I; eauto with iFrame.
    all: wp_pures; iApply wp_value; done.
Qed.

Definition cache' : val :=
  λ: "f",
  let: "c" := ref (InjL "f") in
  λ: <>, match: !"c" with
          InjL "g" =>
            let: "k" := "g" #() in "c" <- "k";; "k"
          | InjR "k" =>  "k"
          end.


Definition E : expr :=
  let: "z" := ref (λ: <>, #0) in
  let: "r" := ref #true in
  let: "z'" :=
    λ: <>, (assert (!"r");; "r" <- #false;; !"z") #() in
  let: "c" := cache' "z'" in
  "z" <- "c";; "c" #().



Lemma E_safe :
  (∀ f n, {{ LazyInt f n }} cache' f {{ g, □ LazyInt g n }}) ⊢
  {{ True }} E {{ _, True }}.
Proof.
  iIntros "#Hcache !> _". rewrite /E. wp_alloc z as "Hz".
  iAssert (□ LazyInt (λ: <>, #0) 0)%I as "Hlazy".
  { iModIntro. rewrite /LazyInt. wp_pures. by iApply wp_value. }
  wp_pures. wp_alloc r as "Hr". wp_pures.
  pose (λ: <>, (assert (! #r);; #r <- #false;; ! #z) #())%V as h. fold h.
  iApply (inv_alloc nroot (∃ f, z ↦ f ∗ □ LazyInt f 0) with "[Hz]").
  { iExists _. iFrame. done. }
  iIntros "#I". iClear "Hlazy".
  iAssert (LazyInt h 0) with "[Hr]" as "Hh".
  { rewrite /LazyInt /h. wp_pure _.
    (* the code here is a bit akward due to the
       fact that we need to close invariants in the
       post *)
    wp_bind (_;; _ ;; _)%E.
    iApply (inv_open with "I"); first set_solver.
    iIntros "Inv". rewrite /h. wp_pures.
    iDestruct "Inv" as "(%f & Hz & #Hf)".
    wp_load. wp_pures. wp_store. wp_load.
    iApply wp_value.
    (* we close the invariant again *)
    iSplitL "Hz"; first eauto with iFrame.
    iApply "Hf". }
    (* since h is a lazy int, we can cache it *)
    wp_bind (cache' h).
    iApply (wp_wand with "[Hh]"); first by iApply "Hcache".
    iIntros (c) "#Hc".

    wp_pures. wp_bind (_ <- _)%E.
    iApply (inv_open with "I"); first set_solver.
    iIntros "(%f & >Hz & Hlazy)". wp_store.
    iApply wp_value.

    iSplitL "Hz"; first by eauto with iFrame.
    wp_pures. iApply (wp_wand with "Hc").
    iIntros (v) "_". done.
Qed.


(** Let's see what happens if we symbolically execute E.
   We do it inside of a weakest pre, because we can use all
   of Iris's tactics. If you do not trust this setup and
   believe some the proof takes a wrong turn somewhere, you
   can always use the operatinal semantics itself to show
   that E will reach a stuck state. *)
Lemma E_not_safe:
  ⊢ {{ True }} E {{ _, True }}.
Proof.
  iIntros "!> _". rewrite /E. wp_alloc z as "Hz".
  wp_pures. wp_alloc r as "Hr". wp_pures.
  pose (λ: <>, (assert (! #r);; #r <- #false;; ! #z) #())%V as h. fold h.
  rewrite /cache'.
  wp_pures. wp_alloc l as "Hl".
  wp_pures. wp_store.
  wp_pures. wp_load.
  wp_pures. rewrite {2}/h.
  wp_pures. wp_load. wp_pures.
  wp_store. wp_load. wp_pures.
  wp_load. wp_pures. rewrite {2}/h.
  wp_pures. wp_load. wp_pures.
  wp_bind (#0 #0)%E.

  (* Whooops *)
Abort.


Definition lazyint_two : val :=
  λ: "f1" "f2" "i",
    let: "c" := cache "i" in
    "f1" "c" + "f2" "c".

Lemma lazyint_two_spec (h1 h2 f : val) n :
  (∀ f n, {{ LazyInt f n }} h1 f {{ v, ∃ m : Z, ⌜v = #m⌝ }}) -∗
  (∀ f n, {{ LazyInt f n }} h2 f {{ v, ∃ m : Z, ⌜v = #m⌝ }}) -∗
  {{ LazyInt f n }} lazyint_two h1 h2 f {{ v, ∃ m, ⌜v = #m⌝ }}.
Proof.
  (* FIXME: exercise *)
Admitted.


(** Exercise: derive the invariant rule for timeless propositions *)
Lemma inv_open_timeless N E F `{!Timeless F} e Φ :
  ↑N ⊆ E →
  inv N F -∗
  (F -∗ WP e @ (E ∖ ↑N) {{ v, ▷ F ∗ Φ v }})%I -∗
  WP e @ E {{ Φ }}.
Proof.
  (* FIXME: exercise *)
Admitted.
