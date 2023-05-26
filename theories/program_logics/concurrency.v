From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.bi Require Import fractional.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Export primitive_laws proofmode.
From iris.algebra Require Import excl auth numbers.
From iris.base_logic.lib Require Import ghost_var.
From iris.prelude Require Import options.

(** * Concurrency *)

(** Our new notion of steps to account for concurrency.
  [prim_step e1 σ1 κs e2 σ2 efs] means that (e1, σ1) steps to (e2, σ2), forking off threads [efs].
  You can ignore the κs (it relates to another feature, prophecy variables, that we are not going to get into in this course).
  (it corresponds to the notion of "base steps" →_b  in the lecture notes)
 *)
(*Check prim_step.*)
(** [step] lifts this reduction to thread pools. *)
(*Check step.*)

(*Check ForkS.*)
(** In Iris's HeapLang, CAS is encoded in terms of another primitive: CmpXchg, namely, "compare and exchange".
  The difference to CAS is that it returns not only a Boolean flag (indicating success or failure), but rather
  a pair that also contains the old/current value.
*)
(*Print CAS.*)
(*Check CmpXchgS.*)

Global Notation "{{ P } } e {{ Φ } }" := (□(P%I -∗ WP e {{ Φ%I }}))%I
  (at level 20, P, e, Φ at level 200,
  format "{{  P  } }  e  {{  Φ  } }") : stdpp_scope.

Global Notation "{{ P } } e {{ v , Q } }" := (□ (P%I -∗ WP e {{ v, Q%I }}))%I
  (at level 20, P, e, Q at level 200,
  format "{{  P  } }  e  {{  v ,  Q  } }") : stdpp_scope.

(** Weakest Precondition Rules *)
(*Check wp_cmpxchg_fail.*)
(*Check wp_cmpxchg_suc.*)
(*Check wp_fork.*)

Definition assert (e : expr) : expr :=
  if: e then #() else #0 #0.

Section cas.
  Context `{heapGS Σ}.

  Definition cas_example : expr :=
    let: "x" := ref #0 in
    CAS "x" #0 #42;;
    !"x".

  Lemma cas_example_spec :
    ⊢ {{ True }} cas_example {{ v, ⌜v = #42⌝}}.
  Proof.
    iIntros "!> _". unfold cas_example.

    (* we use the [wp_cmpxchg_suc] tactic to prove that the CAS is successful *)
    wp_alloc l as "Hl".
    wp_cmpxchg_suc.

    (* or: *)
    (*wp_cmpxchg as Hsuc | Hfail. *)
    (*2: { congruence. }*)

    wp_pures. wp_load. eauto.
  Qed.

  Definition fork_example : expr :=
    let: "x" := ref #0 in
    Fork ("x" <- #42).
  Lemma fork_example_spec :
    ⊢ {{ True }} fork_example {{ v, True }}.
  Proof.
    iIntros "!> _". unfold fork_example.
    wp_alloc l as "Hl". wp_pures.
    (* We have to split the resources up among the threads *)
    iApply (wp_fork with "[Hl]").
    - iNext. wp_store. eauto.
    - eauto.
  Qed.
End cas.

(** Our invariant opening rule now require the expression around which we open the invariant to be [Atomic],
  to ensure that no other thread can notice that the invariant does not hold while we operate on it. *)
Lemma wp_inv_open `{heapGS Σ} E N e P Φ :
  ↑N ⊆ E →
  Atomic WeaklyAtomic e →
  inv N P -∗
  (▷ P -∗ WP e @ E ∖ ↑N {{ v, ▷ P ∗ Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (??) "Hinv Hcont". iInv "Hinv" as "HP" "Hcl".
  iApply (wp_wand with "(Hcont HP)").
  iIntros (v) "[HP Hv]". by iMod ("Hcl" with "HP").
Qed.

Section coin_flip.
  Context `{heapGS Σ}.

  Definition flip_coin : expr :=
    let: "coin" := ref #0 in
    Fork ("coin" <- #1);;
    !"coin".

  Definition coinN : namespace := nroot .@ "coin".

  Definition coinInv (l : loc) : iProp Σ :=
    l ↦ #0 ∨ l ↦ #1.

  Lemma flip_coin_spec :
    ⊢ {{ True }} flip_coin {{ v, ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}.
  Proof.
    iIntros "!> _". unfold flip_coin.
    wp_alloc l as "Hl". wp_pures.

    iMod (inv_alloc coinN _ (coinInv l) with "[$Hl]") as "#Hinv".
    wp_bind (Fork _).
    iApply wp_fork.
    { iNext.
      iApply (wp_inv_open with "Hinv"); first set_solver.
      iIntros "Hi".
      (* alternatively, we can use Iris's [iInv] tactic *)
      (*iInv "Hinv" as "Hi" "Hclose". *)
      iDestruct "Hi" as "[>Hl | >Hl]".
      - wp_store. (* iMod ("Hclose" with "[$Hl]") as "_". *)
        eauto with iFrame.
      - wp_store. (* iMod ("Hclose" with "[$Hl]") as "_". *)
        eauto with iFrame.
    }
    iNext. wp_pures.

    iApply (wp_inv_open with "Hinv"); first set_solver.
    iIntros "[>Hl | >Hl]".
    all: wp_load; eauto with iFrame.
  Qed.
End coin_flip.

(* Lock implementation *)
Definition newlock : val :=
  λ: <>, ref #false.
Definition try_acquire : val :=
  λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" :=
    if: try_acquire "l" then #() else "acquire" "l".
Definition release : val :=
  λ: "l", "l" <- #false.

Section spin_lock.
  Context `{heapGS Σ}.


  (** Lock specification *)
  Definition lockN : namespace := nroot .@ "lock".
  Definition lock_inv (l : loc) (P : iProp Σ) : iProp Σ :=
    ((l ↦ #false ∗ P) ∨ (l ↦ #true))%I.
  Definition is_lock (v : val) (P : iProp Σ) : iProp Σ :=
    (∃ l : loc, ⌜v = #l⌝ ∗ inv lockN (lock_inv l P))%I.

  Instance is_lock_pers v P : Persistent (is_lock v P).
  Proof. apply _. Qed.

  Lemma newlock_spec P :
    ⊢ {{ P }} newlock #() {{ v, is_lock v P }}.
  Proof.
    iIntros "!> HP". unfold newlock. wp_pures.
    wp_alloc l as "Hl".
    iMod (inv_alloc lockN _ (lock_inv l P) with "[Hl HP]") as "Hinv".
    { iNext. iLeft. iFrame. }
    iModIntro. iExists l. eauto with iFrame.
  Qed.

  Lemma try_acquire_spec v P :
    ⊢ {{ is_lock v P }} try_acquire v {{ w, (⌜w = #true⌝ ∗ P) ∨ ⌜w = #false⌝ }}.
  Proof.
    iIntros "!> Hlock". unfold try_acquire. wp_pures.
    iDestruct "Hlock" as "(%l & -> & #Hinv)".
    (* NOTE: This will fail if we don't bind first. Try it!
      In a concurrent setting, we can only open invariants around atomic expressions that terminate
      in one step.
     *)
    (*iMod (inv_acc with "Hinv") as "[Hi Hclose]".*)
    wp_bind (CmpXchg _ _ _).
    iApply (wp_inv_open with "Hinv"); first set_solver.
    iIntros "[(>Hl & HP) | >Hl]".
    - (* we can acquire the lock *)
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl"; first iFrame.
      wp_pures. eauto with iFrame.
    - (* we fail *)
      wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first iFrame.
      wp_pures. eauto with iFrame.
  Qed.

  Lemma acquire_spec v P :
    ⊢ {{ is_lock v P }} acquire v {{ w, ⌜w = #()⌝ ∗ P }}.
  Proof.
    iIntros "!> #Hlock". iLöb as "IH". unfold acquire.
    wp_pures. wp_bind (try_acquire _).
    iApply (wp_wand with "[Hlock]").
    { by iApply try_acquire_spec. }
    iIntros (w) "[(-> & HP) | ->]".
    - wp_pures. eauto with iFrame.
    - wp_pure _. by iApply "IH".
  Qed.

  Lemma release_spec v P :
    ⊢ {{ is_lock v P ∗ P }} release v {{ w, True }}.
  Proof.
    iIntros "!> (#Hlock & HP)". unfold release.
    wp_pures.
    iDestruct "Hlock" as "(%l & -> & #Hinv)".
    iApply (wp_inv_open with "Hinv"); first set_solver.
    iIntros "[(>Hl & _) | >Hl]".
    all: wp_store; iModIntro; iSplitL; last done.
    all: iLeft; eauto with iFrame.
  Qed.
End spin_lock.

(** Exercise: with notation *)
Definition with_lock : val :=
  λ: "l" "e",
  (acquire "l";; let: "x" := "e" #()in release "l";; "x")%E.
Definition with_lock' e1 e2 := (with_lock (e1: expr) (λ: <>, e2)%E).
Section with_lock.
  Context `{heapGS Σ}.

  Lemma with_lock_spec Φ (l c : val) P :
    is_lock l P -∗
    (P -∗ WP c #() {{ v, P ∗ Φ v }}) -∗
    WP with_lock l c {{ Φ }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.
End with_lock.

(** Exclusive Ghost Token *)
Definition lockR : cmra := exclR unitO.
Class lockG Σ :=
  LockG { lockG_inG : inG Σ lockR; }.
#[export] Existing Instance lockG_inG.
Definition lockΣ : gFunctors := #[ GFunctor lockR ].
Global Instance subG_lockΣ Σ : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lock_lemmas.
  Context `{lockG Σ}.
  Definition locked γ := own γ (Excl ()).
  Lemma locked_alloc :
    ⊢ |==> ∃ γ, locked γ.
  Proof.
    iApply own_alloc. done.
  Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.
  Lemma locked_exclusive γ : locked γ -∗ locked γ -∗ False.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (own_valid_2 with "Hl1 Hl2") as %Ha. done.
  Qed.
End lock_lemmas.

(** Exercise: Exclusive locks *)
Section excl_spin_lock.
  Context `{heapGS Σ} `{lockG Σ}.

  Definition is_excl_lock (v : val) (γ : gname) (P : iProp Σ) : iProp Σ :=
        is_lock v P (* TODO *)
  .

  Instance is_excl_lock_pers v γ  P : Persistent (is_excl_lock v γ P).
  Proof. apply _. Qed.

  Lemma newlock_spec' P :
    ⊢ {{ P }} newlock #() {{ v, ∃ γ, is_excl_lock v γ P }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma acquire_spec' v γ P :
    ⊢ {{ is_excl_lock v γ P }} acquire v {{ w, ⌜w = #()⌝ ∗ locked γ ∗ P }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma release_spec' v γ P :
    ⊢ {{ is_excl_lock v γ P ∗ locked γ ∗ P }} release v {{ w, True }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma really_exclusive v γ P :
    ⊢ {{ is_excl_lock v γ P ∗ locked γ }} assert (!v = #true) {{ _, True }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.
End excl_spin_lock.


(** Parallel composition *)
Definition await : val :=
  rec: "await" "x" :=
    if: !"x" then #() else "await" "x".
Definition comp : val :=
  λ: "e1" "e2",
  let: "r" := ref #false in
  Fork ("e2" #();; "r" <- #true);;
  "e1" #();;
  await "r".

(** Exercise: Prove the following specification for parallel composition *)
Section para_comp.
  Context `{heapGS Σ} `{lockG Σ}.

  Definition parN := nroot .@ "par".

  Lemma parallel_spec (e1 e2 : val) Q1 Q2 :
    WP e1 #() {{ _, Q1 }} -∗
    WP e2 #() {{ _, Q2 }} -∗
    WP comp e1 e2 {{ _, Q1 ∗ Q2 }}.
  Proof using Type*.
    (* FIXME: exercise *)
  Admitted.
End para_comp.

Definition inc_counter : val :=
  λ: "l" "r", with_lock "l" (λ: <>, "r" <- !"r" + #1).
Definition parallel_counter : expr :=
  let: "r" := ref #0 in
  let: "l" := newlock #() in
  comp (λ: <>, inc_counter "l" "r")
       (λ: <>, inc_counter "l" "r");;
  with_lock "l" (λ: <>, !"r").

Section counter.
  Context `{heapGS Σ} `{lockG Σ} `{ghost_varG Σ nat}.


  (** You may find the GhostVariable algebra useful.
    Iris already provides it, and you can use the following lemmas.
   *)
  (*Check ghost_var_alloc.*)
  (*Check ghost_var_agree.*)
  (*Check ghost_var_update.*)
  (* Note: Iris supports splitting a ghost variable into halves via the usual destruct patterns.
    For example: *)
  Lemma gvar_split_halves γ (a : nat) :
    ghost_var γ 1 a -∗ ghost_var γ (1/2) a ∗ ghost_var γ (1/2) a.
  Proof.
    iIntros "[H1 H2]". iFrame.
  Qed.

  Lemma parallel_counter_spec :
    ⊢ {{ True }} parallel_counter {{ v, ⌜v = #2⌝ }}.
  Proof using Type*.
    (* FIXME: exercise *)
  Admitted.
End counter.

(** Exercise: Mutex *)
Definition mkmutex : val :=
  λ: "d", (newlock #(), ref "d").
Definition acquire_mutex : val :=
  λ: "m", acquire (Fst "m");; (Snd "m", (λ: <>, release (Fst "m"))).

Section mutex.
  Context `{heapGS Σ}.

  Notation "l '↦:' P" := (∃ v : val, l ↦ v ∗ P v)%I (at level 40) : stdpp_scope.

  Definition is_mutex (v : val) (P : val → iProp Σ) : iProp Σ :=
         True 
  .
  Instance is_mutex_pers v P : Persistent (is_mutex v P).
  Proof. apply _. Qed.

  Lemma mkmutex_spec P (v : val) :
    ⊢ {{ P v }} mkmutex v {{ v, is_mutex v P }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.

  Lemma acquire_mutex_spec P (v : val) :
    ⊢ {{ is_mutex v P }}
        acquire_mutex v
      {{ w, ∃ (l : loc) (rl : val), ⌜w = (#l, rl)%V⌝ ∗ l ↦: P ∗ {{ l ↦: P }} rl #() {{ _, True }} }}.
  Proof.
    (* FIXME: exercise *)
  Admitted.
End mutex.

(** Exercise: Channels *)
Definition await'': val :=
  rec: "await" "f" := if: "f" #() then #() else "await" "f".

Notation await' e  := (await'' (λ: <>, e)%E).


Definition unwrap : val :=
  λ: "o", match: "o" with NONE => assert (#false) | SOME "a" => "a" end.


Lemma await'_spec {Σ} `{!heapGS Σ} e (P: iProp Σ) Q:
  {{P}} e {{v, (⌜v = #true⌝ ∗ Q #()) ∨ (⌜v = #false⌝ ∗ P)}} ⊢
  {{P}} await'' (λ: <>, e)%V {{v, Q v}} .
Proof.
  iIntros "#hoare !> P". iLöb as "IH".
  rewrite {2}/await''. wp_pures.
  wp_bind e. iApply (wp_wand with "(hoare P)").
  iIntros (v) "[[-> Q]|[-> P]]".
  - wp_pures. iModIntro. done.
  - fold await''. wp_pures. by iApply "IH".
Qed.

Lemma unwrap_spec {Σ} `{!heapGS Σ} v w Φ:
  v = SOMEV w →
  Φ w ⊢ WP unwrap v {{ Φ }} .
Proof.
  intros ->. unfold unwrap.
  iIntros "Hpost". wp_pures. done.
Qed.



(** We represent channels as tuples (l_s, l_r, wait) containing
    a lock l_s for the sending side,
    a lock l_r for the receiving side,
    and a data field containing (in an option) the data that is currently being sent.
 *)
Definition newchan : val :=
  λ: <>,
    (newlock #(), newlock #(), ref NONE).

Definition send : val :=
  λ: "c" "v",
    let: "l_s" := Fst (Fst "c") in
    let: "l_r" := Snd (Fst "c") in
    let: "data" := Snd "c" in

    with_lock' "l_s" (
      assert (!"data" = NONE);;
      (* send the data *)
      "data" <- SOME "v";;
      (* await the receiver to acknowledge it  *)
      await' (!"data" = NONE)
    ).


Definition receive : val :=
  λ: "c",
    let: "l_s" := Fst (Fst "c") in
    let: "l_r" := Snd (Fst "c") in
    let: "data" := Snd "c" in

    with_lock' "l_r" (
      await' (!"data" ≠ NONE);;
      let: "k" := unwrap (!"data") in
      "data" <- NONE;;
      "k"
    ).


Section channel_spec.
  Context `{heapGS Σ} `{lockG Σ}.

  (* [Pc] is a predicate that values sent over the channel must satisfy *)
  Context (Pc : val → iProp Σ) `{Pers: !∀ v, Persistent (Pc v)}.


  (* We reuse the exclusive locked ghost state from above *)
  Notation "●_ γ" := (locked γ) (at level 60) : stdpp_scope.
  Section invariants.
    Context (data: loc) (l_s l_r: val) (s1 s2 r1 r2: gname).

    Definition is_sender : iProp Σ :=
      is_lock l_s (●_s1).
    Definition is_receiver : iProp Σ :=
      is_lock l_s (●_r1).

    Definition channelN := nroot .@ "chan".
    Definition channel_inv : iProp Σ :=
        (●_s2 ∗ ●_r2 ∗ data ↦ NONEV)
      ∨ (●_s1 ∗ ●_r2 ∗ (∃ v: val, data ↦ SOMEV v ∗ Pc v))
      ∨ (●_s1 ∗ ●_r1 ∗ (∃ v: val, data ↦ SOMEV v ∗ Pc v))
      ∨ (●_s1 ∗ ●_r2 ∗ data ↦ NONEV).

    Global Instance is_sender_persistent :
      Persistent (is_sender).
    Proof. apply _. Qed.
    Global Instance is_receiver_persistent :
      Persistent (is_receiver).
    Proof. apply _. Qed.
  End invariants.

  Definition is_channel (v : val) : iProp Σ :=
    ∃ (l_s l_r : val) (data : loc) (s1 s2 r1 r2: gname),
      ⌜v = (l_s, l_r, #data)%V⌝ ∗
      is_sender l_s s1 ∗
      is_receiver l_r r1 ∗
      inv channelN (channel_inv data s1 s2 r1 r2).
  Global Instance is_channel_persistent v :
    Persistent (is_channel v).
  Proof. apply _. Qed.

  Lemma newchan_spec :
    ⊢ {{ True }} newchan #() {{ v, is_channel v }}.
  Proof using Type*.
    (* FIXME: exercise *)
  Admitted.

  Lemma send_spec v d :
    ⊢ {{ is_channel v ∗ Pc d }} send v d {{ v, ⌜v = #()⌝ }}.
  Proof using Pers.
    (* FIXME: exercise *)
  Admitted.

  Lemma receive_spec v :
    ⊢ {{ is_channel v }} receive v {{ d, Pc d }}.
  Proof using Pers.
    (* FIXME: exercise *)
  Admitted.
End channel_spec.
