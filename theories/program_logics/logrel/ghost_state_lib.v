From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.base_logic.lib Require Import mono_nat ghost_var ghost_map.
From semantics.pl Require Import invariant_lib.
From semantics.pl.heap_lang Require Import primitive_laws proofmode.
From iris.algebra Require Import csum excl agree.
From iris.prelude Require Import options.

Section updates.
  Context `{heapGS Σ}.

  Implicit Types (P Q : iProp Σ).

  Lemma upd_return P :
    P -∗ |==> P.
  Proof.
    by iIntros "$".
  Qed.

  Lemma upd_bind P Q :
    (|==> P) -∗
    (P -∗ |==> Q) -∗
    |==> Q.
  Proof.
    iIntros ">HP HQ". by iApply "HQ".
  Qed.

  Lemma upd_wp e Φ :
    (|==> WP e {{ Φ }}) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros ">$".
  Qed.
End updates.


(** Some ghost theories are below *)

(** MonoNat *)
Section mononat.
  Context `{heapGS Σ} `{mono_natG Σ}.

  Definition mono_def γ n := mono_nat_auth_own γ 1%Qp n.
  Definition mono_aux : seal (@mono_def). Proof. by eexists. Qed.
  Definition mono := mono_aux.(unseal).
  Definition mono_eq : @mono = @mono_def := mono_aux.(seal_eq).

  Definition lb_def := mono_nat_lb_own.
  Definition lb_aux : seal (@lb_def). Proof. by eexists. Qed.
  Definition lb := lb_aux.(unseal).
  Definition lb_eq : @lb = @lb_def := lb_aux.(seal_eq).

  Lemma mono_nat_make_bound γ n :
    mono γ n -∗ lb γ n.
  Proof.
    rewrite mono_eq lb_eq.
    iApply mono_nat_lb_own_get.
  Qed.

  Lemma mono_nat_use_bound γ n m :
    mono γ n -∗ lb γ m -∗ ⌜n ≥ m⌝.
  Proof.
    rewrite mono_eq lb_eq.
    iIntros "Hauth Hlb". iPoseProof (mono_nat_lb_own_valid with "Hauth Hlb") as "(_ & $)".
  Qed.

  Lemma mono_nat_increase_val γ n :
    mono γ n -∗ |==> mono γ (S n).
  Proof.
    rewrite mono_eq.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "($ & _)"; eauto.
  Qed.

  Lemma mono_nat_new n :
    ⊢ |==> ∃ γ, mono γ n.
  Proof.
    rewrite mono_eq.
    iMod (mono_nat_own_alloc n) as "(%γ & ? & _)"; eauto with iFrame.
  Qed.

  Global Instance mono_nat_lb_persistent γ n : Persistent (lb γ n).
  Proof. rewrite lb_eq. apply _. Qed.
  Global Instance mono_nat_lb_timeless γ n : Timeless (lb γ n).
  Proof. rewrite lb_eq. apply _. Qed.
  Global Instance mono_nat_mono_timeless γ n : Timeless (mono γ n).
  Proof. rewrite mono_eq. apply _. Qed.
End mononat.


(** Half algebra: provides two halves *)
Class halvesG Σ (A : Type) := HalvesG { halvesG_ghost_varG : ghost_varG Σ A; }.
#[export] Existing Instance halvesG_ghost_varG.
Definition halvesΣ A : gFunctors := ghost_varΣ A.
Global Instance subG_halvesΣ Σ A : subG (halvesΣ A) Σ → halvesG Σ A.
Proof. solve_inG. Qed.
Section half.
  Context {A : Type}.
  Context `{halvesG Σ A}.

  Definition ghalf_def γ (a : A) := ghost_var γ (1/2)%Qp a.
  Definition ghalf_aux : seal (@ghalf_def). Proof. by eexists. Qed.
  Definition ghalf := ghalf_aux.(unseal).
  Definition ghalf_eq : @ghalf = @ghalf_def := ghalf_aux.(seal_eq).

  Lemma ghalves_alloc a :
    ⊢ |==> ∃ γ, ghalf γ a ∗ ghalf γ a.
  Proof.
    iMod (ghost_var_alloc a) as "(%γ & H1 & H2)".
    rewrite ghalf_eq; eauto with iFrame.
  Qed.

  Lemma ghalves_agree γ a b :
    ghalf γ a -∗ ghalf γ b -∗ ⌜a = b⌝.
  Proof.
    rewrite !ghalf_eq. iApply ghost_var_agree.
  Qed.

  Lemma ghalves_update γ a b c :
    ghalf γ a -∗ ghalf γ b -∗ |==> ghalf γ c ∗ ghalf γ c.
  Proof.
    rewrite !ghalf_eq /ghalf_def.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->.
    by iMod (ghost_var_update_halves c with "H1 H2") as "[$ $]".
  Qed.

  Global Instance ghalf_timeless γ a : Timeless (ghalf γ a).
  Proof. rewrite ghalf_eq. apply _. Qed.
End half.

Notation "'left'" := (ghalf) (only parsing).
Notation "'right'" := (ghalf) (only parsing).

(** One shot *)
Class oneshotG Σ (A : Type) :=
  OneShotG { oneshotG_inG : inG Σ (csumR (exclR unitO) (agreeR (leibnizO A))); }.
#[export] Existing Instance oneshotG_inG.
Definition oneshotΣ A : gFunctors := #[ GFunctor (csumR (exclR unitO) (agreeR (leibnizO A))) ].
Global Instance subG_oneshotΣ Σ A : subG (oneshotΣ A) Σ → oneshotG Σ A.
Proof. solve_inG. Qed.
Section oneshot.
  Context {A : Type}.
  Context `{oneshotG Σ A}.

  Definition os_pending_def γ := own γ (Cinl (Excl ())).
  Definition os_pending_aux : seal (@os_pending_def). Proof. by eexists. Qed.
  Definition os_pending := os_pending_aux.(unseal).
  Definition os_pending_eq : @os_pending = @os_pending_def := os_pending_aux.(seal_eq).


  Definition os_shot_def γ (a : A) := own γ (Cinr (to_agree (a : leibnizO A))).
  Definition os_shot_aux : seal (@os_shot_def). Proof. by eexists. Qed.
  Definition os_shot := os_shot_aux.(unseal).
  Definition os_shot_eq : @os_shot = @os_shot_def := os_shot_aux.(seal_eq).

  Lemma os_pending_alloc :
    ⊢ |==> ∃ γ, os_pending γ.
  Proof.
    rewrite os_pending_eq. iApply own_alloc. done.
  Qed.

  Lemma os_pending_shoot γ a :
    os_pending γ -∗ |==> os_shot γ a.
  Proof.
    rewrite os_pending_eq os_shot_eq.
    iApply own_update.
    apply cmra_update_exclusive.
    done.
  Qed.

  Global Instance os_shot_persistent γ a : Persistent (os_shot γ a).
  Proof. rewrite os_shot_eq. apply _. Qed.

  Lemma os_pending_shot_False γ a :
    os_pending γ -∗ os_shot γ a -∗ False.
  Proof.
    iIntros "H1 H2". rewrite os_pending_eq os_shot_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    done.
  Qed.

  Lemma os_pending_pending_False γ :
    os_pending γ -∗ os_pending γ -∗ False.
  Proof.
    iIntros "H1 H2". rewrite os_pending_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    done.
  Qed.

  Lemma os_shot_agree γ a b :
    os_shot γ a -∗ os_shot γ b -∗ ⌜a = b⌝.
  Proof.
    iIntros "H1 H2". rewrite os_shot_eq.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply to_agree_op_inv_L in Hv.
  Qed.

  Global Instance os_shot_timeless γ a : Timeless (os_shot γ a).
  Proof. rewrite os_shot_eq. apply _. Qed.
  Global Instance os_pending_timeless γ : Timeless (os_pending γ).
  Proof. rewrite os_pending_eq. apply _. Qed.
End oneshot.

(** Agreement maps *)
Class agmapG Σ (A B : Type) `{Countable A} :=
  AgMapG { agmapG_inG : ghost_mapG Σ A B; }.
#[export] Existing Instance agmapG_inG.
Definition agmapΣ A B `{Countable A} : gFunctors := ghost_mapΣ A B.
Global Instance subG_agmapΣ Σ A B `{Countable A} : subG (agmapΣ A B) Σ → agmapG Σ A B.
Proof. solve_inG. Qed.
Section oneshot.
  Context {A B : Type} `{Countable A}.
  Context `{agmapG Σ A}.

  Definition agmap_auth_def γ M := ghost_map_auth γ 1 M.
  Definition agmap_auth_aux : seal (@agmap_auth_def). Proof. by eexists. Qed.
  Definition agmap_auth := agmap_auth_aux.(unseal).
  Definition agmap_auth_eq : @agmap_auth = @agmap_auth_def := agmap_auth_aux.(seal_eq).

  Definition agmap_elem_def γ a b := ghost_map_elem γ a DfracDiscarded b.
  Definition agmap_elem_aux : seal (@agmap_elem_def). Proof. by eexists. Qed.
  Definition agmap_elem := agmap_elem_aux.(unseal).
  Definition agmap_elem_eq : @agmap_elem = @agmap_elem_def := agmap_elem_aux.(seal_eq).

  Lemma agmap_auth_alloc_empty :
    ⊢ |==> ∃ γ, agmap_auth γ ∅.
  Proof.
    rewrite agmap_auth_eq. iApply ghost_map_alloc_empty.
  Qed.

  Lemma agmap_auth_insert {γ M} a b :
    M !! a = None →
    agmap_auth γ M -∗ |==>
    agmap_auth γ (<[a := b]> M) ∗ agmap_elem γ a b.
  Proof.
    rewrite agmap_auth_eq agmap_elem_eq.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert a b with "Hauth") as "($ & He)"; first done.
    iApply (ghost_map_elem_persist with "He").
  Qed.

  Lemma agmap_auth_lookup {γ M} a b :
    agmap_auth γ M -∗ agmap_elem γ a b -∗ ⌜M !! a = Some b⌝.
  Proof.
    rewrite agmap_auth_eq agmap_elem_eq.
    iApply ghost_map_lookup.
  Qed.

  Lemma agmap_elem_agree γ k a b :
    agmap_elem γ k a -∗ agmap_elem γ k b -∗ ⌜a = b⌝.
  Proof.
    rewrite agmap_elem_eq. iApply ghost_map_elem_agree.
  Qed.

  Global Instance agmap_elem_persistent γ a b : Persistent (agmap_elem γ a b).
  Proof. rewrite agmap_elem_eq. apply _. Qed.
  Global Instance agmap_elem_timeless γ a b : Timeless (agmap_elem γ a b).
  Proof. rewrite agmap_elem_eq. apply _. Qed.
  Global Instance agmap_auth_timeless γ M : Timeless (agmap_auth γ M).
  Proof. rewrite agmap_auth_eq. apply _. Qed.
End oneshot.
