(** Adapted from https://gitlab.mpi-sws.org/iris/reloc/-/blob/master/theories/typing/contextual_refinement.v *)
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import proofmode.
From semantics.pl.reloc Require Export syntactic logrel fundamental adequacy.

(** * Proving contextual refinement *)

Inductive ctx_item :=
  (* Base lambda calculus *)
  | CTX_Lam (x : binder)
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  (* Base types and their operations *)
  | CTX_UnOp (op : un_op)
  | CTX_BinOpL (op : bin_op) (e2 : expr)
  | CTX_BinOpR (op : bin_op) (e1 : expr)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  (* Products *)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  (* Sums *)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  (* Heap *)
  | CTX_Alloc
  | CTX_Load
  | CTX_StoreL (e2 : expr)
  | CTX_StoreR (e1 : expr)
  (* Recursive Types *)
  | CTX_Roll
  | CTX_Unroll
  (* Polymorphic Types *)
  | CTX_TLam
  | CTX_TApp
  (* Existential types *)
  | CTX_Pack
  | CTX_UnpackL (x : binder) (e2 : expr)
  | CTX_UnpackR (x : binder) (e1 : expr)
.

Definition fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  (* Base lambda calculus *)
  | CTX_Lam x => Lam x e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  (* Base types and operations *)
  | CTX_UnOp op => UnOp op e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  (* Products *)
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  (* Sums *)
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  (* Heap *)
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  (* Recursive & polymorphic types *)
  | CTX_Roll => Roll e
  | CTX_Unroll => Unroll e
  | CTX_TLam => TLam e
  | CTX_TApp => TApp e
  | CTX_Pack => Pack e
  | CTX_UnpackL x e1 => Unpack e x e1
  | CTX_UnpackR x e0 => Unpack e0 x e
  end.

Definition ctx := list ctx_item.

Definition fill_ctx (K : ctx) (e : expr) : expr := foldr fill_ctx_item e K.

(** typed ctx *)
Inductive typed_ctx_item :
    ctx_item → nat → gmap string type → type → nat → gmap string type → type → Prop :=
  (* Base lambda calculus *)
  | TP_CTX_Lam Δ Γ A B (x : string) :
     type_wf Δ A →
     typed_ctx_item (CTX_Lam x) Δ ((<[x:=A]>Γ)) B Δ Γ (TFun A B)
  | TP_CTX_LamAnon Δ Γ A B :
     type_wf Δ A →
     typed_ctx_item (CTX_Lam BAnon) Δ Γ B Δ Γ (TFun A B)
  | TP_CTX_AppL Δ Γ e2 A B :
     syn_typed Δ Γ e2 A →
     typed_ctx_item (CTX_AppL e2) Δ Γ (TFun A B) Δ Γ B
  | TP_CTX_AppR Δ Γ e1 A B :
     syn_typed Δ Γ e1 (TFun A B) →
     typed_ctx_item (CTX_AppR e1) Δ Γ A Δ Γ B
  (* Base types and operations *)
  | TP_CTX_UnOp op Δ Γ A B :
     un_op_typed op A B →
     typed_ctx_item (CTX_UnOp op) Δ Γ A Δ Γ B
  | TP_CTX_BinOpL op Δ Γ e2 A B C :
     syn_typed Δ Γ e2 B →
     bin_op_typed op A B C →
     typed_ctx_item (CTX_BinOpL op e2) Δ Γ A Δ Γ C
  | TP_CTX_BinOpR op e1 Δ Γ A B C :
     syn_typed Δ Γ e1 A →
     bin_op_typed op A B C →
     typed_ctx_item (CTX_BinOpR op e1) Δ Γ B Δ Γ C
  | TP_CTX_IfL Δ Γ e1 e2 A :
     syn_typed Δ Γ e1 A → syn_typed Δ Γ e2 A →
     typed_ctx_item (CTX_IfL e1 e2) Δ Γ (TBool) Δ Γ A
  | TP_CTX_IfM Δ Γ e0 e2 A :
     syn_typed Δ Γ e0 (TBool) → syn_typed Δ Γ e2 A →
     typed_ctx_item (CTX_IfM e0 e2) Δ Γ A Δ Γ A
  | TP_CTX_IfR Δ Γ e0 e1 A :
     syn_typed Δ Γ e0 (TBool) → syn_typed Δ Γ e1 A →
     typed_ctx_item (CTX_IfR e0 e1) Δ Γ A Δ Γ A
  (* Products *)
  | TP_CTX_PairL Δ Γ e2 A B :
     syn_typed Δ Γ e2 B →
     typed_ctx_item (CTX_PairL e2) Δ Γ A Δ Γ (TProd A B)
  | TP_CTX_PairR Δ Γ e1 A B :
     syn_typed Δ Γ e1 A →
     typed_ctx_item (CTX_PairR e1) Δ Γ B Δ Γ (TProd A B)
  | TP_CTX_Fst Δ Γ A B :
     typed_ctx_item CTX_Fst Δ Γ (TProd A B) Δ Γ A
  | TP_CTX_Snd Δ Γ A B :
     typed_ctx_item CTX_Snd Δ Γ (TProd A B) Δ Γ B
  (* Sums *)
  | TP_CTX_InjL Δ Γ A B :
     type_wf Δ B →
     typed_ctx_item CTX_InjL Δ Γ A Δ Γ (TSum A B)
  | TP_CTX_InjR Δ Γ A B :
     type_wf Δ A →
     typed_ctx_item CTX_InjR Δ Γ B Δ Γ (TSum A B)
  | TP_CTX_CaseL Δ Γ e1 e2 A B C :
     syn_typed Δ Γ e1 (TFun A C) → syn_typed Δ Γ e2 (TFun B C) →
     typed_ctx_item (CTX_CaseL e1 e2) Δ Γ (TSum A B) Δ Γ C
  | TP_CTX_CaseM Δ Γ e0 e2 A B C :
     syn_typed Δ Γ e0 (TSum A B) → syn_typed Δ Γ e2 (TFun B C) →
     typed_ctx_item (CTX_CaseM e0 e2) Δ Γ (TFun A C) Δ Γ C
  | TP_CTX_CaseR Δ Γ e0 e1 A B C :
     syn_typed Δ Γ e0 (TSum A B) → syn_typed Δ Γ e1 (TFun A C) →
     typed_ctx_item (CTX_CaseR e0 e1) Δ Γ (TFun B C) Δ Γ C
  (* Heap *)
  | TPCTX_Alloc Δ Γ A :
     typed_ctx_item CTX_Alloc Δ Γ A Δ Γ (TRef A)
  | TP_CTX_Load Δ Γ A :
     typed_ctx_item CTX_Load Δ Γ (TRef A) Δ Γ A
  | TP_CTX_StoreL Δ Γ e2 A :
     syn_typed Δ Γ e2 A → typed_ctx_item (CTX_StoreL e2) Δ Γ (TRef A) Δ Γ TUnit
  | TP_CTX_StoreR Δ Γ e1 A :
     syn_typed Δ Γ e1 (TRef A) →
     typed_ctx_item (CTX_StoreR e1) Δ Γ A Δ Γ TUnit
  (* Polymorphic & recursive types *)
  | TP_CTX_Roll Δ Γ A :
     typed_ctx_item CTX_Roll Δ Γ A.[(TMu A)/] Δ Γ (TMu A)
  | TP_CTX_Unroll Δ Γ A :
     typed_ctx_item CTX_Unroll Δ Γ (TMu A) Δ Γ A.[(TMu A)/]
  | TP_CTX_TLam Δ Γ A :
     typed_ctx_item CTX_TLam (S Δ) (⤉Γ) A Δ Γ (TForall A)
  | TP_CTX_TApp Δ Γ A B :
     type_wf Δ B →
     typed_ctx_item CTX_TApp Δ Γ (TForall A) Δ Γ A.[B/]
  | TP_CTX_Pack Δ Γ B C :
     type_wf Δ C →
     type_wf (S Δ) B →
     typed_ctx_item CTX_Pack Δ Γ B.[C/] Δ Γ (TExists B)
  | TP_CTX_UnpackL (x : string) e2 Δ Γ A B :
      type_wf Δ B →
      syn_typed (S Δ) (<[x:=A]>(⤉ Γ)) e2 (B.[ren (+1)]) →
     typed_ctx_item (CTX_UnpackL x e2) Δ Γ (TExists A) Δ Γ B
  | TP_CTX_UnpackR (x : string) e1 Δ Γ A B :
      type_wf Δ B →
      syn_typed Δ Γ e1 (TExists A) →
     typed_ctx_item (CTX_UnpackR x e1) (S Δ) (<[x:=A]>(⤉ Γ)) (B.[ren (+1)]) Δ Γ B
.

Inductive typed_ctx: ctx → nat → gmap string type → type → nat → gmap string type → type → Prop :=
  | TPCTX_nil Δ Γ A :
     typed_ctx nil Δ Γ A Δ Γ A
  | TPCTX_cons Δ1 Γ1 A Δ2 Γ2 B Δ3 Γ3 C k K :
     typed_ctx_item k Δ2 Γ2 B Δ3 Γ3 C →
     typed_ctx K Δ1 Γ1 A Δ2 Γ2 B →
     typed_ctx (k :: K) Δ1 Γ1 A Δ3 Γ3 C.

(** If the target terminates with a value, then also the source should terminate with some value *)
Definition ctx_refines Δ (Γ : gmap string type) (e e' : expr) (A : type) : Prop := ∀ K σ0 σ1 v1 B,
  (* no prophecies *)
  σ0 = mkstate σ0.(heap) →
  typed_ctx K Δ Γ A 0 ∅ B →
  rtc thread_step (fill_ctx K e, σ0) (of_val v1, σ1) →
  ∃ v2 σ1', rtc thread_step (fill_ctx K e', σ0) (of_val v2, σ1').

Notation "'CTX' Δ ; Γ ⊨ e ':≤:' e' : A" :=
  (ctx_refines Δ Γ e e' A) (at level 100, e, e' at next level, A at level 200).

Lemma typed_ctx_item_typed K Δ Γ A Δ' Γ' B e :
  syn_typed Δ Γ e A → typed_ctx_item K Δ Γ A Δ' Γ' B →
  syn_typed Δ' Γ' (fill_ctx_item K e) B.
Proof.
  induction 2; simpl; eauto using syn_typed.
Qed.

Lemma typed_ctx_typed K Δ Γ A Δ' Γ' B e :
  syn_typed Δ Γ e A → typed_ctx K Δ Γ A Δ' Γ' B → syn_typed Δ' Γ' (fill_ctx K e) B.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

Instance ctx_refines_reflexive Δ Γ A :
  Reflexive (fun e1 e2 => ctx_refines Δ Γ e1 e2 A).
Proof.
  intros e K ????? Hty Hst.
  eexists _,_. apply Hst.
Qed.

Instance ctx_refines_transitive Δ Γ A :
  Transitive (fun e1 e2 => ctx_refines Δ Γ e1 e2 A).
Proof.
  intros e1 e2 e3 Hctx1 Hctx2 K σ0 σ1 v1 B Hh Hty Hst.
  destruct (Hctx1 K σ0 σ1 v1 B Hh Hty Hst) as [v2' [σ1' Hst']].
  by apply (Hctx2 K σ0 σ1' v2' B).
Qed.

Lemma fill_ctx_app (K K' : ctx) (e : expr) :
  fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e.
Proof. by rewrite /fill_ctx foldr_app. Qed.

Lemma typed_ctx_compose (K K' : ctx) (Δ1 Δ2 Δ3 : nat) (Γ1 Γ2 Γ3 : gmap string type) (A B C : type) :
  typed_ctx K Δ1 Γ1 A Δ2 Γ2 B →
  typed_ctx K' Δ2 Γ2 B Δ3 Γ3 C →
  typed_ctx (K' ++ K) Δ1 Γ1 A Δ3 Γ3 C.
Proof.
  revert Δ1 Δ2 Δ3 Γ1 Γ2 Γ3 A B C.
  induction K' as [|k K'] => Δ1 Δ2 Δ3 Γ1 Γ2 Γ3 A B C.
  - by inversion 2; simplify_eq/=.
  - intros HK.
    inversion 1 as [|? ? ? ? ? ? ? ? ??? Hx1 Hx2]; simplify_eq/=.
    specialize (IHK' _ _ _ _ _ _ _ _ _ HK Hx2).
    econstructor; eauto.
Qed.

Lemma ctx_refines_congruence Δ Γ e1 e2 A Δ' Γ' B K :
  typed_ctx K Δ Γ A Δ' Γ' B →
  (CTX Δ; Γ ⊨ e1 :≤: e2 : A) →
  CTX Δ'; Γ' ⊨ fill_ctx K e1 :≤: fill_ctx K e2 : B.
Proof.
  intros HK Hctx K' thp σ₀ σ₁ v Hty.
  rewrite !fill_ctx_app => Hst.
  apply (Hctx (K' ++ K) thp σ₀ σ₁ v); auto.
  eapply typed_ctx_compose; eauto.
Qed.

Section log_related_under_typed_ctx.
  Context `{!relocGS Σ}.

  Local Hint Resolve compat_var compat_lambda compat_lambda_anon compat_tlam compat_int compat_bool compat_unit compat_if compat_beta compat_tapp compat_pack compat_unpack compat_binop compat_unop compat_pair compat_fst compat_snd compat_injl compat_injr compat_case compat_roll compat_unroll compat_new compat_store compat_load: core.

  (* Precongruence *)
  Lemma log_related_under_typed_ctx Δ Γ e e' A Δ' Γ' B K :
    typed_ctx K Δ Γ A Δ' Γ' B →
    TY Δ; Γ ⊨ e :≤: e' : A →
    TY Δ'; Γ' ⊨ fill_ctx K e :≤: fill_ctx K e' : B.
  Proof.
    revert Δ Γ A Δ' Γ' B e e'.
    induction K as [|k K]=> Δ Γ A Δ' Γ' B e e'; simpl.
    - inversion_clear 1; trivial.
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? ? ? ? Hx1 Hx2].
      specialize (IHK _ _ _ _ _ _ e e' Hx2).
      inversion Hx1; subst; simpl; intros He; eauto using fundamental.
  Qed.
End log_related_under_typed_ctx.

(** Observal types for which the language (i.e., surrounding contexts) can observe equality *)
Inductive ObsType : type → Prop :=
  | obs_int : ObsType Int
  | obs_bool : ObsType Bool
  | obs_unit : ObsType Unit
  | obs_prod A1 A2 : ObsType A1 → ObsType A2 → ObsType (TProd A1 A2)
  | obs_sum A1 A2 : ObsType A1 → ObsType A2 → ObsType (TSum A1 A2)
.

Lemma ObsType_soundness `{relocGS Σ} A δ v v' :
  ObsType A → type_interp A δ v v' -∗ ⌜v = v'⌝.
Proof.
  induction 1 as [ | | | ??? IH1 ? IH2 | ??? IH1 ? IH2] in v, v' |-*; simpl.
  - iIntros "(% & -> & ->)". done.
  - iIntros "(% & -> & ->)". done.
  - iIntros "( -> & ->)". done.
  - iIntros "(% & % & % & % & -> & -> & H1 & H2)".
    iPoseProof (IH1 with "H1") as "->".
    iPoseProof (IH2 with "H2") as "->".
    done.
  - iIntros "[(% & % & -> & -> & H1) | (% & % & -> & -> & H2)]".
    + iPoseProof (IH1 with "H1") as "->"; done.
    + iPoseProof (IH2 with "H2") as "->"; done.
Qed.

Definition trivial_env {Σ} `{heapGS Σ} : envO :=
  λne n, (mk_semtype (λ v v', False)%I : semtypeO (Σ := Σ)).

Lemma logrel_adequate Σ `{reloc_preGS Σ} e e' Δ A (σ : state) :
  σ = mkstate σ.(heap) →
  (∀ `{relocGS Σ}, TY Δ; ∅ ⊨ e :≤: e' : A) →
  adequate NotStuck e σ (λ v _, ∃ v' h, rtc thread_step (e', σ) (of_val v', h) ∧ (ObsType A → v = v')).
Proof.
  intros ? Hlog.
  set (τ := λ (_ : relocGS Σ), type_interp A trivial_env).
  eapply (refines_adequate Σ τ); first done; last first.
  - intros HΣ. iPoseProof (Hlog HΣ $! trivial_env ∅) as "Ha".
    rewrite !fmap_empty !subst_map_empty.
    iApply "Ha". iApply context_interp_empty.
  - intros HΣ v v'. iIntros "Ha" (Hobs).
    by iApply ObsType_soundness.
Qed.

Theorem logrel_typesafety Σ `{reloc_preGS Σ} e e' e1 Δ A σ σ' :
  σ = mkstate σ.(heap) →
  (∀ `{relocGS Σ}, TY Δ; ∅ ⊨ e :≤: e' : A) →
  rtc thread_step (e, σ) (e1 , σ') →
  not_stuck e1 σ'.
Proof.
  intros Hlog ??%rtc_thread_erased_step.
  cut (adequate NotStuck e σ (λ v _, ∃ v' h, rtc thread_step (e', σ) (of_val v', h) ∧ (ObsType A → v = v'))).
  { intros [_ Ha]; eapply Ha; [done.. | ]. apply elem_of_list_singleton; done. }
  eapply logrel_adequate; eauto.
Qed.

Theorem F_mu_ref_typesafety e e' σ σ' Δ A :
  σ = mkstate σ.(heap) →
  syn_typed Δ ∅ e A →
  rtc thread_step (e, σ) (e', σ') →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros.
  eapply (logrel_typesafety relocΣ); eauto.
  intros. by apply fundamental.
Qed.

Lemma logrel_simul Σ `{reloc_preGS Σ} e e' Δ A v h σ :
  σ = mkstate σ.(heap) →
  (∀ `{relocGS Σ}, TY Δ; ∅ ⊨ e :≤: e' : A) →
  rtc thread_step (e, σ) (of_val v, h) →
  (∃ v' h', rtc thread_step (e', σ) (of_val v', h') ∧ (ObsType A → v = v')).
Proof.
  intros ? Hlog Hsteps%rtc_thread_erased_step.
  cut (adequate NotStuck e σ (λ v _, ∃ v' h, rtc thread_step (e', σ) (of_val v', h) ∧ (ObsType A → v = v'))).
  { destruct 1 as [H1 _]. naive_solver. }
  eapply logrel_adequate; eauto.
Qed.

(** Contextual refinement for open terms *)
Lemma refines_sound_open Σ `{reloc_preGS Σ} Δ Γ e e' A :
  (∀ `{relocGS Σ}, TY Δ; Γ ⊨ e :≤: e' : A) →
  CTX Δ; Γ ⊨ e :≤: e' : A.
Proof.
  intros Hlog K σ0 σ1 v1 B Hh Htyped Hstep.
  cut (  (∃ v' h', rtc thread_step (fill_ctx K e', σ0) (of_val v', h') ∧ (ObsType B → v1 = v'))).
  { naive_solver. }
  eapply (logrel_simul Σ _ _ Δ); first done; last by apply Hstep.
  iIntros (?).
  iApply (log_related_under_typed_ctx); eauto.
Qed.

(** The main contextual refinement lemma *)
Lemma refines_sound Σ `{reloc_preGS Σ} (e e' : expr) Δ A :
  (∀ `{relocGS Σ} δ, ⊢ refines e e' (type_interp A δ)) →
  CTX Δ; ∅ ⊨ e :≤: e' : A.
Proof.
  intros Hlog. eapply refines_sound_open; first apply _.
  iIntros (? ? ?) "Hctx".
  iPoseProof (context_interp_dom_eq with "Hctx") as "%Hdom".
  rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_iff_L in Hdom.
  subst γ. rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
