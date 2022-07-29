From iris.prelude Require Import prelude.
From stdpp Require Export binders strings.
From semantics.ts.systemf_mu_state Require Export locations.
From semantics.lib Require Export maps.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** Expressions and vals. *)
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp (* Arithmetic *)
  | LtOp | LeOp | EqOp. (* Comparison *)


Inductive expr :=
  | Lit (l : base_lit)
  (* Base lambda calculus *)
  | Var (x : string)
  | Lam (x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Polymorphism *)
  | TApp (e : expr)
  | TLam (e : expr)
  | Pack (e : expr)
  | Unpack (x : binder) (e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Isorecursive types *)
  | Roll (e : expr)
  | Unroll (e : expr)
  (* State *)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | New (e : expr)
.

Bind Scope expr_scope with expr.

Inductive val :=
  | LitV (l : base_lit)
  | LamV (x : binder) (e : expr)
  | TLamV (e : expr)
  | PackV (v : val)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | RollV (v : val)
.

Bind Scope val_scope with val.

Fixpoint of_val (v : val) : expr :=
  match v with
  | LitV l => Lit l
  | LamV x e => Lam x e
  | TLamV e => TLam e
  | PackV v => Pack (of_val v)
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  | RollV v => Roll (of_val v)
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lit l => Some $ LitV l
  | Lam x e => Some (LamV x e)
  | TLam e => Some (TLamV e)
  | Pack e =>
     to_val e ≫= (λ v, Some $ PackV v)
  | Pair e1 e2 =>
    to_val e1 ≫= (λ v1, to_val e2 ≫= (λ v2, Some $ PairV v1 v2))
  | InjL e => to_val e ≫= (λ v, Some $ InjLV v)
  | InjR e => to_val e ≫= (λ v, Some $ InjRV v)
  | Roll e => to_val e ≫= (λ v, Some $ RollV v)
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

#[export] Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite <-!to_of_val, Hv. Qed.

(** structural computational version *)
Fixpoint is_val (e : expr) : Prop :=
  match e with
  | Lit l => True
  | Lam x e => True
  | TLam e => True
  | Pack e => is_val e
  | Pair e1 e2 => is_val e1 ∧ is_val e2
  | InjL e => is_val e
  | InjR e => is_val e
  | Roll e => is_val e
  | _ => False
  end.
Lemma is_val_spec e : is_val e ↔ ∃ v, to_val e = Some v.
Proof.
  induction e; simpl; (split; [ | intros (v & Heq)]); simplify_option_eq; try done; eauto.
  - rewrite IHe. intros (v & ->); eauto.
  - apply IHe. eauto.
  - rewrite IHe1 IHe2. intros [(v1 & ->) (v2 & ->)]. eauto.
  - rewrite IHe1 IHe2. eauto.
  - rewrite IHe. intros (v & ->). eauto.
  - apply IHe. eauto.
  - rewrite IHe. intros (v & ->); eauto.
  - apply IHe. eauto.
  - rewrite IHe. intros (v & ->). eauto.
  - apply IHe. eauto.
Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.


(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Lit _ => e
  | Var y => if decide (x = y) then es else Var y
  | Lam y e =>
      Lam y $ if decide (BNamed x = y) then e else subst x es e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | TApp e => TApp (subst x es e)
  | TLam e => TLam (subst x es e)
  | Pack e => Pack (subst x es e)
  | Unpack y e1 e2 => Unpack y (subst x es e1) (if decide (BNamed x = y) then e2 else subst x es e2)
  | UnOp op e => UnOp op (subst x es e)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | If e0 e1 e2 => If (subst x es e0) (subst x es e1) (subst x es e2)
  | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
  | Fst e => Fst (subst x es e)
  | Snd e => Snd (subst x es e)
  | InjL e => InjL (subst x es e)
  | InjR e => InjR (subst x es e)
  | Case e0 e1 e2 => Case (subst x es e0) (subst x es e1) (subst x es e2)
  | Roll e => Roll (subst x es e)
  | Unroll e => Unroll (subst x es e)
  | Load e => Load (subst x es e)
  | Store e1 e2 => Store (subst x es e1) (subst x es e2)
  | New e => New (subst x es e)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  end%Z.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match v1, v2 with
  | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
  | _, _ => None
  end.

Definition heap := gmap loc val.
Fixpoint heap_array (l : loc) (vs : list val) : heap :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs w k :
  heap_array l vs !! k = Some w ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; eauto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0. eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : heap) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

Definition init_heap (l : loc) (n : Z) (v : val) (σ : heap) : heap :=
  heap_array l (replicate (Z.to_nat n) v) ∪ σ.

Lemma init_heap_singleton l v σ :
  init_heap l 1 v σ = <[l:=v]> σ.
Proof.
  rewrite /init_heap /=.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Inductive base_step : expr * heap → expr * heap → Prop :=
  | BetaS x e1 e2 e' σ :
     is_val e2 →
     e' = subst' x e2 e1 →
     base_step (App (Lam x e1) e2, σ) (e', σ)
  | TBetaS e1 σ :
      base_step (TApp (TLam e1), σ) (e1, σ)
  | UnpackS e1 e2 e' x σ :
      is_val e1 →
      e' = subst' x e1 e2 →
      base_step (Unpack x (Pack e1) e2, σ) (e', σ)
  | UnOpS op e v v' σ :
     to_val e = Some v →
     un_op_eval op v = Some v' →
     base_step (UnOp op e, σ) (of_val v', σ)
  | BinOpS op e1 v1 e2 v2 v' σ :
     to_val e1 = Some v1 →
     to_val e2 = Some v2 →
     bin_op_eval op v1 v2 = Some v' →
     base_step (BinOp op e1 e2, σ) (of_val v', σ)
  | IfTrueS e1 e2 σ :
     base_step (If (Lit $ LitBool true) e1 e2, σ) (e1, σ)
  | IfFalseS e1 e2 σ :
     base_step (If (Lit $ LitBool false) e1 e2, σ) (e2, σ)
  | FstS e1 e2 σ :
     is_val e1 →
     is_val e2 →
     base_step (Fst (Pair e1 e2), σ) (e1, σ)
  | SndS e1 e2 σ :
     is_val e1 →
     is_val e2 →
     base_step (Snd (Pair e1 e2), σ) (e2, σ)
  | CaseLS e e1 e2 σ :
     is_val e →
     base_step (Case (InjL e) e1 e2, σ) (App e1 e, σ)
  | CaseRS e e1 e2 σ :
     is_val e →
     base_step (Case (InjR e) e1 e2, σ) (App e2 e, σ)
  | UnrollS e σ :
      is_val e →
      base_step (Unroll (Roll e), σ) (e, σ)
  | NewS e v σ l :
     σ !! l = None →
     to_val e = Some v →
     base_step (New e, σ) (Lit $ LitLoc l, init_heap l 1 v σ)
  | LoadS l v σ :
     σ !! l = Some v →
     base_step (Load (Lit $ LitLoc l), σ) (of_val v, σ)
  | StoreS l v w e2 σ :
     σ !! l = Some v →
     to_val e2 = Some w →
     base_step (Store (Lit $ LitLoc l) e2, σ)
               (Lit LitUnit, <[l:=w]> σ)
.

(* Misc *)
Lemma is_val_of_val v : is_val (of_val v).
Proof. apply is_val_spec. rewrite to_of_val. eauto. Qed.

(** If [e1] makes a base step to a value under some state [σ1] then any base
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma base_step_to_val e1 e2 e2' σ1 σ2 σ2' :
  base_step (e1, σ1) (e2, σ2) →
  base_step (e1, σ1) (e2', σ2') → is_Some (to_val e2) → is_Some (to_val e2').
Proof. inversion 1; inversion 1; naive_solver. Qed.

Lemma new_fresh v σ :
  let l := fresh_locs (dom σ) in
  base_step (New (of_val v), σ) (Lit $ LitLoc l, init_heap l 1 v σ).
Proof.
  intros.
  apply NewS.
  - apply (not_elem_of_dom).
    rewrite -(loc_add_0 l).
    by apply fresh_locs_fresh.
  - rewrite to_of_val. eauto.
Qed.

(** We define evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | TAppCtx
  | PackCtx
  | UnpackCtx (x : binder) (e2 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | UnrollCtx
  | RollCtx
  | LoadCtx
  | StoreRCtx (e1 : expr)
  | StoreLCtx (v2 : val)
  | NewCtx
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | TAppCtx => TApp e
  | PackCtx => Pack e
  | UnpackCtx x e2 => Unpack x e e2
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (of_val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (of_val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | UnrollCtx => Unroll e
  | RollCtx => Roll e
  | LoadCtx => Load e
  | StoreRCtx e1 => Store e1 e
  | StoreLCtx v2 => Store e (of_val v2)
  | NewCtx => New e
  end.

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.
Lemma fill_item_no_val Ki e :
  to_val e = None → to_val (fill_item Ki e) = None.
Proof.
  intros Hn. destruct (to_val (fill_item _ _ )) eqn:Heq; last done.
  edestruct (fill_item_val Ki e) as (? & ?); last simplify_eq.
  eauto.
Qed.

Lemma val_base_stuck e1 e2 σ1 σ2 : base_step (e1, σ1) (e2, σ2) → to_val e1 = None.
Proof. inversion 1; naive_solver. Qed.

Lemma of_val_lit v l :
  of_val v = (Lit l) → v = LitV l.
Proof. destruct v; simpl; inversion 1; done. Qed.
Lemma of_val_pair_inv (v v1 v2 : val) :
  of_val v = Pair (of_val v1) (of_val v2) → v = PairV v1 v2.
Proof.
  destruct v; simpl; inversion 1.
  apply of_val_inj in H1. apply of_val_inj in H2. subst; done.
Qed.
Lemma of_val_injl_inv (v v' : val) :
  of_val v = InjL (of_val v') → v = InjLV v'.
Proof.
  destruct v; simpl; inversion 1.
  apply of_val_inj in H1. subst; done.
Qed.
Lemma of_val_injr_inv (v v' : val) :
  of_val v = InjR (of_val v') → v = InjRV v'.
Proof.
  destruct v; simpl; inversion 1.
  apply of_val_inj in H1. subst; done.
Qed.

Ltac simplify_val :=
  repeat match goal with
  | H: to_val (of_val ?v) = ?o |- _ => rewrite to_of_val in H
  | H: is_val ?e |- _ => destruct (proj1 (is_val_spec e) H) as (? & ?); clear H
  | H: to_val ?e = ?v |- _ => is_var e; specialize (of_to_val _ _ H); intros <-; clear H
  | H: of_val ?v = Lit ?l |- _ => is_var v; specialize (of_val_lit _ _ H); intros ->; clear H
  | |- context[to_val (of_val ?e)] => rewrite to_of_val
  end.
Lemma base_ectxi_step_val Ki e e2 σ1 σ2 :
  base_step (fill_item Ki e, σ1) (e2, σ2) → is_Some (to_val e).
Proof.
  revert e2. induction Ki; inversion_clear 1; simplify_option_eq; simplify_val; eauto.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; try naive_solver eauto with f_equal.
  all: intros ?? Heq; injection Heq; intros ??; simplify_eq; simplify_val; naive_solver.
Qed.

Section contexts.
  Notation ectx := (list ectx_item).
  Definition empty_ectx : ectx := [].
  Definition comp_ectx : ectx → ectx → ectx := flip (++).

  Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.
  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. done. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. unfold fill, comp_ectx; simpl. by rewrite foldl_app. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. induction K as [|Ki K IH]; unfold Inj; naive_solver. Qed.

  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof.
    induction K as [|Ki K IH] in e |-*; [ done |]. by intros ?%IH%fill_item_val.
  Qed.
  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

End contexts.

(** Contextual steps *)
Inductive contextual_step : expr * heap → expr * heap → Prop :=
  Ectx_step K e1 e2 σ1 σ2 e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    base_step (e1', σ1) (e2', σ2) → contextual_step (e1, σ1) (e2, σ2).


Lemma base_contextual_step e1 e2 σ1 σ2 :
  base_step (e1, σ1) (e2, σ2) → contextual_step (e1, σ1) (e2, σ2).
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma fill_contextual_step K e1 e2 σ1 σ2 :
  contextual_step (e1, σ1) (e2, σ2) → contextual_step (fill K e1, σ1) (fill K e2, σ2).
Proof.
  inversion 1; subst.
  rewrite !fill_comp. by econstructor.
Qed.

(** *** closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lam x e => is_closed (x :b: X) e
  | Unpack x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | TApp e | TLam e | Pack e | Roll e | Unroll e | Load e | New e=> is_closed X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 => is_closed X e1 && is_closed X e2
  |  If e0 e1 e2 | Case e0 e1 e2 =>
   is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

(** [closed] states closedness as a Coq proposition, through the [Is_true] transformer. *)
Definition closed (X : list string) (e : expr) : Prop := Is_true (is_closed X e).
#[export] Instance closed_proof_irrel X e : ProofIrrel (closed X e).
Proof. unfold closed. apply _. Qed.
#[export] Instance closed_dec X e : Decision (closed X e).
Proof. unfold closed. apply _. Defined.

(** closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?.
  induction e in X |-*; simpl; intros ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_do_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

Lemma closed_is_closed X e :
  is_closed X e = true ↔ closed X e.
Proof.
  unfold closed. split.
  - apply Is_true_eq_left.
  - apply Is_true_eq_true.
Qed.

(** Substitution lemmas *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  induction e in X |-*; simpl; rewrite ?bool_decide_spec ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.
Lemma subst'_is_closed_nil e x es : is_closed [] e → subst' x es e = e.
Proof. intros. destruct x as [ | x]. { done. } by apply subst_is_closed_nil. Qed.

(** ** More on the contextual semantics *)

Definition base_reducible (e : expr) σ :=
  ∃ e' σ', base_step (e, σ) (e', σ').
Definition base_irreducible (e : expr) σ :=
  ∀ e' σ', ¬base_step (e, σ) (e', σ').
Definition base_stuck (e : expr) σ :=
  to_val e = None ∧ base_irreducible e σ.

(** Given a base redex [e1_redex] somewhere in a term, and another
    decomposition of the same term into [fill K' e1'] such that [e1'] is not
    a value, then the base redex context is [e1']'s context [K'] filled with
    another context [K''].  In particular, this implies [e1 = fill K''
    e1_redex] by [fill_inj], i.e., [e1]' contains the base redex.)
 *)
Lemma step_by_val K' K_redex e1' e1_redex e2 σ1 σ2 :
    fill K' e1' = fill K_redex e1_redex →
    to_val e1' = None →
    base_step (e1_redex, σ1) (e2, σ2) →
    ∃ K'', K_redex = comp_ectx K' K''.
Proof.
  rename K' into K. rename K_redex into K'.
  rename e1' into e1. rename e1_redex into e1'.
  intros Hfill Hred Hstep; revert K' Hfill.
  induction K as [|Ki K IH] using rev_ind; simpl; intros K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hstep. apply base_ectxi_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !fill_app in Hfill; simpl in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill.
    - by apply fill_not_val.
    - apply fill_not_val. eauto using val_base_stuck.
  }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. unfold comp_ectx; simpl. rewrite assoc; done.
Qed.

(** If [fill K e] takes a base step, then either [e] is a value or [K] is
    the empty evaluation context. In other words, if [e] is not a value
    wrapping it in a context does not add new base redex positions. *)
Lemma base_ectx_step_val K e e2 σ1 σ2 :
  base_step (fill K e, σ1) (e2, σ2) → is_Some (to_val e) ∨ K = empty_ectx.
Proof.
  destruct K as [|Ki K _] using rev_ind; simpl; [by auto|].
  rewrite fill_app; simpl.
  intros ?%base_ectxi_step_val; eauto using fill_val.
Qed.

(** If a [contextual_step] preserving a surrounding context [K] happens,
   the reduction happens entirely below the context. *)
Lemma contextual_step_ectx_inv K e e' σ1 σ2 :
  to_val e = None →
  contextual_step (fill K e, σ1) (fill K e', σ2) →
  contextual_step (e, σ1) (e', σ2).
Proof.
  intros ? Hcontextual.
  inversion Hcontextual as [??????? Heq1 Heq2 ?]; subst.
  eapply step_by_val in H as (K'' & Heq); [ | done | done].
  subst K0.
  rewrite <-fill_comp in Heq1. rewrite <-fill_comp in Heq2.
  apply fill_inj in Heq1. apply fill_inj in Heq2. subst.
  econstructor; done.
Qed.

Lemma contextual_ectx_step_case K e e' σ1 σ2 :
  contextual_step (fill K e, σ1) (e', σ2) →
  (∃ e'', e' = fill K e'' ∧ contextual_step (e, σ1) (e'', σ2)) ∨ is_val e.
Proof.
  destruct (to_val e) as [ v | ] eqn:Hv.
  { intros _. right. apply is_val_spec. eauto. }
  intros Hcontextual. left.
  inversion Hcontextual as [K' ? ? ? ? e1' e2' Heq1 Heq2 Hstep]; subst.
  eapply step_by_val in Heq1 as (K'' & ->); [ | done | done].
  rewrite <-fill_comp.
  eexists _. split; [done | ].
  rewrite <-fill_comp in Hcontextual.
  apply contextual_step_ectx_inv in Hcontextual; done.
Qed.

Lemma base_reducible_contextual_step_ectx K e1 e2 σ1 σ2 :
  base_reducible e1 σ1 →
  contextual_step (fill K e1, σ1) (e2, σ2) →
  ∃ e2', e2 = fill K e2' ∧ base_step (e1, σ1) (e2', σ2).
Proof.
  intros (e2''&σ2'' & HhstepK) Hctx.
  inversion Hctx as [K' ???? e1' e2' HKe1 -> Hstep].
  edestruct (step_by_val K) as [K'' ?];
    eauto using val_base_stuck; simplify_eq/=.
  rewrite <-fill_comp in HKe1; simplify_eq.
  exists (fill K'' e2'). rewrite fill_comp; split; [done | ].
  apply base_ectx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
  { apply val_base_stuck in Hstep; simplify_eq. }
  by rewrite !fill_empty.
Qed.

Lemma base_reducible_contextual_step e1 e2 σ1 σ2 :
  base_reducible e1 σ1 →
  contextual_step (e1, σ1) (e2, σ2) →
  base_step (e1, σ1) (e2, σ2).
Proof.
  intros.
  edestruct (base_reducible_contextual_step_ectx empty_ectx) as (?&?&?);
    rewrite ?fill_empty; eauto.
  by simplify_eq; rewrite fill_empty.
Qed.

(** *** Reducibility *)
Definition reducible (e : expr) σ :=
    ∃ e' σ', contextual_step (e, σ) (e', σ').
Definition irreducible (e : expr) σ :=
  ∀ e' σ', ¬contextual_step (e, σ) (e', σ').
Definition stuck (e : expr) σ :=
  to_val e = None ∧ irreducible e σ.
Definition not_stuck (e : expr) σ :=
  is_Some (to_val e) ∨ reducible e σ.

Lemma base_step_not_stuck e e' σ σ' : base_step (e, σ) (e', σ') → not_stuck e σ.
Proof. unfold not_stuck, reducible; simpl. eauto 10 using base_contextual_step. Qed.

Lemma val_stuck e e' σ σ' : contextual_step (e, σ) (e', σ') → to_val e = None.
Proof.
  inversion 1 as [??????? -> -> ?%val_base_stuck].
  apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
Qed.
Lemma not_reducible e σ : ¬reducible e σ ↔ irreducible e σ.
Proof. unfold reducible, irreducible. naive_solver. Qed.
Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
Proof. intros (?&?&?). eauto using val_stuck. Qed.
Lemma val_irreducible e σ : is_Some (to_val e) → irreducible e σ.
Proof. intros [??] ?? ?%val_stuck. by destruct (to_val e). Qed.

Lemma irreducible_fill K e σ :
  irreducible (fill K e) σ → irreducible e σ.
Proof.
  intros Hirred e' σ' Hstep.
  eapply Hirred. by apply fill_contextual_step.
Qed.

Lemma base_reducible_reducible e σ :
  base_reducible e σ → reducible e σ.
Proof. intros (e' & σ' & Hhead). exists e', σ'. by apply base_contextual_step. Qed.


(* we derive a few lemmas about contextual steps *)
Lemma contextual_step_app_l e1 e1' e2 σ1 σ2 :
  is_val e2 →
  contextual_step (e1, σ1) (e1', σ2) →
  contextual_step (App e1 e2, σ1) (App e1' e2, σ2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step [AppLCtx _]).
Qed.

Lemma contextual_step_app_r e1 e2 e2' σ1 σ2 :
  contextual_step (e2, σ1) (e2', σ2) →
  contextual_step (App e1 e2, σ1) (App e1 e2', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [AppRCtx e1]).
Qed.

Lemma contextual_step_tapp e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (TApp e, σ1) (TApp e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [TAppCtx]).
Qed.

Lemma contextual_step_pack e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Pack e, σ1) (Pack e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [PackCtx]).
Qed.

Lemma contextual_step_unpack x e e' e2 σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Unpack x e e2, σ1) (Unpack x e' e2, σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [UnpackCtx x e2]).
Qed.

Lemma contextual_step_unop op e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (UnOp op e, σ1) (UnOp op e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [UnOpCtx op]).
Qed.

Lemma contextual_step_binop_l op e1 e1' e2 σ1 σ2 :
  is_val e2 →
  contextual_step (e1, σ1) (e1', σ2) →
  contextual_step (BinOp op e1 e2, σ1) (BinOp op e1' e2, σ2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step [BinOpLCtx op v]).
Qed.

Lemma contextual_step_binop_r op e1 e2 e2' σ1 σ2 :
  contextual_step (e2, σ1) (e2', σ2) →
  contextual_step (BinOp op e1 e2, σ1) (BinOp op e1 e2', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [BinOpRCtx op e1]).
Qed.

Lemma contextual_step_if e e' e1 e2 σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (If e e1 e2, σ1) (If e' e1 e2, σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [IfCtx e1 e2]).
Qed.

Lemma contextual_step_pair_l e1 e1' e2 σ1 σ2 :
  is_val e2 →
  contextual_step (e1, σ1) (e1', σ2) →
  contextual_step (Pair e1 e2, σ1) (Pair e1' e2, σ2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step [PairLCtx v]).
Qed.

Lemma contextual_step_pair_r e1 e2 e2' σ1 σ2 :
  contextual_step (e2, σ1) (e2', σ2) →
  contextual_step (Pair e1 e2, σ1) (Pair e1 e2', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [PairRCtx e1]).
Qed.


Lemma contextual_step_fst e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Fst e, σ1) (Fst e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [FstCtx]).
Qed.

Lemma contextual_step_snd e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Snd e, σ1) (Snd e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [SndCtx]).
Qed.

Lemma contextual_step_injl e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (InjL e, σ1) (InjL e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [InjLCtx]).
Qed.

Lemma contextual_step_injr e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (InjR e, σ1) (InjR e', σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [InjRCtx]).
Qed.

Lemma contextual_step_case e e' e1 e2 σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Case e e1 e2, σ1) (Case e' e1 e2, σ2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step [CaseCtx e1 e2]).
Qed.

Lemma contextual_step_roll e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Roll e, σ1) (Roll e', σ2).
Proof. by apply (fill_contextual_step [RollCtx]). Qed.

Lemma contextual_step_unroll e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Unroll e, σ1) (Unroll e', σ2).
Proof. by apply (fill_contextual_step [UnrollCtx]). Qed.

Lemma contextual_step_new e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (New e, σ1) (New e', σ2).
Proof. by apply (fill_contextual_step [NewCtx]). Qed.

Lemma contextual_step_load e e' σ1 σ2 :
  contextual_step (e, σ1) (e', σ2) →
  contextual_step (Load e, σ1) (Load e', σ2).
Proof. by apply (fill_contextual_step [LoadCtx]). Qed.

Lemma contextual_step_store_r e1 e2 e2' σ1 σ2 :
  contextual_step (e2, σ1) (e2', σ2) →
  contextual_step (Store e1 e2, σ1) (Store e1 e2', σ2).
Proof. by apply (fill_contextual_step [StoreRCtx _]). Qed.

Lemma contextual_step_store_l e1 e1' e2 σ1 σ2 :
  is_val e2 →
  contextual_step (e1, σ1) (e1', σ2) →
  contextual_step (Store e1 e2, σ1) (Store e1' e2, σ2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step [StoreLCtx _]).
Qed.


#[export]
Hint Resolve
  contextual_step_app_l contextual_step_app_r contextual_step_binop_l contextual_step_binop_r
  contextual_step_case contextual_step_fst contextual_step_if contextual_step_injl contextual_step_injr
  contextual_step_pack contextual_step_pair_l contextual_step_pair_r contextual_step_snd contextual_step_tapp
  contextual_step_tapp contextual_step_unop contextual_step_unpack contextual_step_roll contextual_step_unroll
  contextual_step_new contextual_step_load contextual_step_store_r contextual_step_store_l : core.
