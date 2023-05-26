From stdpp Require Export binders strings.
From iris.prelude Require Import options.
From semantics.lib Require Export maps.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(** Expressions and vals. *)
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit.
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
  | Case (e0 : expr) (e1 : expr) (e2 : expr).

Bind Scope expr_scope with expr.

Inductive val :=
  | LitV (l : base_lit)
  | LamV (x : binder) (e : expr)
  | TLamV (e : expr)
  | PackV (v : val)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
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
  | _ => False
  end.
Lemma is_val_spec e : is_val e ↔ ∃ v, to_val e = Some v.
Proof.
  induction e as [ | | ? e IH | e1 IH1 e2 IH2 | e IH | ? e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 | e IH | e IH | e IH | ? e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH | e IH | e IH | e IH | e1 IH1 e2 IH2 e3 IH3 ];
    simpl; (split; [ | intros (v & Heq)]); simplify_option_eq; try done; eauto.
  - rewrite IH. intros (v & ->). eauto.
  - apply IH. eauto.
  - rewrite IH1, IH2. intros [(v1 & ->) (v2 & ->)]. eauto.
  - rewrite IH1, IH2. eauto.
  - rewrite IH. intros (v & ->). eauto.
  - apply IH. eauto.
  - rewrite IH. intros (v & ->); eauto.
  - apply IH. eauto.
Qed.

Ltac simplify_val :=
  repeat match goal with
  | H: to_val (of_val ?v) = ?o |- _ => rewrite to_of_val in H
  | H: is_val ?e |- _ => destruct (proj1 (is_val_spec e) H) as (? & ?); clear H
  end.

(* Misc *)
Lemma is_val_of_val v : is_val (of_val v).
Proof. apply is_val_spec. rewrite to_of_val. eauto. Qed.

(* literals and our operators have decidable equality. *)
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

Inductive base_step : expr → expr → Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 →
     e' = subst' x e2 e1 →
     base_step (App (Lam x e1) e2) e'
  | TBetaS e1 :
      base_step (TApp (TLam e1)) e1
  | UnpackS e1 e2 e' x :
      is_val e1 →
      e' = subst' x e1 e2 →
      base_step (Unpack x (Pack e1) e2) e'
  | UnOpS op e v v' :
     to_val e = Some v →
     un_op_eval op v = Some v' →
     base_step (UnOp op e) (of_val v')
  | BinOpS op e1 v1 e2 v2 v' :
     to_val e1 = Some v1 →
     to_val e2 = Some v2 →
     bin_op_eval op v1 v2 = Some v' →
     base_step (BinOp op e1 e2) (of_val v')
  | IfTrueS e1 e2 :
     base_step (If (Lit $ LitBool true) e1 e2) e1
  | IfFalseS e1 e2 :
     base_step (If (Lit $ LitBool false) e1 e2) e2
  | FstS e1 e2 :
     is_val e1 →
     is_val e2 →
     base_step (Fst (Pair e1 e2)) e1
  | SndS e1 e2 :
     is_val e1 →
     is_val e2 →
     base_step (Snd (Pair e1 e2)) e2
  | CaseLS e e1 e2 :
     is_val e →
     base_step (Case (InjL e) e1 e2) (App e1 e)
  | CaseRS e e1 e2 :
     is_val e →
     base_step (Case (InjR e) e1 e2) (App e2 e)
.

(** We define evaluation contexts *)
Inductive ectx :=
  | HoleCtx
  | AppLCtx (K: ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K: ectx)
  | TAppCtx (K: ectx)
  | PackCtx (K: ectx)
  | UnpackCtx (x : binder)(K: ectx)  (e2 : expr)
  | UnOpCtx (op : un_op) (K: ectx)
  | BinOpLCtx (op : bin_op) (K: ectx) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr) (K: ectx)
  | IfCtx (K: ectx) (e1 e2 : expr)
  | PairLCtx (K: ectx) (v2 : val)
  | PairRCtx (e1 : expr) (K: ectx)
  | FstCtx (K: ectx)
  | SndCtx (K: ectx)
  | InjLCtx (K: ectx)
  | InjRCtx (K: ectx)
  | CaseCtx (K: ectx) (e1 : expr) (e2 : expr) .

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | TAppCtx K => TApp (fill K e)
  | PackCtx K => Pack (fill K e)
  | UnpackCtx x K e2 => Unpack x (fill K e) e2
  | UnOpCtx op K => UnOp op (fill K e)
  | BinOpLCtx op K v2 => BinOp op (fill K e) (of_val v2)
  | BinOpRCtx op e1 K => BinOp op e1 (fill K e)
  | IfCtx K e1 e2 => If (fill K e) e1 e2
  | PairLCtx K v2 => Pair (fill K e) (of_val v2)
  | PairRCtx e1 K => Pair e1 (fill K e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  | InjLCtx K => InjL (fill K e)
  | InjRCtx K => InjR (fill K e)
  | CaseCtx K e1 e2 => Case (fill K e) e1 e2
  end.

Fixpoint comp_ectx (K: ectx) (K' : ectx) : ectx :=
  match K with
  | HoleCtx => K'
  | AppLCtx K v2 => AppLCtx (comp_ectx K K') v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K K')
  | TAppCtx K => TAppCtx (comp_ectx K K')
  | PackCtx K => PackCtx (comp_ectx K K')
  | UnpackCtx x K e2 => UnpackCtx x (comp_ectx K K') e2
  | UnOpCtx op K => UnOpCtx op (comp_ectx K K')
  | BinOpLCtx op K v2 => BinOpLCtx op (comp_ectx K K') v2
  | BinOpRCtx op e1 K => BinOpRCtx op e1 (comp_ectx K K')
  | IfCtx K e1 e2 => IfCtx (comp_ectx K K') e1 e2
  | PairLCtx K v2 => PairLCtx (comp_ectx K K') v2
  | PairRCtx e1 K => PairRCtx e1 (comp_ectx K K')
  | FstCtx K => FstCtx (comp_ectx K K')
  | SndCtx K => SndCtx (comp_ectx K K')
  | InjLCtx K => InjLCtx (comp_ectx K K')
  | InjRCtx K => InjRCtx (comp_ectx K K')
  | CaseCtx K e1 e2 => CaseCtx (comp_ectx K K') e1 e2
  end.

(** Contextual steps *)
Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    base_step e1' e2' → contextual_step e1 e2.

Definition reducible (e : expr) :=
  ∃ e', contextual_step e e'.


Definition empty_ectx := HoleCtx.

(** Basic properties about the language *)
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.



Lemma base_contextual_step e1 e2 :
  base_step e1 e2 → contextual_step e1 e2.
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 → contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lam x e => is_closed (x :b: X) e
  | Unpack x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | TApp e | TLam e | Pack e => is_closed X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 => is_closed X e1 && is_closed X e2
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

(** Substitution lemmas *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  induction e in X |-*; simpl; rewrite ?bool_decide_spec, ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.
Lemma subst'_is_closed_nil e x es : is_closed [] e → subst' x es e = e.
Proof. intros. destruct x as [ | x]. { done. } by apply subst_is_closed_nil. Qed.


(* we derive a few lemmas about contextual steps *)
Lemma contextual_step_app_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (App e1 e2) (App e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (AppLCtx HoleCtx v)).
Qed.

Lemma contextual_step_app_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (App e1 e2) (App e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (AppRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_tapp e e':
  contextual_step e e' →
  contextual_step (TApp e) (TApp e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (TAppCtx HoleCtx)).
Qed.

Lemma contextual_step_pack e e':
  contextual_step e e' →
  contextual_step (Pack e) (Pack e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PackCtx HoleCtx)).
Qed.

Lemma contextual_step_unpack x e e' e2:
  contextual_step e e' →
  contextual_step (Unpack x e e2) (Unpack x e' e2).
  Proof.
    intros Hcontextual.
    by eapply (fill_contextual_step (UnpackCtx x HoleCtx e2)).
  Qed.

Lemma contextual_step_unop op e e':
  contextual_step e e' →
  contextual_step (UnOp op e) (UnOp op e').
  Proof.
    intros Hcontextual.
    by eapply (fill_contextual_step (UnOpCtx op HoleCtx)).
  Qed.

Lemma contextual_step_binop_l op e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (BinOp op e1 e2) (BinOp op e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (BinOpLCtx op HoleCtx v)).
Qed.

Lemma contextual_step_binop_r op e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (BinOp op e1 e2) (BinOp op e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (BinOpRCtx op e1 HoleCtx)).
Qed.

Lemma contextual_step_if e e' e1 e2:
  contextual_step e e' →
  contextual_step (If e e1 e2) (If e' e1 e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (IfCtx HoleCtx e1 e2)).
Qed.

Lemma contextual_step_pair_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (Pair e1 e2) (Pair e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (PairLCtx HoleCtx v)).
Qed.

Lemma contextual_step_pair_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (Pair e1 e2) (Pair e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PairRCtx e1 HoleCtx)).
Qed.


Lemma contextual_step_fst e e':
  contextual_step e e' →
  contextual_step (Fst e) (Fst e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (FstCtx HoleCtx)).
Qed.

Lemma contextual_step_snd e e':
  contextual_step e e' →
  contextual_step (Snd e) (Snd e').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (SndCtx HoleCtx)).
Qed.

Lemma contextual_step_injl e e':
  contextual_step e e' →
  contextual_step (InjL e) (InjL e').
  Proof.
    intros Hcontextual.
    by eapply (fill_contextual_step (InjLCtx HoleCtx)).
  Qed.

Lemma contextual_step_injr e e':
  contextual_step e e' →
  contextual_step (InjR e) (InjR e').
  Proof.
    intros Hcontextual.
    by eapply (fill_contextual_step (InjRCtx HoleCtx)).
  Qed.

Lemma contextual_step_case e e' e1 e2:
  contextual_step e e' →
  contextual_step (Case e e1 e2) (Case e' e1 e2).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (CaseCtx HoleCtx e1 e2)).
Qed.

#[export]
Hint Resolve
  contextual_step_app_l contextual_step_app_r contextual_step_binop_l contextual_step_binop_r
  contextual_step_case contextual_step_fst contextual_step_if contextual_step_injl contextual_step_injr
  contextual_step_pack contextual_step_pair_l contextual_step_pair_r contextual_step_snd contextual_step_tapp
  contextual_step_tapp contextual_step_unop contextual_step_unpack : core.
