From iris.heap_lang Require Import lang notation.

Implicit Types (e : expr) (v : val).

Definition TApp e : expr := e #().
Notation "e <>" := (TApp e) (at level 50) : expr_scope.

Definition TLamV e : val := λ: <>, e.
Definition TLam e : expr := λ: <>, e.
Notation "Λ, e" := (TLamV e) (at level 100) : val_scope.
Notation "Λ, e" := (TLam e) (at level 100) : expr_scope.

Definition Pack e : expr := e.
Definition PackV v : val := v.
Notation "'pack' e" := (Pack e) (at level 60) : expr_scope.
Notation "'pack' v" := (PackV v) (at level 60) : val_scope.

Definition Unpack e (x : binder) e2 : expr := (λ: x, e2) e.
Notation "'unpack' e 'as' x 'in'  e2" := (Unpack e%E x e2%E) (at level 40) : expr_scope.

Definition Roll e : expr := e.
Definition RollV v : val := v.
Notation "'roll' e" := (Roll e) (at level 60) : expr_scope.
Notation "'roll' v" := (RollV v) (at level 60) : val_scope.

Definition Unroll e : expr := let: "x" := e in "x".
Notation "'unroll' e" := (Unroll e) (at level 60) : expr_scope.

