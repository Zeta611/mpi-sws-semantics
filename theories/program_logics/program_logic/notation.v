From stdpp Require Export coPset.
From iris.bi Require Import interface derived_connectives.
From iris.prelude Require Import options.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

Inductive stuckness := NotStuck | MaybeStuck.

Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Global Instance stuckness_le : SqSubsetEq stuckness := stuckness_leb.
Global Instance stuckness_le_po : PreOrder stuckness_le.
Proof. split; by repeat intros []. Qed.


Class Swp (PROP EXPR VAL A : Type) :=
  wp : A → coPset → coPset → EXPR → (VAL → PROP) → PROP.
Global Arguments wp {_ _ _ _ _} _ _ _ _%E _%I.
Global Instance: Params (@wp) 9 := {}.

Notation "'WP' e @ s ; E1 ; E2 {{ Φ } }" := (wp s E1 E2 e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E1 ; E2 {{ Φ } }" := (wp NotStuck E1 E2 e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E1 ; E2 ? {{ Φ } }" := (wp MaybeStuck E1 E2 e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E1 {{ Φ } }" := (wp s E1 E1 e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E1 {{ Φ } }" := (wp NotStuck E1 E1 e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E1 ? {{ Φ } }" := (wp MaybeStuck E1 E1 e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e {{ Φ } }" := (wp NotStuck ⊤ ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e ? {{ Φ } }" := (wp MaybeStuck ⊤ ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "'WP' e @ s ; E1 ; E2 {{ v , Q } }" := (wp s E1 E2 e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E1 ;  '/' E2  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E1 ; E2 {{ v , Q } }" := (wp NotStuck E1 E2 e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E1 ;  '/' E2  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E1 ; E2 ? {{ v , Q } }" := (wp MaybeStuck E1 E2 e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E1 ;  '/' E2  ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  E  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck ⊤ ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

