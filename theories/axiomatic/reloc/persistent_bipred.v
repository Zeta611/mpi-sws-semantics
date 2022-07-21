(* Adapted from the persistent preds at https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/logrel/persistent_pred.v *)
From stdpp Require Import tactics.
From iris.bi Require Import bi.
From iris.prelude Require Import options.

Section persistent_pred.
  Context (A : Type) (PROP : bi).

  (* The domain of semantic types: persistent Iris bipredicates type over A. *)
  Record persistent_bipred := PersBiPred {
    pers_bipred_car :> A → A → PROP;
    pers_bipred_persistent x y : Persistent (pers_bipred_car x y)
  }.
  Local Arguments PersBiPred _%I {_}.
  Global Existing Instances pers_bipred_persistent.

  Local Instance persistent_bipred_equiv : Equiv persistent_bipred :=
    λ Φ Φ', ∀ x y, Φ x y ≡ Φ' x y.
  Local Instance persistent_bipred_dist : Dist persistent_bipred :=
    λ n Φ Φ', ∀ x y, Φ x y ≡{n}≡ Φ' x y.
  Definition persistent_bipred_ofe_mixin : OfeMixin persistent_bipred.
  Proof. by apply (iso_ofe_mixin (pers_bipred_car : _ → A -d> A -d> _)). Qed.
  Canonical Structure persistent_bipredO :=
    Ofe persistent_bipred persistent_bipred_ofe_mixin.

  Global Instance persistent_bipred_cofe : Cofe persistent_bipredO.
  Proof.
    apply (iso_cofe_subtype' (λ Φ : A -d> A -d> PROP, ∀ w w', Persistent (Φ w w'))
      PersBiPred pers_bipred_car)=> //.
    - apply _.
    - apply limit_preserving_forall=> w.
      apply limit_preserving_forall=> w'.
      apply bi.limit_preserving_Persistent => n Φ Ψ H. apply H.
  Qed.

  Global Instance persistent_bipred_car_ne n :
    Proper (dist n ==> (=) ==> (=) ==> dist n)
      pers_bipred_car.
  Proof. by intros ? ? ? ? ? -> ? ? ->. Qed.
  Global Instance persistent_bipred_car_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) pers_bipred_car.
  Proof. by intros ? ? ? ? ? -> ? ? ->. Qed.

  Lemma persistent_pred_ext (f g : persistent_bipred) : f ≡ g ↔ ∀ x y, f x y ≡ g x y.
  Proof. done. Qed.

  Global Instance: Inhabited persistent_bipred := populate (PersBiPred (λ _ _, True))%I.

End persistent_pred.

Global Arguments PersBiPred {_ _} _%I {_}.
Global Arguments pers_bipred_car {_ _} !_ _ _.
Global Instance: Params (@pers_bipred_car) 2 := {}.
