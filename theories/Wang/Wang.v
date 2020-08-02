Require Import Undecidability.Shared.Prelim.


Record tile := mkTile {
    top : nat;
    bottom: nat;
    left: nat;
    right: nat
}.

Definition pattern := list tile.

Definition getTile := nth_error.

(* Definition Wang : list tile * pattern -> Prop :=
    fun '(T,xs) => exists (f:nat->nat->nat), forall x y, exists t, getTile(f x y) = t /\  *)