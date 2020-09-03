Require Import Undecidability.Shared.Prelim.
Require Import PslBase.FiniteTypes PslBase.FiniteTypes.BasicDefinitions PslBase.EqDec.

Section Wang.

    Variable color: finType.

    Record tileKind := mkTile {
        top : color;
        bottom: color;
        left: color;
        right: color
    }.

    Definition tiling := nat -> nat -> nat.

    Definition tileSet := list tileKind.

    Definition getTile (T:tileSet) (f:tiling) x y : option tileKind := nth_error T (f x y).

    Definition valid (T:tileSet) (f:tiling) := 
        forall x y, 
        exists t, Some t = getTile T f x y /\
        exists tAbove, Some tAbove = getTile T f x (S y) /\
        exists tRight, Some tRight = getTile T f (S x) y /\
        (* let t := f x y in
        let tAbove := f x (S y) in
        let tRight := f (S x) y in *)
            top t = bottom tAbove /\
            right t = left tRight.

End Wang.


Require Import Undecidability.TM.TM.
Require Import Undecidability.Shared.Prelim.
Require Import Undecidability.StringRewriting.Util.singleTM.
Require Import Undecidability.StringRewriting.Reductions.TM_to_SRH.

Require Import PslBase.FiniteTypes PslBase.FiniteTypes.BasicDefinitions PslBase.EqDec.


Section TMTransform.

  (* TM -> tilSet *)

  Variable Σ : finType.

  Inductive ΣB := blank | sigmaSymbol (s:Σ).

  Instance eq_dec_sigB : eq_dec ΣB.
  Proof.
    intros. hnf. decide equality; apply eq_dec_sig.
  Defined.

  Instance finType_sigB : finTypeC (EqType ΣB).
  Proof.
    exists (blank::(List.map (fun s => sigmaSymbol s) (elem Σ))).
    intros x. destruct x; cbn. 
    induction (elem Σ); auto.
    apply inductive_count. intros x y; now inversion 1. apply (@enum_ok Σ (class Σ) s). 
  Defined.

  Variable tm : sTM Σ.

  Inductive colors := 
    empty | row | 
    symbol (s:ΣB) | 
    statePair (p:states tm) (s:ΣB) |
    state (p:states tm)
    .

  Instance eq_dec_colors : eq_dec colors.
  Proof.
    intros. hnf. decide equality;try apply eq_dec_sigB.
  Admitted.

  Instance finType_colors: finTypeC (EqType colors).
  Proof.
  Admitted.
      (* Search finTypeC. *)
      (* Print EqType. *)
      (* Print finTypeC. *)
    (* exists (hash::dollar::(List.map (fun s => sigma s) (elem sig))).
    intros x. destruct x; cbn. induction (elem sig); auto. induction (elem sig); auto.  
    apply inductive_count. intros x y; now inversion 1. apply (@enum_ok sig (class sig) s). 
  Defined. *)

  Definition colors_finType : finType := (@FinType (EqType colors) finType_colors).
  Definition ΣB_finType : finType := (@FinType (EqType ΣB) finType_sigB).


  (* Print finType.
  Print finTypeC.

  Check (class Σ).
  Check tileSet. *)
  (* Print sTM. *)

  Definition tiles : tileSet colors_finType :=
      (* init tile *)
      [mkTile (statePair (start tm) blank) empty empty row] ++ 
      (* empty tile *)
      [mkTile (symbol blank) empty row row] ++ 

    (* move along *)
    (let (sym,_) := (class ΣB_finType) in 
        map (fun s => 
            mkTile 
                (symbol s) 
                (symbol s) 
                row row) 
            sym) ++ 

    (* move into *)
    (
    let (sym,_) := (class ΣB_finType) in 
    let (tmStates,_) := (class (states tm)) in 
    concat (
        map (fun s => 
            map (fun p => 
                mkTile 
                    (statePair p s)
                    (symbol s)
                    (state p)
                    row
                ) 
            tmStates)
        sym)
        )

    (* transitions *)

    .

    (* TODO: blank with option *)


  (* Check tiles. *)


End TMTransform.


(* TODO: in halt => no transition *)

(* Definition Wang : list tile * pattern -> Prop :=
    fun '(T,xs) => exists (f:nat->nat->nat), forall x y, exists t, getTile(f x y) = t /\  *)