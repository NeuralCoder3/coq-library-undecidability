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

  Definition ΣB := option Σ.
  Definition blank : ΣB := None.

  Definition ΣB_finType : finType := (@FinType (EqType ΣB) (finTypeC_Option Σ)).

  Variable tm : sTM Σ.

  Inductive colors := 
    empty | row | 
    symbol (s:ΣB) | 
    statePair (ps:states tm * ΣB) |
    state (p:states tm)
    .

  Instance eq_dec_colors : eq_dec colors.
  Proof.
    intros. hnf. repeat decide equality; apply eq_dec_sig.
  Defined.

  Definition stateSymbol := prod (states tm) ΣB.
  Definition stateSymbol_finType : finType := (@FinType (EqType stateSymbol) (finTypeC_Prod (states tm) ΣB_finType )).

  Instance finType_colors: finTypeC (EqType colors).
  Proof.
  Search finTypeC.
    pose (symbolList := let (x,_) := class ΣB_finType in x).
    pose (stateSymbolList := let (x,_) := class stateSymbol_finType in x).
    pose (stateList := let (x,_) := class (states tm) in x).
    exists (empty::row::
        (map symbol symbolList) ++
        (map statePair stateSymbolList) ++
        (map state stateList)
    ).
    intros x. destruct x; cbn. 
  Admitted.
      (* Search finTypeC. *)
      (* Print EqType. *)
      (* Print finTypeC. *)
    (* exists (hash::dollar::(List.map (fun s => sigma s) (elem sig))).
    intros x. destruct x; cbn. induction (elem sig); auto. induction (elem sig); auto.  
    apply inductive_count. intros x y; now inversion 1. apply (@enum_ok sig (class sig) s). 
  Defined. *)

  Definition colors_finType : finType := (@FinType (EqType colors) finType_colors).


  Definition initTile :=
    mkTile (statePair (start tm,blank)) empty empty row.

  Definition blankTile :=
    mkTile (symbol blank) empty row row.

  Definition passAlongTiles : tileSet colors_finType :=
    let (sym,_) := (class ΣB_finType) in 
        map 
        (fun s => 
            mkTile 
                (symbol s) 
                (symbol s) 
                row row) 
        sym.

  Definition moveIntoTiles : tileSet colors_finType :=
    let (sym,_) := (class ΣB_finType) in 
    let (tmStates,_) := (class (states tm)) in 
    concat (
        map (fun s => 
            concat (
            map (fun p => 
                [mkTile 
                    (statePair (p,s))
                    (symbol s)
                    (state p)
                    row;
                mkTile 
                    (statePair (p,s))
                    (symbol s)
                    row
                    (state p)
                ]
                ) 
            tmStates))
        sym).

  Definition transitionTile : tileSet colors_finType :=
    let (sym,_) := (class ΣB_finType) in 
    let (tmStates,_) := (class (states tm)) in 
    concat (
        map (fun s => 
            map (fun p => 
                let (q,x) := (@trans Σ tm) (p,s) in
                let (ns,d) := x in
                match d with
                | L => 
                    mkTile 
                        (symbol ns)
                        (statePair (p,s))
                        (state q)
                        row
                | R => 
                    mkTile 
                        (symbol ns)
                        (statePair (p,s))
                        row
                        (state q)
                | N => 
                    mkTile 
                        (statePair (q,ns))
                        (statePair (p,s))
                        row
                        row
                end
                ) 
            (filter (fun p => negb (halt p))
                tmStates))
        sym).

  Definition tiles : tileSet colors_finType :=
      [initTile;blankTile] ++
      passAlongTiles ++
      moveIntoTiles ++
      transitionTile
    .

End TMTransform.

Require Import ssrbool ssreflect ssrfun.

Print sTM.

Lemma haltingEnd sig (tm:sTM sig) (p:states tm): 
    halt p -> 
    ~ exists t s, In t (tiles tm) /\ bottom t = statePair (p,s).
Proof.
    rewrite /(tiles).
    move => Halt [t [s 
        [
            /(in_app_iff) [+|/(in_app_iff) [+|/(in_app_iff) [+|+]]] 
            +
        ]]].
    - case => [<-|[<-|[]]] //=. 
    - rewrite /passAlongTiles. case: (class _) => + _.
      elim => [[]|x xs IH] /= [<-|H1] //=. 
      by apply: IH.
    - rewrite /moveIntoTiles => + +. 
      case: (class _) => + _.
      case: (class _) => + _.
      move => states symbols.
      elim: symbols states => /= [+|x xs IH] /=.
      1: by elim.
      move => + /(in_app_iff) [].
      + clear IH.
        by elim => [+ |y ys IH] //= [<-|[<-|+]] //=.
      + by apply: IH.
    - rewrite /transitionTile => + +. 
      case: (class _) => + _; case: (class _) => + _.
      move => states symbols.
      elim: symbols states => /= [+|x xs IH] /=.
      1: by elim.
      move => + /(in_app_iff) [].
      + elim => [+|y ys {}IH] //=.
        case (halt y) eqn: H => //=.
        move => [<-|+].
        * case trans => ? [] ? [] //=.
          all: injection => _ G;move: G H Halt => -> -> //=.
        * apply: IH.
      + apply: IH.
Qed.


(* in every step exactly one (p,s) *)




(* TODO: in halt => no transition *)

(* Definition Wang : list tile * pattern -> Prop :=
    fun '(T,xs) => exists (f:nat->nat->nat), forall x y, exists t, getTile(f x y) = t /\  *)