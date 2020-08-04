Require Import Undecidability.Shared.Prelim.

Definition var := nat.

Inductive whileP :=
  wCon (n:var) (c:nat)
| wAdd (i j k:var)
| wSub (i j k:var)
| wWhile (i:var) (P1:whileP)
| wSeq (P1 P2 : whileP).

Definition state := var -> nat.

Open Scope nat.
Notation "x == y" := (Nat.eqb x y)(at level 71).

Definition update (x:var) (c:nat) (s:state) : state :=
  fun y => if x==y then c else s y.

Inductive ϕ (S:state) : whileP -> state -> Prop :=
  semAdd i j k: ϕ S (wAdd i j k) (update i (S j + S k) S)
| semSub i j k: ϕ S (wSub i j k) (update i (S j - S k) S)
| semCon i c: ϕ S (wCon i c) (update i c S)
| semSeq P1 P2 S2 S3: ϕ S P1 S2 -> ϕ S2 P2 S3 -> ϕ S (wSeq P1 P2) S3
| semWhileP i P1: S i = 0 -> ϕ S (wWhile i P1) S
| semWhileP2 i P1 S2 S3: S i > 0 -> ϕ S P1 S2 -> ϕ S2 (wWhile i P1) S3 -> ϕ S (wWhile i P1) S3.

Notation "i '<-' j 'w+' k" := (wAdd i j k)(at level 60).
Notation "i '<-' j 'w-' k" := (wSub i j k)(at level 60).
Notation "i ':=' c" := (wCon i c)(at level 60).
Notation "P1 ; P2" := (wSeq P1 P2)(at level 70).
Notation "'while' i 'do' P1 'od' " := (wWhile i P1)(at level 80).

Notation "S '{' a '↦' x '}'" := (update a x S)(at level 60).

Fixpoint updateList (xs:list (var*nat)) S :=
    match xs with
    | nil => S
    (* | (a,xa)::ys => update a xa (updateList ys S) *)
    | (a,xa)::ys => updateList ys (update a xa S)
    end.

(* Notation "St { a ↦ xa ; b ↦ xb ; .. ; c ↦ xc }" := 
    (updateList (cons (a,xa) (cons (b,xb) .. (cons (c,xc) nil) .. )) S)(at level 60). *)
(* Notation "St { a ↦ xa ; b ↦ xb ; .. ; c ↦ xc ; d ↦ xd }" := 
    (update a xa ((update b xb .. (update c xc (update d xd S)) .. )))(at level 60). *)

Definition WhileHalting :=
    fun '(P,s) => exists s', ϕ s P s'.

Definition StatelessHalting :=
    fun P => exists s', ϕ (fun _ => 0) P s'.


Inductive whileP' :=
| wInc (i:var)
| wDec (i:var)
| wWhile' (i:var) (P1:whileP')
| wSeq' (P1 P2 : whileP').

(* Inductive phi (S:state) : whileP' -> state -> Prop := 
  semInc i: phi' s (wInc i) (update i (1 + (s i)) s)
| semDec i: phi' s (wDec i) (update i ((s i)-1) s)
| semSeq' P1 P2 S2 S3: phi' s P1 S2 -> phi' S2 P2 S3 -> phi' s (wSeq P1 P2) S3
| semWhileP' i P1: s i = 0 -> phi' s (wWhile i P1) s
| semWhileP2' i P1 S2 S3: s i > 0 -> phi' s P1 S2 -> phi' S2 (wWhile i P1) S3 -> phi' s (wWhile i P1) S3. *)





(* Reductions: CM1 <= While <= While' <= BF *)


Require Import ssreflect ssrbool ssrfun.
Require Import Nat Arith Lia PeanoNat.
Require Import FunctionalExtensionality.
Require Import Equality.

Lemma eqb_refl t: t==t.
Proof.
    elim: t => [|? ? //=];first done.
Qed.

Lemma stateOverwrite S x a b: update x b (update x a S) = update x b S.
Proof.
    apply: functional_extensionality => ?.
    rewrite /(update).
    by case Nat.eqb.
Qed.







Definition assertion := state -> Prop.
Notation "s =[ P ]=> s'" := (ϕ s P s')(at level 60).
Definition hoare (P:assertion) P1 (Q:assertion) :=
    forall s s', s =[ P1 ]=> s' -> P s -> Q s'.
Notation "{{ P }} c {{ Q }}" := (hoare P c Q)(at level 90, c at next level).

Lemma hoareCon P x c: {{ fun s => P (update x c s)}} x := c {{ P }}.
Proof.
    move => s s' H.
    by inversion H;subst.
Qed.

Lemma hoareAdd P i j k: {{ fun s => P (update i (s j + s k) s)}} i <- j w+ k {{ P }}.
Proof.
    move => ? ? H;by inversion H;subst.
Qed.

Lemma hoareSub P i j k: {{ fun s => P (update i (s j - s k) s)}} i <- j w- k {{ P }}.
Proof.
    move => ? ? H;by inversion H;subst.
Qed.

Lemma hoareSeq P Q R c1 c2: 
    {{ P }} c1 {{ Q }} -> 
    {{ Q }} c2 {{ R }} ->
    {{ P }} c1;c2 {{ R }}.
Proof.
    rewrite /(hoare).
    move => + + s s' H.
    inversion H;subst.
    move => /(_ _ _ H2) + /(_ _ _ H4) + Hp.
    by move => /(_ Hp) Hq /(_ Hq).
Qed.

Lemma hoareConseq (P1 P2 Q1 Q2 : assertion) c: 
    (forall s, P1 s -> P2 s) -> 
    {{ P2 }} c {{ Q2 }} -> 
    (forall s, Q2 s -> Q1 s) ->
    {{ P1 }} c {{ Q1 }}.
Proof.
    move => I1 + I2 s s' G.
    move /(_ s s' G) => + /I1 P.
    by move /(_ P) /I2.
Qed.

Lemma hoareWhile P i c:
    {{ fun s => P s /\ s i > 0 }} c {{ P }} ->
    {{ P }} while i do c od {{ fun s => P s /\ s i=0 }}.
Proof.
    move => H1 s s' H.
    dependent induction H;subst.
    - by constructor.
    - move => Hp.
      case (IHϕ2 i c);try done.
      apply H1 in H0.
      apply: H0. by constructor.
Qed.

Lemma hoareConGen P' P x c: (P'= fun s => P (update x c s)) -> {{ P' }} x := c {{ P }}.
Proof.
    move => ->.
    by apply: hoareCon.
Qed.

Lemma hoareAddGen P' P i j k: (P'= fun s => P (update i (s j + s k) s)) -> {{ P' }} i <- j w+ k {{ P }}.
Proof.
    move => ->.
    by apply: hoareAdd.
Qed.

Lemma hoareSubGen P' P i j k: (P'= fun s => P (update i (s j - s k) s)) -> {{ P' }} i <- j w- k {{ P }}.
Proof.
    move => ->.
    by apply: hoareSub.
Qed.








Goal forall s, ~ exists s', ϕ s (0 := 1;while 0 do 0 := 1 od) s'.
Proof.
    move => s [s' H].
    inversion H;subst.
    dependent induction H4.
    (* inversion H4;subst. *)
    - inversion H2;subst.
      move: H0.
      rewrite /(update) eqb_refl.
      discriminate.
    - apply IHϕ2;try done.
      inversion H4_;subst.
      inversion H2;subst.
      by rewrite (stateOverwrite).
Qed.

Definition wWhileLt a b t P :=
    t <- b w- a;
    while t do
        P;
        t <- b w- a
    od.

Lemma semWhileLtEnd s a b t P: s b <= s a -> ϕ s (wWhileLt a b t P) (update t 0 s).
Proof.
    move => H.
    rewrite /(wWhileLt).
    econstructor;first by constructor.
    have ->: (s b - s a = 0) by lia.
    constructor. rewrite /(update).
    by rewrite eqb_refl.
Qed.

Lemma semWhilteLt S1 S2 S3 a b t P:  
    S1 a < S1 b -> 
    ϕ (update t (S1 b - S1 a) S1) P S2 -> 
    ϕ S2 (wWhileLt a b t P) S3 -> 
    ϕ S1 (wWhileLt a b t P) S3.
Proof.
    move => H H2 H3.
    econstructor;first by constructor.
    econstructor.
    - rewrite /(update) eqb_refl.
      lia.
    - econstructor; first by apply: H2.
      constructor.
    - inversion H3;subst.
      inversion H4;subst.
      apply: H6.
Qed.

Lemma hoareWhileLt P a b t c:
    {{ fun s => P s /\ s a < s b }} c {{ P }} ->
    {{ P }} wWhileLt a b t c {{ fun s => P s /\ b <= a }}.
Proof.
    move => H.
    rewrite /(wWhileLt).
    apply: hoareSeq.
    - eapply hoareConseq.
      2: apply: hoareSub.
      admit.
      admit.
    - apply: hoareConseq.
      2: {
        apply: hoareWhile.
        eapply hoareSeq.
        2: apply hoareSub.
admit.
      }
Admitted.

Definition wDivMod i j k l t1 t2 :=
    k := 0;
    l := 0;
    t1 := 1;
    wWhileLt l i t2 
    (
        l <- l w+ j;
        k <- k w+ t1
    );
    k <- k w- t1;
    l <- l w- j;
    l <- i w- j.

    (* Search modulo. *)


Lemma hoareDivMod n m i j k l t1 t2: 
    {{ fun s => s i = n /\ s j = m }} 
    (wDivMod i j k l t1 t2) 
    {{ fun s => 
        s i = n /\ 
        s j = m /\ 
        s l = (modulo n m) /\
        s k = (div n m)
     }}.
Proof.
    rewrite /(wDivMod).
    apply: hoareSeq.
    apply: hoareSeq.
    apply: hoareSeq.
    apply: hoareSeq.
    apply: hoareSeq.
    apply: hoareSeq.
    2,3: apply: hoareCon.
    3-5: apply: hoareSub.
    all: simpl.
    - apply: hoareConseq.
      2: apply: hoareCon.
Admitted.

    (* ϕ S1 (wDivMod i j k l t1 t2) 
    (updateList ((t1,1)::(t2,0)::(k,div (S1 i) (S1 j))::(l,modulo (S1 i) (S1 j))::[]) S1).


Lemma semDivMod i j k l t1 t2 S1: 
    ϕ S1 (wDivMod i j k l t1 t2) 
    (updateList ((t1,1)::(t2,0)::(k,div (S1 i) (S1 j))::(l,modulo (S1 i) (S1 j))::[]) S1).
Proof.
    rewrite /wDivMod.
    (* do 6 does not work *)
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    all: try constructor.
    - admit.
    -  *)

(* Lemma semDiv i j k l t1 t2 S1 S2: ϕ S1 (wDivMod i j k l t1 t2) S2 -> S2 k = i / j *)

(* if a==0 then P1 else P2 *)
(* Definition wIf a P1 P2 t :=
    t := 1;
    t <- t w- a;
    while t do
      P1;
      t := 0
    od;
    t := 0;
    t <- t w+ a;
    while t do 
      P2;
      t:=0
    od. *)
Definition wIf a P1 P2 t1 t2 :=
    t1 := 1;
    t1 <- t1 w- a;
    t2 := 0;
    t2 <- t2 w+ a;
    while t1 do
      P1;
      t2 := 0
    od;
    while t2 do 
      P2;
      t2:=0
    od.

Lemma stateAssertionExtension P (s t: state):
    (forall v, s v = t v) ->
    P s -> P t.
Proof.
    by move => /(functional_extensionality) ->.
Qed.

Lemma hoareIf P Q a P1 P2 t1 t2:
    t1 <> t2 -> a <> t1 -> a <> t2 ->

    (* need P1, P2, P do not involve t1 t2  (or for P1, P2 t1,t2=0) *)
    (forall s vx vy, P s <-> P (update t2 vy (update t1 vx s))) ->

    {{ fun s => s a = 0 /\ P s }} P1 {{ Q }} ->
    {{ fun s => s a > 0 /\ P s }} P2 {{ Q }} ->
    {{ P }} wIf a P1 P2 t1 t2 {{ Q }}.
Proof.
    move => G1 G2 G3 TS H1 H2. rewrite /(wIf).
    apply: (@hoareSeq _ (fun s => s t1 = 1-s a /\ s t2 = s a /\ P s)).
    - apply: hoareSeq.
      apply: hoareSeq.
      apply: hoareSeq.
      4: apply: hoareAdd.
      3: apply: hoareCon.
      2: apply: hoareSub.
      apply: hoareConseq.
      3: move => ? H;apply: H.
      2: apply hoareCon.
      move => s Hp /=.
      (* rewrite stateOverwrite. *)
      rewrite /update.
      repeat rewrite eqb_refl.
      replace (t1==a) with false by admit.
      replace (t2==a) with false by admit.
      replace (t2==t1) with false by admit.
      split;split;try done.
      move: (TS s (1-s a) (s a)).
      rewrite /(update).
      move => [+ _]. move /(_ Hp). 
      apply: stateAssertionExtension => v.
      case (t2==v), (t1==v);done.
    - move => s s' H.
      inversion H;subst;clear H.
      case E: (s a) => [|?] /= [H [H' H'']].
      + admit.
      + inversion H4;subst.
        2: lia.
        apply: (H2 S2).
        2: split;trivial;lia.
Admitted.

(* Notation "'if' a 'then' P1 'else' P2" := () *)

(* Require Import Undecidability.CounterMachines.CM1. *)

Definition State := nat.
Definition Instruction := prod State nat.
Definition Cm1 := list Instruction.

Check wDivMod.
Check hoareDivMod.

(*

for while programs
https://github.com/NeuralCoder3/TI/blob/master/while/while.v

*)

(* Fixpoint stepConvert (pc val continue pc' one:var) (prog:Cm1) (tmp:nat) :=
    match prog with 
      [] => 
        continue := 0
    | (p,c)::prog' => 
        let tmp1 := tmp in
        let tmp2 := S tmp1 in
        let tmp3 := S tmp2 in (* S c *)
        let tmp4 := S tmp3 in
        let tmp5 := S tmp4 in
        let tmp6 := S tmp5 in
        let tmp7 := S tmp6 in
        let tmp8 := S tmp7 in
        let tmp9 := S tmp8 in
        let tmp10 := S tmp9 in
        let tmp11 := S tmp10 in
        let tmp12 := S tmp11 in
        let newTmp := S tmp12 in
        wIf pc' 
        (
            tmp3 := (S c);
            wDivMod 
                val tmp3 
                tmp4 (* div *)
                tmp5 (* mod *)
                tmp6 tmp7; (* tmp *)
            wIf tmp5
            (
                tmp8 <- val w+ one; (* n+1 *)
                tmp8 <- tmp8 w+ one; (* n+2 *)
                wMul tmp4 tmp8
                    tmp9 (* val*(n+2)/(n+1) = val/(n+1) * (n+2) *)
                    tmp10; (* tmp *)
                pc := p
            )
            (
                pc <- pc w+ one
            )
            tmp11 tmp12
        )
        (
            pc' <- pc' w- one;
            stepConvert pc val continue pc' one prog newTmp
        )
        tmp1 tmp2
    end.


Definition innerPart (pc val continue pc' one:var) (prog:CM1) (tmp:nat) :=
    pc' <- 0;
    pc' <- pc' w+ pc;
    stepConvert pc val continue pc' one prog tmp.

Definition CMInterpreter (prog:CM1) :=
    let pc := 0 in
    let val := 1 in
    let continue := 2 in
    let pc' := 3 in
    let one := 4 in
    let tmp := 5 in
    one := 1;
    pc := 0;
    val := 1;
    continue := 1;
    while continue do
        innerPart pc val continue pc' one prog tmp
    od. *)