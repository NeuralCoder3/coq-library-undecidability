Require Import Undecidability.Shared.Prelim.

Definition symbol := nat.
Definition word := list symbol.
Definition program := list word. (* ith -> word *)

Definition step (M:program) (w:word) :=
    match w with
      x::y::w' => w' ++ nth_default [] M x
    | _ => []
    end.

Definition halting (w:word) := w = [].
Definition tag_Halting M w := exists n, halting (Nat.iter n (step M) w).



Require Import Coq.Relations.Relation_Operators.
Definition stepR M (w w2:word) := step M w = w2.
Definition rtcStep M := clos_refl_trans word (stepR M).

Inductive stepN (M:program) (w:word) : nat -> word -> Prop :=
  stepO: stepN M w 0 w
| stepS w' w'' n: stepR M w w' -> stepN M w' n w'' -> stepN M w (S n) w''.





Require Import ssreflect ssrbool ssrfun.
Require Import Lia.
Require Import Coq.Classes.RelationClasses.

Lemma iterInner M w n: step M  (Nat.iter n (step M) w) = Nat.iter n (step M) (step M w).
Proof.
    elim: n => [|n IH] //=.
    by rewrite IH.
Qed.

Lemma stepIndexed M w n w': stepN M w n w' <-> Nat.iter n (step M) w = w'.
Proof.
    split.
    - elim => [{}w|{}w {}w' w'' {}n H1 H2 IH] //=.
      by rewrite iterInner H1.
    - elim : n w w' => [w w' /= ->|n IH w w'] /=;first constructor.
      rewrite iterInner => /(IH) H. by econstructor.
Qed.

Lemma lengthExtend {X} (xs:list X) n: | xs | = S n -> exists x xr, xs = x::xr /\ |xr| = n.
Proof.
    case: xs => /= [H|x xs H];first discriminate.
    exists x;exists xs;split;first done;lia.
Qed.

Lemma appIsNil {X} (x:list X) y: x=x++y -> y = [].
Proof.
    elim: x y => [|x xs IH] ys /=;first done.
    move => H. apply: IH.
    by injection H.
Qed.

Lemma oneStepResolve M a b X Y: stepR M (a::b::X) Y -> Y=X++nth_default [] M a.
Proof.
  done.
Qed.

(* Lemma extendStepOne M m X Y a b:
  | X | = 2*m ->
  stepN M X m Y ->
  stepN M (a::b::X) (S m) (nth_default [] M a++Y).
Proof.
  elim: m X Y a b => [|m IH] X Y a b.
  - move => /length_zero_iff_nil -> /= H.
    inversion H;subst.
    econstructor;first by rewrite /stepR /step.
    rewrite app_nil_r /=;constructor.
  - replace (2*S m) with (S(S(2*m))) by lia.
    move => /lengthExtend [s0 [wr [Heq1 /lengthExtend [s1 [x' [Heq2 Hlen]]]]]] H;subst.
    inversion H;subst.
    unfold stepR, step in H1;cbn in H1;subst.
    econstructor;first by rewrite /stepR /step /=.

  move => H1 H2.
  elim : H2 a b H1 => [{}X|{}X X' X'' {}m H1 H2 IH] a b.
  - move => /length_zero_iff_nil -> /=.
    econstructor;first by rewrite /stepR /step.
    rewrite app_nil_r /=;constructor.
  - replace (2*S m) with (S(S(2*m))) by lia.
    move => /lengthExtend [s0 [wr [Heq1 /lengthExtend [s1 [x' [Heq2 Hlen]]]]]];subst.
    unfold stepR, step in H1;cbn in H1;subst.
    econstructor;first by rewrite /stepR /step /=. *)
    (* econstructor;first by rewrite /stepR /step. *)


(* Lemma multiStepResolve M m X Y C:
 | X | = 2*m -> stepN M (X++C) m Y ->
 exists Y', stepN M X m Y' /\ Y=C++Y'.
Proof.
  elim: m X Y C => [|m IH] X Y C + Hs.
  - inversion Hs;subst. move => /length_zero_iff_nil -> /=. exists []. split;first constructor.
    by rewrite app_nil_r.
  - replace (2*S m) with (S(S(2*m))) by lia.
    move => /lengthExtend [s0 [wr [Heq1 /lengthExtend [s1 [x' [Heq2 Hlen]]]]]];subst.
    inversion Hs;subst. unfold stepR, step in H0;cbn in H0; subst w'.
    move: H1. rewrite -app_assoc. move => /(IH _ _ _ Hlen) [Y' [H ?]];subst.
    eexists;split.

  move => + H.
  elim: H => /=.
  -  *)

(* Lemma execWord M x y z n: 
    length x = 2*n -> 
    stepN M x n y <-> 
    stepN M (x++z) n (z++y).
Proof.
    elim: n x y z => [|n IH];move => x y z.
    - move => /length_zero_iff_nil -> /=.
      split;move => H;inversion H;subst.
      + rewrite app_nil_r;constructor.
      + rewrite (appIsNil H1);constructor.
    - replace (2*S n) with (S(S(2*n))) by lia.
      move => /lengthExtend [s0 [wr [Heq1 /lengthExtend [s1 [x' [Heq2 Hlen]]]]]];subst.
      split;move => H.
      + inversion H;subst.
        unfold stepR, step in H1; subst w'.
        simpl;econstructor;first reflexivity.
        rewrite /stepR /step -app_assoc.  *)



Lemma execWord M x y z n: 
    length x = 2*n -> 
    stepN M x n y -> 
    stepN M (x++z) n (z++y).
Proof.
    (* move => H G.
    elim: n x y z G H => [|n IH];move => x y z G;inversion G;subst.
    - move => /length_zero_iff_nil -> /=.
      rewrite app_nil_r;constructor.
    - replace (2*S n) with (S(S(2*n))) by lia.
      move => /lengthExtend [s0 [wr [Heq1 /lengthExtend [s1 [x' [Heq2 Hlen]]]]]];subst.
      unfold stepR, step in H0; subst w'.
      simpl;econstructor;first reflexivity.
      rewrite /stepR /step -app_assoc. apply IH.

      econstructor.
      2: apply: H1.
      transitivity H1.
    - 

    elim: G z H => [w|w w' w'' {}n H1 H2 IH];move => z.
    - move => /length_zero_iff_nil -> /=.
      rewrite app_nil_r;constructor.
    - replace (2*S n) with (S(S(2*n))) by lia.
      move => /lengthExtend [s0 [wr [Heq1 /lengthExtend [s1 [wrr [Heq2 _]]]]]].
      


      have [s1 [s2 H]]: (exists s1 s2 wr, w=s1::s2::wr).
      {
      } *)

Admitted.






Fixpoint repeat {X} (symbols:list X) (n:nat) :=
    match n with
      O => []
    | S m => symbols ++ repeat symbols m
    end.

Lemma stepToRTC M m X Y: stepN M X m Y -> rtcStep M X Y.
Proof.
  elim => [w|w w' w'' n <- H1 H2];first do 2 constructor.
  econstructor 3.
  2: apply: H2.
  by constructor.
Qed.


(* Goal forall n m o, 2*m+o = 2*n -> rtcStep collatz ((repeat [0] (2*m) ++ repeat [1;2] o)) (repeat [0] n).
Proof.
    move => + m.
    elim : m => [n o H|m IH n o H] /=.
    - elim : o n H => [|o IH n H].
        + admit.
        + 
     admit.
    -  *)

Lemma repeatLen {X} (xs:list X) n: | repeat xs n | = n* | xs |.
Proof.
  elim : n => [|n IH] //=.
  by rewrite app_length IH.
Qed.



Definition collatz : program :=
    [
        [1;2];
        [0];
        [0;0;0]
    ].


Lemma ruleRepeat M a x n:
  stepN M (repeat [a;x] n) n (repeat (nth_default [] M a) n).
Proof.
    elim : n => [|n IH] /=;first constructor.
    econstructor;
    first by rewrite /stepR /step /collatz /nth_default /=. 
    apply: execWord;
    first (rewrite repeatLen /=;lia).
    apply: IH.
Qed.


(* Lemma collatzAToBC n:
stepN collatz (repeat [0] (2 * n)) n (repeat [1; 2] n).
Proof.
    (* elim : n => [|n IH];first constructor.
    replace (repeat _ (2*S n)) with (0::0::repeat [0] (2*n)).
    2: by replace (2*(S n)) with (2+2*n) by lia.
    econstructor;
    first by rewrite /stepR /step /collatz /nth_default /=. 
    apply: execWord;
    first (rewrite repeatLen /=;lia).
    apply: IH. *)
    replace (repeat [0] (2*n)) with (repeat [0;0] n).
    2: {
      elim : n => [|n /= ->] //=.
      by replace (n+S _) with (S(n+(n+0))) by lia.
    }
    apply ruleRepeat.
Qed. *)

(* Lemma collatzBCToA n:
stepN collatz (repeat [1; 2] n) n (repeat [0] n).
Proof.
    (* elim : n => [|n IH] /=;first constructor.
    econstructor;
    first by rewrite /stepR /step /collatz /nth_default /=. 
    apply: execWord;
    first (rewrite repeatLen /=;lia).
    apply: IH. *)
    apply ruleRepeat.
Qed.

Lemma collatzCBToA n:
stepN collatz (repeat [2; 1] n) n (repeat [0;0;0] n).
Proof.
    (* elim : n => [|n IH] /=;first constructor.
    econstructor;
    first by rewrite /stepR /step /collatz /nth_default /=. 
    apply: execWord;
    first (rewrite repeatLen /=;lia).
    apply: IH. *)
Qed. *)

Lemma repeatDuplicate {X} (x:list X) n:  repeat x (2*n) = repeat (x++x) n.
Proof.
  elim : n => [|n /= <-] //=.
  replace (n+S _) with (S(n+(n+0))) by lia => /=.
  by rewrite app_assoc.
Qed.

Lemma collatzEven n: rtcStep collatz (repeat [0] (2*n)) (repeat [0] n).
Proof.
    apply: (rt_trans _ _ _ (repeat [1;2] n)).
    - apply (stepToRTC (m:=n)).
      rewrite repeatDuplicate.
      apply ruleRepeat.
    - apply (stepToRTC (m:=n)).
      apply ruleRepeat.
Qed.

Lemma repeatAdd {X} (xs:list X) n m: repeat xs (n+m) = repeat xs n ++ repeat xs m.
Proof.
  elim: n m => [|n IH] m //=.
  by rewrite IH app_assoc.
Qed.

Lemma collatzOdd n m: n=S m -> rtcStep collatz (repeat [0] (2*n+1)) (repeat [0] (3*n+2)).
Proof.
  move => H.
  apply: (rt_trans _ _ _ (0::repeat [1;2] n)).
  2: apply: (rt_trans _ _ _ (repeat [2;1] n ++ [2])).
  3: apply: (rt_trans _ _ _ (2::repeat [0;0;0] n)).
  - apply (stepToRTC (m:=n)).
    rewrite repeatAdd /=.
    apply: execWord; first (rewrite repeatLen /=;lia).
    rewrite repeatDuplicate.
    apply ruleRepeat.
  - move: H => -> /=;constructor.
    rewrite /stepR /step /nth_default /collatz //=.
    elim: m => [|m /= ->] //=.
  - apply (stepToRTC (m:=n)).
    apply: execWord; first (rewrite repeatLen /=;lia).
    apply ruleRepeat.
  - constructor.
    move: H => ->.
    replace (3*S m) with (3+3*m) by lia.
    rewrite /stepR /step /nth_default /collatz /=;do 2 f_equal.
    elim: m => [|m /= ->] //=.
    by replace (m+S(m+S(m+0))) with (2+m+(m+(m+0))) by lia.
Qed.

Inductive collRel : nat -> nat -> Prop :=
| collEven n: collRel (2*n) n
| collOdd n: collRel (2*n+1) (3*n+2).

Require Import Coq.Program.Equality.

Lemma tagHaltingStepN M w:
tag_Halting M w <-> exists n w', halting w' /\ stepN M w n w'.
Proof.
  split => [[n H]|[n [w' [H H']]]].
  - exists n; eexists;split;first apply: H;clear H.
    elim: n w => [|n IH] w /=;first constructor.
    econstructor;first done.
    rewrite iterInner.
    apply: IH.
  - exists n.
    elim: H' H => [{}w|{}w {}w' w'' {}n H1 H2 IH] H //=.
    move: H1 H2 (IH H) => <- _.
    by rewrite iterInner.
Qed.

Lemma tagHaltingStepNnil M w:
tag_Halting M w <-> exists n, stepN M w n [].
Proof.
  rewrite tagHaltingStepN.
  split => [[n [? [-> H]]]|[n H]].
  - by exists n.
  - by exists n, [];split.
Qed.


(* Goal forall n m, clos_refl_trans _ collRel n m <-> rtcStep collatz (repeat [0] n) (repeat [0] m).
Proof.
  move => n m;split.
  - elim => [x y H|x|x y z H1 IH1 H2 IH2].
    + inversion H. *)


Goal forall x, x>0 -> clos_refl_trans _ collRel x 1 <-> tag_Halting collatz (repeat [0] x).
Proof.
  move => x Hx.
  rewrite tagHaltingStepNnil.
  split => [H|[n H']].
  - dependent induction H;
    admit.
    (* + have ->: (x = 2) by admit.
      exists 3;split;first done.
      do 4 econstructor.
    + exists 1, [];split;first done.
      do 2 econstructor.
    + admit. *)
  - 
  (* - dependent induction H'.
    + inversion x.
      have Hx': (x0 = 0) by admit.
      lia.
    + apply IHH'.
  - elim: n x Hx H' => [|n IH] x Hx H'.
    + inversion H'.
      have Hx': (x = 0) by admit.
      lia.
    + inversion H';subst.
  
  elim: H' H => [w|w w' w'' m H1 H2 IH] H /=.
    +  *)