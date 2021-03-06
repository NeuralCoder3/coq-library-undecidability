From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Export LTactics GenEncode.
Require Import PslBase.Numbers.

Require Import Nat.
From Undecidability.L Require Import Datatypes.LBool Functions.EqBool.
Import GenEncode. Import Nat.
(** ** Encoding of natural numbers *)

Run TemplateProgram (tmGenEncode "nat_enc" nat).
Hint Resolve nat_enc_correct : Lrewrite.

Instance termT_S : computableTime' S (fun _ _ => (1,tt)).
Proof.
  extract constructor.
  solverec.
Defined.

Instance termT_pred : computableTime' pred (fun _ _ => (5,tt)).
Proof.
  extract.
  solverec.
Defined.

Instance termT_plus' : computableTime' add (fun x xT => (5,(fun y yT => (11*x+4,tt)))).
Proof.
  extract.
  fold add. solverec.
Defined.

Instance termT_mult : computableTime' mult (fun x xT => (5,(fun y yT => (x * (11 * y) + 19*x+ 4,tt)))).
Proof.
  extract.
  fold mul. solverec.
Defined.

Instance term_sub : computableTime' Nat.sub (fun n _ => (5,fun m _ => (min n m*14 + 8,tt)) ).
Proof.
  extract. recRel_prettify_arith. solverec.
Qed.

Instance termT_leb : computableTime' leb (fun x xT => (5,(fun y yT => (min x y*14 + 8,tt)))).
Proof.
  extract.
  solverec.
Defined.


Instance eqbNat_inst : eqbClass Nat.eqb.
Proof.
  exact Nat.eqb_spec. 
Qed.

Instance eqbComp_nat : eqbCompT nat.
Proof.
  evar (c:nat). exists c. unfold Nat.eqb.
  unfold enc;cbn.
  extract.
  solverec.
  [c]:exact 5.
  all:unfold c;try lia.
Qed.

Instance termT_pow:
  computableTime' Init.Nat.pow   (fun (x : nat) _ => (5,fun (n : nat) _ => (n* (x*19+x^n*11+19) + 5, tt))).
Proof.
  extract. fold Nat.pow. solverec.
  replace (11 * n * x2 * x2 ^ n) with (11 * n * x2 ^ (1 + n)). 2:now cbn;nia.
  decide (x2=0). { subst. ring_simplify. destruct n. now cbn;Lia.nia. now rewrite !pow_0_l. }
                 rewrite <- pow_le_mono_r with (b:=n) (c:=S n). 2,3:Lia.nia. nia.
Qed.

(* now some more encoding-related properties:*)

Fixpoint nat_unenc (s : term) :=
  match s with
  | lam (lam #1) => Some 0
  | lam (lam (app #0 s)) => match nat_unenc s with Some n => Some (S n) | x=>x end
  | _ => None
  end.

Lemma unenc_correct m : (nat_unenc (nat_enc m)) = Some m.
Proof.
  induction m; simpl; now try rewrite IHm.
Qed.

Lemma unenc_correct2 t n : nat_unenc t = Some n -> nat_enc n = t.
Proof with try solve [Coq.Init.Tactics.easy].
  revert n. eapply (size_induction (f := size) (p := (fun t => forall n, nat_unenc t = Some n -> nat_enc n = t))). clear t. intros t IHt n H.
  destruct t as [ | | t]. easy. easy.
  destruct t as [ | | t]. easy. easy.
  destruct t. 3:easy.
  -destruct n0. easy. destruct n0. 2:easy. inv H. easy.
  -destruct t1. 2-3:easy. destruct n0. 2:easy. simpl in H. destruct (nat_unenc t2) eqn:A.
   +apply IHt in A;simpl;try lia. destruct n. inv H. simpl. congruence.
   +congruence.
Qed.

Lemma dec_enc t : dec (exists n, t = nat_enc n).
Proof.
  destruct (nat_unenc t) eqn:H.
  - left. exists n. now eapply unenc_correct2 in H.
  - right. intros [n A]. rewrite A in H. rewrite unenc_correct in H. inv H.
Qed.

Lemma size_nat_enc (n:nat) :
  size (enc n) = n * 4 + 4.
Proof.
  induction n;cbv [enc registered_nat_enc] in *. all:cbn [size nat_enc] in *. all:solverec.
Qed.

Lemma size_nat_enc_r (n:nat) :
  n <= size (enc n).
Proof.
    induction n;cbv [enc registered_nat_enc] in *. all:cbn [size nat_enc] in *. all:solverec.
Qed.


Instance term_nat_max :
  computableTime' (Nat.max) (fun x _ => (5,fun y _ => (min x y * 15 + 8,tt))).
Proof.
  extract. solverec.
Qed.

(* This is an example for an function in which the run-time of the fix itself is not constant (in add, the fix on the first argument always returns an function in ~5 steps)*)
(* Instance termT_testId : computableTime' (fix f x := *)
(*                                             match x with *)
(*                                               0 => 0 *)
(*                                             | S x => S (f x) *)
(*                                             end). *)
(* Proof. *)
(*   extract. *)
(*   eexists (fun x xT => (x*9+7,tt)). *)
(*   abstract (repeat (cbn;intros;intuition;try destruct _;try ring_simplify)). *)
(* Defined. *)
