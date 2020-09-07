Require Import Equations.Equations Vector.

Derive Signature for Vector.t.

Require Import Undecidability.Shared.Prelim.

From Undecidability Require Import TM.Util.TM_facts.
From Undecidability Require Import Problems.Reduction.
From Undecidability Require Import StringRewriting.Util.singleTM.

(** ** Definition of single-tape Turing Machines  *)
(** Adopted definitions from the formalization of Multitape Turing Machines taken from Asperti, Riciotti "Formalizing Turing Machines" and accompanying Matita foramlisation *)

Require Import ssreflect ssrbool ssrfun.

Section Fix_Sigma.

  Variable sig : finType.

  Global Instance eq_dec_sig: eq_dec sig.
  Proof. exact _. Defined. 

  (* *** Definition of the tape *)
  
  (** A tape is essentially a triple âŒ©left,current,rightâŒª where however the current 
symbol could be missing. This may happen for three different reasons: both tapes 
are empty; we are on the left extremity of a non-empty tape (left overflow), or 
we are on the right extremity of a non-empty tape (right overflow). *)
  
  (* Inductive tape : Type := *)
  (* | niltape : tape *)
  (* | leftof : sig -> list sig -> tape *)
  (* | rightof : sig -> list sig -> tape *)
  (* | midtape : list sig -> sig -> list sig -> tape. *)

  Record tape := mkTape 
    { pos : nat; 
      content: nat -> option sig}.
  (* Notation tape := ({ pos:nat | list sig). *)
  
  (* Global Instance eq_dec_tape: eq_dec tape.
  Proof. 
    unfold EqDec.dec. 
    intros [] [].
    
    repeat decide equality.
         all: eapply eqType_dec.
  Defined. *)
  
  (* Definition tapeToList (t : tape) : list sig :=
    content t. *)
  
  (* Definition sizeOfTape t := |tapeToList t|. *)

  (* (* symbol under head *) *)
  (* Definition current := *)
  (*   fun (t : tape) => *)
  (*     match t with *)
  (*     | midtape _ c _ => Some c *)
  (*     | _ => None *)
  (*     end. *)

  (* (* symbol-list left of head *) *)
  (* Definition left := *)
  (*   fun (t : tape) => *)
  (*     match t with *)
  (*     | niltape _ => [] *)
  (*     | leftof _ _ => [] *)
  (*     | rightof s l => s :: l *)
  (*     | midtape l _ _ => l *)
  (*     end. *)

  (* (* symbol-list right of head *) *)
  (* Definition right := *)
  (*   fun (t : tape) => *)
  (*     match t with *)
  (*     | niltape _ => [] *)
  (*     | leftof s r => s :: r *)
  (*     | rightof _ _ => [] *)
  (*     | midtape _ _ r => r *)
  (*     end. *)

  (* makes a tape from left, current, right *)
  Check singleTM.mk_tape.
   Definition mk_tape (ls:list sig) (c:option sig) (rs:list sig) : tape :=
     mkTape (|ls|) (fun n => nth_error (singleTM.tapeToList(singleTM.mk_tape ls c rs)) n).
    (* refine (mkTape (|ls|) ()).
    move => n.
    (* case: (n < (|ls|)).
    refine (@mkTape (|ls|) (ls ++ [c] ++ rs) _).
    do 2 rewrite app_length;simpl. lia. *)
   Defined. *)

  (* *** Definition of moves *)
  
  (* Inductive move : Type := L : move | R : move | N : move. *)

  Global Instance move_eq_dec : eq_dec move.
  Proof.
    intros. hnf. decide equality.
  Defined.

  Global Instance move_finC : finTypeC (EqType move).
  Proof.
    apply (FinTypeC (enum := [TM.Lmove; TM.Rmove; TM.Nmove])).
    intros []; now cbv.
  Qed.
    
  (* *** Definition of a Sigletape Turing Machine *)

  Record osTM : Type :=
    {
      states : finType; (* states of the TM *)
      trans : states * (option sig) -> states * ((option sig) * move); (* the transition function *)
      start: states; (* the start state *)
      halt : states -> bool (* decidable subset of halting states *)
    }.

  Definition tape_move_right t := 
    match t with 
    | mkTape pos content =>
      mkTape (S pos) content
    end.

  Definition tape_move_left t := 
    match t with 
    | mkTape pos content =>
      mkTape (Nat.pred pos) content
    end.

  Definition tape_move := fun (t : tape) (m : move) =>
                            match m with  Rmove => tape_move_right t | TM.Lmove => tape_move_left t | TM.Nmove => t end.

  Definition update (f:nat->option sig) (pos:nat) (s:sig) (pos':nat) : option sig :=
    if pos =? pos' then Some s else f pos'.

  (* Writing on the tape *)

  Definition tape_write := fun (t : tape) (s : option sig) =>
    match t with 
    | mkTape pos content =>
        match s with
          None => t (* write blank or leave unchanged? *)
        | Some s0 => mkTape pos (update content pos s0)
        end
    end.

  (** A single step of the machine *)
  
  Definition tape_move_mono := fun (t : tape) (mv : option sig * move) =>
                                 tape_move (tape_write t (fst mv)) (snd mv).


  (* *** Configurations of TM *)
  
  Record mconfig (states:finType) : Type :=
    mk_mconfig
      {
        cstate : states;
        ctape : tape
      }.

  (* Instance eq_dec_conf (s: finType): eq_dec (mconfig s).
  Proof. intros x y. destruct x,y.
         decide (cstate0 = cstate1); decide (ctape0 = ctape1);
           try (right; intros H; now inversion H). left. now subst.
  Qed.   *)


  (* *** Machine execution *)

  Definition current t :=
    content t (pos t).

  Definition step :=
    fun (M:osTM) (c:mconfig (states M)) => 
      let (news,action) := trans (cstate c, current (ctape c))
      in mk_mconfig news (tape_move_mono (ctape c) action).

  (* Initial configuration *)  
  Definition initc := fun (M : osTM) tape =>
                        mk_mconfig (@start M) tape.
    
  (* Run the machine i steps until it halts *)
  (* Returns None iff the maschine does not halt within i steps *)
  (* Definition loop (A:Type) := fix l n (f:A -> A) (p : A -> bool) a {struct n}:= *)
  (*                             if p a then Some a  else *)
  (*                               match n with *)
  (*                                 O => None *)
  (*                               | S m => l m f p (f a) *)
  (*                               end. *)

  
  Definition loopM := fun (M :osTM) (i : nat) cin =>
                        loop (@step M) (fun c => halt (cstate c)) cin i. 


  
  (* *** Definition of Reachability *)

  Definition TMterminates (M: osTM) (start: mconfig (states M)) :=
    exists i outc, loopM i start = Some outc.

  Lemma loop_step_not A f p (a : A) i out:
    loop f p (f a) i = out -> (p a = false) -> (loop f p a (S i) = out). 
  Proof.
  destruct i; intros H HF; cbn in *; rewrite HF; destruct (p (f a)); assumption.   
  Qed.

  Inductive reach (M: osTM) : mconfig (states M) ->  mconfig (states M) -> Prop :=
  |reachI c : reach c c
  |reachS c d: reach (step c) d -> (halt (cstate c) = false) -> reach c d.
  Hint Constructors reach : core.

 
  Definition Halt' (M: osTM) (start: mconfig (states M)) :=
    exists (f: mconfig (states M)), halt (cstate f)=true /\ reach start f.

  Lemma TM_terminates_Halt (M:osTM) (start: mconfig (states M)) :
    TMterminates start <-> Halt' start.
  Proof.
    split.
    - intros [i [fin H]]. revert H. revert start. induction i; intros start H; cbn in *.
      + exists start. destruct (halt (cstate start)) eqn: HS. split; auto. inv H.
      + destruct (halt (cstate start)) eqn: HS.
        * inv H. exists fin. now split.  
        * destruct (IHi (step start)) as [q [HF RF]]. unfold loopM. assumption.
          exists q. split. assumption. now apply reachS. 
    - intros [f [HF RF]]. revert HF. induction RF; intros HR. 
      + exists 0, c. cbn. now rewrite HR.
      + destruct (IHRF HR) as [i [out LH]]. exists (S i), out. now apply loop_step_not. 
  Qed.
 
End Fix_Sigma.

Definition Halt (S: {sig:finType & osTM sig & tape sig}) :=
  Halt' (initc (projT2 (sigT_of_sigT2 S)) (projT3 S)).

Definition Reach (S: (sigT (fun (sig:finType) =>
                              (sigT (fun (M:osTM sig) => prod (mconfig sig (states M))
                                                          (mconfig sig (states M))))))) :=
  let (c1,c2) := (projT2 (projT2 S)) in
  reach c1 c2. 
     

Definition single_TM_halt : { sig : finType & (TM sig 1) * (tapes sig 1)}%type -> Prop :=
  fun '(existT _ sig (M, t)) => exists outc k, TM_facts.loopM (TM_facts.initc M t) k = Some outc.

(* Equations (noeqns) f_config A B : TM_facts.mconfig A B 1 -> mconfig A B :=
  { f_config (TM_facts.mk_mconfig a [|b|]) := mk_mconfig a b }. *)

(* From Undecidability Require Import TM.Util.Prelim TM.Util.TM_facts. *)
