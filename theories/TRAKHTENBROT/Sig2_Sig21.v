(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Notation ø := vec_nil.
Local Notation Σ2 := (Σrel 2).

Definition Σ21 : fo_signature.
Proof.
  exists unit unit.
  + exact (fun _ => 2).
  + exact (fun _ => 1).
Defined.

Local Definition P21 (x y : nat) := @fol_atom Σ21 tt ((@in_fot  _ (ar_syms Σ21) tt (£x##£y##ø))##ø).

Section Σ2_Σ21_model.

  Fixpoint Σ2_Σ21 (d : nat) (A : fol_form Σ2) : fol_form Σ21 :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => P21 (Σrel_var (vec_head v)) (Σrel_var (vec_head (vec_tail v))) 
      | fol_bin b A B  => fol_bin b (Σ2_Σ21 d A) (Σ2_Σ21 d B)
      | fol_quant fol_fa A  => ∀ P21 (S d) 0 ⤑ Σ2_Σ21 (S d) A
      | fol_quant fol_ex A  => ∃ P21 (S d) 0 ⟑ Σ2_Σ21 (S d) A
    end.

  Variable (X : Type) (M2  : fo_model Σ2 X).
  Variable (Y : Type) (M21 : fo_model Σ21 Y).

  Let Q x1 x2 := fom_rels M2 tt (x1##x2##ø).
  Let f y1 y2 := fom_syms M21 tt (y1##y2##ø).
  Let P y := fom_rels M21 tt (y##ø).

  Variable R : X -> Y -> Prop.

  Variable (d : nat) (φ : nat -> X) (ψ : nat -> Y)
           (H1 : forall x1 x2 y1 y2, R x1 y1 -> R x2 y2 -> Q x1 x2 <-> P (f y1 y2))
           (H2 : forall x, exists y, R x y /\ P (f (ψ d) y))
           (H3 : forall y, P (f (ψ d) y) -> exists x, R x y).

  Theorem Σ2_Σ21_correct A : 
           (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> fol_sem M2 φ A <-> fol_sem M21 ψ (Σ2_Σ21 d A).
  Proof.
    revert d φ ψ H2 H3.
    induction A as [ | [] v | b A HA B HB | [] A HA ];
      intros d φ ψ H2 H3 H.
    + simpl; tauto.
    + simpl in v; revert H.
      vec split v with x1; vec split v with x2; vec nil v; clear v.
      revert x1 x2; intros [ x1 | [] ] [ x2 | [] ] H; simpl in H |- *.
      apply H1; apply H; auto.
    + simpl; apply (fol_bin_sem_ext _).
      * apply HA; auto; intros; apply H, in_app_iff; auto.
      * apply HB; auto; intros; apply H, in_app_iff; auto.
    + simpl; split.
      * intros (x & Hx).
        destruct (H2 x) as (y & Hy1 & Hy2).
        exists y; split; auto.
        revert Hx; apply HA; simpl; auto.
        intros [|i] Hi; simpl; auto.
        apply H; simpl; apply in_flat_map.
        exists (S i); simpl; auto.
      * intros (y & G1 & G2).
        destruct (H3 _ G1) as (x & Hx).
        exists x; revert G2; apply HA; simpl; auto.
        intros [|i] Hi; simpl; auto.
        apply H; simpl; apply in_flat_map.
        exists (S i); simpl; auto.
    + simpl; split.
      * intros G y Hy.
        destruct (H3 _ Hy) as (x & Hx).
        generalize (G x); apply HA; simpl; auto.
        intros [|i] Hi; simpl; auto.
        apply H; simpl; apply in_flat_map.
        exists (S i); simpl; auto.
      * intros G x.
        destruct (H2 x) as (y & Hy1 & Hy2).
        generalize (G _ Hy2); apply HA; simpl; auto.
        intros [|i] Hi; simpl; auto.
        apply H; simpl; apply in_flat_map.
        exists (S i); simpl; auto.
  Qed.

End Σ2_Σ21_model.

Section Σ2_Σ21_enc.

  Variable (A : fol_form Σ2).

  Let d := S (lmax (fol_vars A)).

  Definition Σ2_Σ21_enc := fol_lconj (map (P21 d) (fol_vars A))
                         ⟑ P21 d 0
                         ⟑ Σ2_Σ21 d A.

End Σ2_Σ21_enc.

Section Σ2_Σ21_enc_sound.

  Variable (A : fol_form Σ2) (X : Type) (M2 : fo_model Σ2 X) (φ : nat -> X)
           (HA : fol_sem M2 φ A).

  Let Y := (bool + X + X*X)%type.

  Let i := S (lmax (fol_vars A)).

  Let d : Y := inl (inl true).

  Let M21 : fo_model Σ21 Y.
  Proof.
    split.
    + simpl; intros _ v.
      exact (match (vec_head v), (vec_head (vec_tail v)) with
        | inl (inl true), inl (inr x)  => inl (inr x)
        | inl (inr x1),   inl (inr x2) => inr (x1,x2)
        | _           ,   _            => inl (inl false)
      end).
    + simpl; intros _ v.
      exact (match vec_head v with
        | inl (inr _) => True
        | inr (x1,x2) => fom_rels M2 tt (x1##x2##ø)
        | _           => False
      end).
  Defined.

  Let ψ n : Y := 
    if eq_nat_dec i n then d else inl (inr (φ n)).

  Let phi_i : ψ i = d.
  Proof.
    unfold ψ.
    destruct (eq_nat_dec i i) as [ | [] ]; auto.
  Qed.

  Let phi_x n : In n (fol_vars A) -> ψ n = inl (inr (φ n)).
  Proof.
    intros H.
    assert (D : lmax (fol_vars A) < i).
    { apply le_refl. }
    unfold ψ.
    destruct (eq_nat_dec i n); auto.
    apply lmax_prop in H; lia.
  Qed.

  Let R x (y : Y) := y = inl (inr x).

  Let sem_Σ2_Σ21_enc : fol_sem M21 ψ (Σ2_Σ21_enc A).
  Proof.
    simpl; msplit 2.
    - rewrite fol_sem_lconj; intros ?; rewrite in_map_iff.
      intros (n & <- & Hn); simpl.
      fold i; rewrite phi_i; simpl.
      rewrite phi_x; auto.
    - fold i; rewrite phi_i; simpl; auto.
    - revert HA; apply Σ2_Σ21_correct with (R := R).
      + intros x1 x2 y1 y2; unfold R; simpl; intros -> ->; tauto.
      + intros x; exists (inl (inr x)); split.
        * red; auto.
        * fold i; rewrite phi_i; unfold d; simpl; auto.
      + fold i; rewrite phi_i; intros [ [ [] | x ] | (x1,x2) ]; simpl; try tauto.
        exists x; red; auto.
      + intros n Hn; rewrite (phi_x _ Hn); red; auto.
  Qed.

  Hypothesis (HX : finite_t X)
             (M2_dec : fo_model_dec M2).

  Hint Resolve finite_t_sum finite_t_bool finite_t_prod.

  Theorem Σ2_Σ21_enc_sound : fo_form_fin_dec_SAT (Σ2_Σ21_enc A).
  Proof.
    exists Y, M21.
    exists. { unfold Y; auto. }
    exists.
    { intros []; simpl; intros v.
      vec split v with x; vec nil v; clear v; simpl.
      destruct x as [ [ [] | x ] | (x1,x2) ]; try tauto.
      apply M2_dec. }
    exists ψ; auto.
  Qed.

End Σ2_Σ21_enc_sound.

Section Σ2_Σ21_enc_complete.
 
  Variable (A : fol_form Σ2) (Y : Type) (M21 : fo_model Σ21 Y)
           (M21_dec : fo_model_dec M21) (ψ : nat -> Y).

  Let i := S (lmax (fol_vars A)).
  Let d := ψ i.

  Let f u v := fom_syms M21 tt (u##v##ø).

  Let P y := fom_rels M21 tt (f d y##ø).
          
  Hypothesis (HA : fol_sem M21 ψ (Σ2_Σ21_enc A)).

  Let Q y := (if @M21_dec tt (f d y##ø) then true else false) = true.

  Let Q_spec y : Q y <-> P y.
  Proof.
    unfold P, Q.
    destruct (M21_dec (f d y##ø)); split; auto; discriminate.
  Qed.

  Let H1 n : In n (fol_vars A) -> Q (ψ n).
  Proof.
    intros Hn; apply Q_spec.
    simpl in HA; apply proj1 in HA.
    rewrite fol_sem_lconj in HA.
    unfold P.
    apply (HA (P21 i n)), in_map_iff.
    exists n; split; auto.
  Qed.

  Let H2 : Q (ψ 0).
  Proof. apply Q_spec, HA. Qed.

  Let H3 : fol_sem M21 ψ (Σ2_Σ21 i A).
  Proof. apply HA. Qed.

  Let X := sig Q.

  Let M2 : fo_model Σ2 X.
  Proof.
    split.
    + intros [].
    + intros r; simpl; intros v.
      exact (fom_rels M21 tt (f (proj1_sig (vec_head v)) (proj1_sig (vec_head (vec_tail v)))##ø)).
  Defined.

  Let φ n : X :=
    match in_dec eq_nat_dec n (fol_vars A) with
      | left H  => exist _ _ (H1 n H)
      | right _ => exist _ _ H2
    end.

  Let R (x : X) (y : Y) := proj1_sig x = y.

  Let sem_A : fol_sem M2 φ A.
  Proof.
    revert H3; apply Σ2_Σ21_correct with (R := R).
    + intros (x1 & E1) (x2 & E2) y1 y2; unfold R; simpl.
      intros <- <-; tauto.
    + intros (x & Hx); exists x; split.
      * red; simpl; auto.
      * apply Q_spec in Hx; auto.
    + intros y Hy; apply Q_spec in Hy.
      exists (exist _ y Hy); red; auto.
    + intros n Hn; unfold φ.
      destruct (in_dec eq_nat_dec n (fol_vars A)) as [ | [] ]; auto.
      red; simpl; auto.
  Qed.

  Hypothesis HY : finite_t Y.

  Theorem Σ2_Σ21_enc_complete : fo_form_fin_dec_SAT A.
  Proof.
    exists X, M2.
    exists. 
    { unfold X; apply fin_t_finite_t.
      + intros; apply eq_bool_pirr.
      + unfold Q; apply finite_t_fin_t_dec; auto.
        intros; apply bool_dec. }
    exists.
    { intros [] v; simpl; apply M21_dec. }
    exists φ; auto. 
  Qed.

End Σ2_Σ21_enc_complete.


  
    
    
      


