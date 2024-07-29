Require Import Coq.Classes.Morphisms.
(* Require Import Coq.Classes.RelationClasses. *)
Require Import Coq.setoid_ring.Ncring.
Require Import Coq.setoid_ring.Ncring_tac.
Require Import Setoid.
Set Implicit Arguments.

Class InvRing_ops (R:Type) := {
    inv: R->R;
}.

Notation "$ x" := (inv x) (at level 1).
Search ring_plus_comp.
Class InvRing (R:Type)`{Ring R}`{InvRing_ops R} := {
    ir_inv_comp : forall x y, (x==y) -> $x==$y;
    ir_inv_idem : forall x, $ ($ x) == x;
    ir_inv_add  : forall x y, $ (x + y) == $ x + $ y;
    ir_inv_mult : forall x y, $ (x * y) == $ y * $ x;
}.

Theorem refl : forall (R:Type)`{InvRing R},
    forall (x: R), $x == $x.
Proof. intros. apply ir_inv_comp. non_commutative_ring. Qed.

Theorem trivial_inv_ring : forall (R:Type)`{Ring R}`{InvRing_ops R},
    (forall x y, (x==y) -> $x==$y) ->
    (forall x y, x * y == y * x) -> (forall x, inv x == x) -> InvRing.
Proof with eauto.
    constructor.
    - unfold Proper, respectful. intros. apply H1. assumption.
    - intros. rewrite H3, H3. reflexivity.
    - intros. rewrite H3, H3, H3. reflexivity.
    - intros. rewrite H3, H3, H3. apply H2.
Qed.

Instance complex_ring_ops (R:Type)`{Ring_ops R} : @Ring_ops
        (R * R)
        (0, 0) (1, 0)
        (fun p q => (fst p + fst q, snd p + snd q))
        (fun p q => (fst p * fst q - snd p * snd q,
                     fst p * snd q + snd p * fst q))
        (fun p q => (fst p - fst q, snd p - snd q))
        (fun p => (- fst p, - snd p))
        (fun p q => (fst p == fst q) /\ (snd p == snd q))
        .
    Qed.

Lemma complex_ring (R:Type)`{Ring R} : Ring (T := R * R).
Proof with eauto.
    constructor; simpl...
    - constructor; constructor; repeat non_commutative_ring.
        + symmetry. apply H0.
        + symmetry. apply H0.
        + transitivity (fst y). apply H0. apply H1.
        + transitivity (snd y). apply H0. apply H1.
    - constructor; simpl; apply ring_plus_comp.
      apply H0. apply H1.
      apply H0. apply H1.
    - constructor; simpl.
      apply ring_sub_comp.
      apply ring_mult_comp. apply H0. apply H1.
      apply ring_mult_comp. apply H0. apply H1.
      apply ring_plus_comp.
      apply ring_mult_comp. apply H0. apply H1.
      apply ring_mult_comp. apply H0. apply H1.
    - constructor; simpl; apply ring_sub_comp.
      apply H0. apply H1.
      apply H0. apply H1.
    - constructor; simpl; apply ring_opp_comp; apply H0.
    - intros [a b] . unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring. 
    - intros [a b] [a' b']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring. 
    - intros [a b] [a' b'] [a'' b'']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b]. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b]. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b] [a' b'] [a'' b'']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b] [a' b'] [a'' b'']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b] [a' b'] [a'' b'']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b] [a' b']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring. 
    - intros [a b]. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
  Qed.

Instance complex_inv_ring_ops (R:Type)`{Ring_ops R} : @InvRing_ops (R * R) := {
    inv := fun p => (fst p, - snd p)
}.

Theorem complex_inv_ring (R:Type)`{Ring R}
    : (forall x y, x * y == y * x)
            -> InvRing (R := R * R) (H := complex_ring).
Proof with eauto.
    constructor; simpl...
    - unfold Proper, respectful. intros. unfold "==". unfold eq_notation. simpl.
      split. apply H1. apply ring_opp_comp. apply H1.
    - intros [a b]. simpl. 
      unfold "==". unfold eq_notation. split; simpl; non_commutative_ring.
    - intros [a b] [a' b']. unfold "==". unfold eq_notation.
      split; simpl; non_commutative_ring.
    - intros [a b] [a' b']. unfold "==". unfold eq_notation.
      split; simpl. apply ring_sub_comp.
      apply H0. transitivity (b' * b). apply H0. non_commutative_ring.
      assert ((- (a * b' + b * a')) == (a' * - b + - b' * a)).
      transitivity (- (b' * a + a' * b)).
      { - apply ring_opp_comp. apply ring_plus_comp. apply H0. apply H0.  }
      { - non_commutative_ring. }
      apply H1.
  Qed.

Instance matrix_ring_ops (R:Type)`{Ring R} : @Ring_ops ((R * R) * (R * R))
        ((0, 0), (0, 0))
        ((1, 0), (0, 1))
        (fun m n =>
            match m, n with
            | ((a, b), (c, d)), ((e, f), (g, h)) =>
                ((a + e, b + f), (c + g, d + h))
            end)
        (fun m n =>
            match m, n with
            | ((a, b), (c, d)), ((e, f), (g, h)) =>
                ((a * e + b * g, a * f + b * h),
                 (c * e + d * g, c * f + d * h))
            end)
        (fun m n =>
            match m, n with
            | ((a, b), (c, d)), ((e, f), (g, h)) =>
                ((a - e, b - f), (c - g, d - h))
            end)
        (fun m => 
            match m with
            | ((a, b), (c, d)) => ((- a, - b), (- c, - d))
            end)
        (fun m n => (fst (fst m) == fst (fst n) /\ snd (fst m) == snd (fst n)
                    /\ fst (snd m) == fst (snd n) /\ snd (snd m) == snd (snd n)))
    .
Qed.

Instance matrix_ring (R:Type)`{Ring R} : @Ring _ _ _ _ _ _ _ _ matrix_ring_ops.
Proof with eauto.
    constructor; simpl.
    - constructor.
      repeat constructor; reflexivity.
      unfold Symmetric. 
      intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] H0.
      destruct H0. destruct H1. destruct H2. simpl in *.
      repeat constructor; simpl; symmetry; assumption. 
      unfold Transitive.
      intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] [[z00 z01] [z10 z11]] H0 H4.
      destruct H0. destruct H1. destruct H2.
      destruct H4. destruct H5. destruct H6.
      simpl in *.
      repeat constructor; simpl.
      transitivity y00; assumption.
      transitivity y01; assumption.
      transitivity y10; assumption.
      transitivity y11; assumption.
    - unfold Proper, respectful.
      intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] H0.
      destruct H0. destruct H1. destruct H2.
      intros [[x00' x01'] [x10' x11']] [[y00' y01'] [y10' y11']] H4.
      destruct H4. destruct H5. destruct H6. simpl in *.
      unfold "=="; unfold eq_notation; repeat split; simpl; apply ring_plus_comp...
    - unfold Proper, respectful.
      intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] H0.
      intros [[x00' x01'] [x10' x11']] [[y00' y01'] [y10' y11']] H0'.
      unfold "==" in H0. unfold eq_notation in H0. simpl in H0.
      destruct H0.  destruct H1.  destruct H2.
      unfold "==" in H0'. unfold eq_notation in H0'. simpl in H0'.
      destruct H0' as [H0' H1'].  destruct H1' as [H1' H2'].  destruct H2' as [H2' H3'].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; apply ring_plus_comp; apply ring_mult_comp...
    - unfold Proper, respectful.
      intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] H0.
      intros [[x00' x01'] [x10' x11']] [[y00' y01'] [y10' y11']] H0'.
      unfold "==" in H0. unfold eq_notation in H0. simpl in H0.
      destruct H0.  destruct H1.  destruct H2.
      unfold "==" in H0'. unfold eq_notation in H0'. simpl in H0'.
      destruct H0' as [H0' H1'].  destruct H1' as [H1' H2'].  destruct H2' as [H2' H3'].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; apply ring_sub_comp...
    - unfold Proper, respectful.
      intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] H0.
      unfold "==" in H0. unfold eq_notation in H0. simpl in H0.
      destruct H0.  destruct H1.  destruct H2.
      unfold "=="; unfold eq_notation; simpl.
      repeat split; apply ring_opp_comp...
    - intros [[x00 x01] [x10 x11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] [[z00 z01] [z10 z11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] [[z00 z01] [z10 z11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] [[z00 z01] [z10 z11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]] [[z00 z01] [z10 z11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]] [[y00 y01] [y10 y11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
    - intros [[x00 x01] [x10 x11]].
      unfold "=="; unfold eq_notation; simpl.
      repeat split; non_commutative_ring...
  Qed.

Instance matrix_inv_ring_ops (R:Type)`{InvRing_ops R} : @InvRing_ops ((R * R) * (R * R)) := {
    inv := fun m => match m with
                    | ((a, b), (c, d)) => (($a, $c), ($b, $d))
                    end
}.

Instance matrix_inv_ring (R:Type)`{Ring R}`{InvRing R}
        : @InvRing _ _ _ _ _ _ _ _ _ matrix_ring matrix_inv_ring_ops.
Proof with eauto.
    constructor.
    - unfold Proper, respectful.
      intros [[a b] [c d]] [[a' b'] [c' d']] H3. unfold "==". unfold eq_notation.
      destruct H3. destruct H4. destruct H5. simpl in *. 
      repeat split; simpl; apply ir_inv_comp; assumption.
    - intros [[a b] [c d]]. simpl. 
      unfold "==". unfold eq_notation. repeat split; simpl; apply ir_inv_idem.
    - intros [[a b] [c d]] [[a' b'] [c' d']]. unfold "==". unfold eq_notation.
      simpl. repeat split; simpl; apply ir_inv_add.
    - intros [[a b] [c d]] [[a' b'] [c' d']]. unfold "==". unfold eq_notation.
      simpl. repeat split; simpl; eapply transitivity.
      + apply ir_inv_add.
      + apply ring_plus_comp; apply ir_inv_mult.
      + apply ir_inv_add.
      + apply ring_plus_comp; apply ir_inv_mult.
      + apply ir_inv_add.
      + apply ring_plus_comp; apply ir_inv_mult.
      + apply ir_inv_add.
      + apply ring_plus_comp; apply ir_inv_mult.
      Unshelve. all: apply ring_setoid.
  Qed.

Lemma inv_injective (R:Type)`{InvRing R} : forall x y, $x == $y <-> x == y.
Proof.
    split.
    transitivity ($($x)).
    - symmetry. apply ir_inv_idem.
    - transitivity ($($y)).
        + apply ir_inv_comp. apply H2.
        + apply ir_inv_idem.
    - intros. apply ir_inv_comp. assumption.
    Qed.

Definition unitary (R:Type)`{InvRing R} (u:R) : Prop := ($u * u == 1) /\ (u * $u == 1).

Proposition id_inv (R:Type)`{InvRing R} : $1 == 1.
Proof.
    transitivity (1 * $1). 
    - non_commutative_ring.
    - transitivity ($(1 * $1)).
        + transitivity ($($1) * $1).
            * apply ring_mult_comp. symmetry. apply ir_inv_idem. reflexivity.
            * symmetry. apply ir_inv_mult.
        + transitivity ($$1).
            * eapply inv_injective. apply H1. non_commutative_ring.
            * apply ir_inv_idem.
Qed.

Proposition id_unitary (R:Type)`{InvRing R} : unitary 1.
Proof.
    unfold unitary. split.
    transitivity ($1). non_commutative_ring. apply id_inv. 
    transitivity ($1). non_commutative_ring. apply id_inv. 
Qed.

Proposition inv_unitary (R:Type)`{InvRing R} : forall u:R, unitary u -> unitary ($u).
Proof.
    intros. unfold unitary in *. destruct H2. split.
    transitivity ($(u * $u)). symmetry. apply ir_inv_mult.
    transitivity ($1). apply ir_inv_comp. apply H3. eapply id_inv.
    transitivity ($($u * u)). symmetry. apply ir_inv_mult.
    transitivity ($1). apply ir_inv_comp. apply H2. eapply id_inv.
Qed.


