Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Setoid.
Set Implicit Arguments.

(* Reserved Notation "$ x" (at level 1). *)

Section MakeInvRing.

(* elements : R *)

Variable R : Type.
Declare Scope R_scope.
Bind Scope R_scope with R.
Delimit Scope R_scope with ring.
Local Open Scope R_scope.

Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
Variable inv : R -> R.
Variable req : R -> R -> Prop.

Notation "0" := rO : R_scope.
Notation "1" := rI : R_scope.
Infix "+" := radd : R_scope.
Infix "-" := rsub : R_scope.
Infix "*" := rmul : R_scope.
Notation "- x" := (ropp x) : R_scope.
Notation "$ x" := (inv x) (at level 1) : R_scope.
Infix "==" := req (at level 70, no associativity) : R_scope.

(* Equality properties *)
Variable Rsth : Setoid_Theory R req.
Variable Reqe : ring_eq_ext radd rmul ropp req.
Variable Inv_ext : forall p q, p == q ->  $ p == $ q.

(* Properties *)
Record involutive_ring_theory : Prop := mk_inv_ring {
    I_ring: ring_theory 0 1 radd rmul rsub ropp req;
    I_idempotent : forall x, $ ($ x) == x;
    I_add: forall x y, $ (x + y) == $ x + $ y;
    I_mult: forall x y, $ (x * y) == $ y * $ x;
}.

Section InvRing.
Variable IRth : involutive_ring_theory.
Let Rth := I_ring IRth.
Let rIdem := I_idempotent IRth.
Let rAdd := I_add IRth.
Let rMult := I_mult IRth.

Add Morphism radd with signature (req ==> req ==> req) as radd_ext.
Proof. exact (Radd_ext Reqe). Qed.
Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext.
Proof. exact (Rmul_ext Reqe). Qed.
Add Morphism ropp with signature (req ==> req) as ropp_ext.
Proof. exact (Ropp_ext Reqe). Qed.
Add Morphism inv with signature (req ==> req) as inv_ext.
Proof. exact Inv_ext. Qed.

Variable IRsth : Setoid_Theory R req.
    Add Parametric Relation : R req
        reflexivity  proved by (@Equivalence_Reflexive _ _ Rsth)
        symmetry     proved by (@Equivalence_Symmetric _ _ Rsth)
        transitivity proved by (@Equivalence_Transitive _ _ Rsth)
    as R_setoid3.
(* add abstract semi-ring to help with some proofs *)

End InvRing.

End MakeInvRing.