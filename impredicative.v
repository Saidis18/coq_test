(* Ex 6.12 *)
Definition my_False : Prop := forall P : Prop, P.
Definition my_not (P : Prop) : Prop := P -> my_False.

Theorem my_False_ind : forall P : Prop, my_False -> P.
Proof.
    intros P f.
    apply f.
Qed.

Theorem th6_12_1 : my_not my_False.
Proof.
    unfold my_not.
    unfold my_False.
    intros H P.
    apply H.
Qed.

Theorem th6_12_2 : forall P : Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
    unfold my_not.
    intros P H0 p.
    apply H0.
    intros H1.
    apply H1.
    assumption.
Qed.

Theorem th6_12_3 : forall P Q : Prop, (P -> Q) ->  my_not Q -> my_not P.
Proof.
    intros P Q H nq p.
    apply nq.
    apply H.
    assumption.
Qed.

Theorem th6_12_4 : forall P Q R : Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
    intros P Q R H0 H1 p.
    apply my_False_ind.
    apply H1.
    assumption.
    apply H0.
    assumption.
Qed.

(* Ex 6.13 *)
Require Import Relations.
Section leibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Variable A : Set.
Definition leibniz (a b : A) : Prop := forall P : A -> Prop, P a -> P b.

Theorem leibniz_sym : symmetric A leibniz.
Proof.
    unfold symmetric.
    intros a b.
    unfold leibniz.
    intros H0 Q.
    apply H0.
    trivial.
Qed.

Theorem leibniz_refl : reflexive A leibniz.
Proof.
    unfold reflexive.
    intros a.
    unfold leibniz.
    intros P pa.
    assumption.
Qed.

Theorem leibniz_trans : transitive A leibniz.
Proof.
    unfold transitive.
    intros a b c.
    intros H0 H1.
    unfold leibniz.
    intros P pa.
    apply H1.
    apply H0.
    assumption.
Qed.

Theorem leibniz_equiv : equiv A leibniz.
Proof.
    unfold equiv.
    repeat split.
    apply leibniz_refl.
    apply leibniz_trans.
    apply leibniz_sym.
Qed.

Theorem leibniz_least_reflexive : forall R : relation A, reflexive A R -> inclusion A leibniz R.
Proof.
    unfold relation.
    unfold reflexive.
    unfold inclusion.
    intros R.
    intros refl a b.
    unfold leibniz.
    intros leib.
    apply (leib (fun u => R a u)).
    apply refl.
Qed.

Theorem leibniz_eq : forall a b : A, leibniz a b -> a = b.
Proof.
    apply leibniz_least_reflexive.
    unfold reflexive.
    intros a.
    apply eq_refl.
Qed.

Theorem eq_leibniz : forall a b : A, a = b -> leibniz a b.
Proof.
    intros a b eq_ab.
    rewrite eq_ab.
    apply leibniz_refl.
Qed.

Theorem leibniz_ind : forall (a : A) (P : A -> Prop), P a -> forall b : A, leibniz a b -> P b.
Proof.
    unfold leibniz.
    intros a Q qa b H.
    apply H.
    assumption.
Qed.

Unset Implicit Arguments.
End leibniz.

(* Ex 6.14 *)
Definition my_and (P Q : Prop) := forall R : Prop, (P -> Q -> R) -> R.
Definition my_or (P Q : Prop) := forall R : Prop, (P -> R) -> (Q -> R) -> R.
Definition my_ex (A : Set) (P : A -> Prop) := forall R : Prop, (forall x : A, P x -> R) -> R.

Theorem th1 : forall P Q : Prop, my_and P Q -> P.
Proof.
    unfold my_and.
    intros PP QQ H.
    apply (H PP).
    intros p q.
    assumption.
Qed.

Theorem th2 : forall P Q : Prop, my_and P Q -> Q.
Proof.
    unfold my_and.
    intros PQ QQ H.
    apply (H QQ).
    intros p q.
    assumption.
Qed.

Theorem th3 : forall P Q R : Prop, (P -> Q -> R) -> my_and P Q -> R.
Proof.
    unfold my_and.
    intros PP Q RR H0 H1.
    apply (H1 RR).
    assumption.
Qed.

Theorem th4 : forall P Q : Prop, P -> my_or P Q.
Proof.
    unfold my_or.
    intros PP QQ p R H0 H1.
    apply H0.
    assumption.
Qed.

Theorem th5 : forall P Q : Prop, Q -> my_or P Q.
Proof.
    unfold my_or.
    intros PP QQ q R H0 H1.
    apply H1.
    assumption.
Qed.

Theorem th6 : forall P Q R : Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.
Proof.
    unfold my_or.
    intros PP QQ RR H0 H1 H2.
    apply (H2 RR); assumption.
Qed.

Theorem th7 : forall P : Prop, my_or P my_False -> P.
Proof.
    unfold my_or.
    intros PP H.
    apply (H PP).
    trivial.
    apply my_False_ind.
Qed.

Theorem th8 : forall P Q : Prop, my_or P Q -> my_or Q P.
Proof.
    unfold my_or.
    intros PP QQ H RR H0 H1.
    apply (H RR); assumption.
Qed.

Theorem th9 : forall (A : Set) (P : A -> Prop) (a : A), P a -> my_ex A P.
Proof.
    unfold my_ex.
    intros A P a Pa R H.
    apply H with (x := a).
    assumption.
Qed.

Theorem th10 : forall (A : Set) (P: A -> Prop), my_not (my_ex A P) -> forall a : A, my_not (P a).
Proof.
    intros A P.
    unfold my_not.
    unfold my_ex.
    intros H a Pa.
    apply (H (fun R g => g a Pa)).
Qed.

(* Ex 6.15 *)
Definition my_le (n p : nat) := forall P : nat -> Prop, P n -> (forall q : nat, P q -> P (S q)) -> P p.

Lemma my_le_n : forall n : nat, my_le n n.
Proof.
    unfold my_le.
    intros n P Pn H.
    assumption.
Qed.

Lemma my_le_S : forall n : nat, my_le n (S n).
Proof.
    unfold my_le.
    intros n P Pn H.
    apply H.
    assumption.
Qed.

Lemma my_le_le : forall n p : nat, my_le n p -> n <= p.
Proof.
    unfold my_le.
    intros n p H.
    apply (H (fun q => n <= q) (le_n n) (fun q Pq => le_S n q Pq)).
Qed.
