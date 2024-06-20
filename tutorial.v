Require Import ZArith.
Open Scope Z_scope.
Parameter max_int : Z.
Locate " _ - _ ".
Definition min_int := 1 - max_int.
Print min_int.
Definition cube z := z * z * z.
Print cube.
Check (cube 2).
Open Scope nat_scope.
Check (cube 1).
(* Argument is interpreted in Z_scope even though the current scope is nat_scope *)

Section binomial_def.
    Variables a b : Z. (* Local declaration *)
    Parameter x : Z. (* Global declaration *)
    Open Scope Z_scope.
    Definition binomial z := a * z + b.
    (* You can now prove things about binomial *)
    Print binomial.
    Section trinomial_def.
        Variable c : Z.
        Definition trinomial z := (binomial z) * z + c.
    End trinomial_def.
End binomial_def.
Check x.
Print binomial.
(* You can now use binomial as a parametric function that has already some theorems proven *)


Definition compose : forall {A B C : Set}, (A -> B) -> (B -> C) -> (A -> C) := fun A B C f g x => g (f x).
Check (compose (A := nat) S (plus 78)).


(* Ex 3.6 *)
Section no_abstractions.
    Variables a b c d e : nat.
    Definition sum := a + b + c + d + e.
End no_abstractions.
Print sum.

(* Ex 3.7 *)
Open Scope Z_scope.
Print Scope Z_scope.
Check Zplus.
Check Zmult.
Definition poly z := Zplus (Zmult 2%Z (Zmult z z)) (Zplus (Zmult 3 z) 3).
Eval compute in poly 2.
Check (poly 2).
Eval cbv delta in poly 2.
Eval cbv delta [poly] in poly 2.
Eval cbv beta delta [poly] in poly 2.
Eval cbv beta zeta delta [poly] in poly 2.
Eval cbv iota beta zeta delta [poly] in poly 2.

Open Scope nat_scope.
Theorem less : 36 <= 38.
Proof le_S _ _ (le_S _ _ (le_n 36)).

(* Ex 5.4 *)
Theorem id : forall (A : Set), A -> A.
Proof fun A => fun x : A => x.

Theorem diag : forall A B : Set, (A -> A -> B) -> A -> B.
Proof fun A B => fun f x => f x x.

Theorem permute : forall A B C : Set, (A -> B -> C) -> B -> A -> C.
Proof fun A B C => fun f b a => f a b.

Theorem f_nat_Z : forall A : Set, (nat -> A) -> Z -> A.
Proof fun A f n => f (Z.to_nat n).

(* Ex 5.5 *)
Theorem all_perm : forall (A : Type) (P : A -> A -> Prop), (forall x y : A, P x y) -> forall x y : A, P y x.
Proof fun A P => fun (f : forall x y : A, P x y) => (fun y x => f x y).
Print all_perm.

Theorem resolution : forall (A : Type) (P Q R H : A -> Prop), (forall a : A, Q a -> R a -> H a) -> (forall b : A, P b -> Q b) -> (forall c : A, P c -> R c -> H c).
Proof fun _ _ _ _ _ f g c pc => f c (g c pc).
Print resolution.

(* Ex. 6.2 *)
Theorem all_perm' : forall (A : Type) (P : A -> A -> Prop), (forall x y : A, P x y) -> forall x y : A, P y x.
Proof.
    intros A P H x y.
    apply H.
Qed.

Theorem resolution' : forall (A : Type) (P Q R H : A -> Prop), (forall a : A, Q a -> R a -> H a) -> (forall b : A, P b -> Q b) -> (forall c : A, P c -> R c -> H c).
Proof.
    intros A P Q R H H0 H1 c P_c.
    apply H0.
    exact (H1 c P_c).
Qed.

(* Ex. 6.3 *)
Theorem th1 : ~False.
Proof.
    intros H.
    apply H.
Qed.

Theorem th2 : forall P : Prop, ~~~P -> ~P.
Proof.
    intros P H0 p.
    apply H0.
    intros H1.
    apply H1.
    assumption.
Qed.

Theorem th3 : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.
Proof.
    intros P Q H not_q p.
    apply not_q.
    apply H.
    assumption.
Qed.

Theorem th4 : forall P Q R : Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
    intros P Q R H0 H1 p.
    apply False_ind.
    apply H1.
    assumption.
    apply H0.
    assumption.
Qed.

(* Ex 6.4 *)
Definition dyslexic_imp := forall P Q : Prop, (P -> Q) -> (Q -> P).
Theorem dyslexic_imp_th : dyslexic_imp -> False.
Proof.
    unfold dyslexic_imp.
    intros inhab.
    apply (inhab False (False -> True)).
    intros f.
    apply False_ind.
    apply False_ind.
Qed.

Definition dyslexic_contrap := forall P Q : Prop, (P -> Q) -> (~P -> ~Q).
Theorem dyslexic_contrap_th : dyslexic_contrap -> False.
Proof.
    unfold dyslexic_contrap.
    intros inhab.
    apply (inhab (dyslexic_contrap -> False) (False -> False)).
    intros ff.
    apply False_ind.
    intros p.
    apply (p inhab).
    apply False_ind.
Qed.

(* Ex 6.5 *)
Theorem eg : forall (A : Set) (a b c d : A), a = c \/ b = c \/ c = c \/ d = c.
Proof.
    intros A a b c d.
    right; right; left.
    reflexivity.
Qed.

(* Ex 6.6 *)
Theorem th6_6_1 : forall A B C : Prop, A/\(B/\C) -> (A/\B)/\C.
Proof.
    intros A B C H0.
    elim H0.
    intros a H1.
    elim H1.
    intros b c.
    split.
    split.
    assumption.
    assumption.
    assumption.
Qed.

Theorem th6_6_2 : forall A B C D : Prop, (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
    intros A B C D [P1 [P2 [a b]]].
    split.
    apply P1.
    assumption.
    apply P2.
    assumption.
Qed.

Theorem th6_6_3 : forall A : Prop, ~(A/\~A).
Proof.
    intros A [a na].
    apply na.
    assumption.
Qed.

Theorem th6_6_4 : forall A B C : Prop, A\/(B\/C) -> (A\/B)\/C.
Proof.
    intros A B C H0.
    elim H0.
    intros a.
    left; left; assumption.
    intros H1.
    elim H1.
    intros b.
    left; right; assumption.
    intros c.
    right; assumption.
Qed.

Theorem th6_6_4' : forall A B C : Prop, A\/(B\/C) -> (A\/B)\/C.
Proof.
    intros A B C [a | [b | c]].
    left; left; assumption.
    left; right; assumption.
    right; assumption.
Qed.

Theorem th6_6_6 : forall A B : Prop, (A\/B)/\~A -> B.
Proof.
    intros A B [[a | b] na].
    apply False_ind.
    apply na.
    assumption.
    assumption.
Qed.

(* Ex 6.7 *)
Definition pierce := forall P Q : Prop, ((P->Q)->P)->P.
Definition classic := forall P : Prop, ~~P -> P.
Definition excluded_middle := forall P : Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q : Prop, ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q : Prop, (P->Q)->(~P\/Q).

Theorem classic_eq : (pierce -> classic) /\ (classic -> excluded_middle) /\ (excluded_middle -> de_morgan_not_and_not) /\ (de_morgan_not_and_not -> implies_to_or) /\ (implies_to_or -> pierce).
Proof.
    repeat split.

    unfold pierce.
    unfold classic.
    intros inhab_pierce.
    intros P nnp.
    apply (inhab_pierce P (~P)).
Abort.

(* Ex 6.9 *)
Section ex6_9.
Variable A : Type.
Variable P Q : A -> Prop.

Theorem th6_9_1 : (exists x : A, P x \/ Q x) -> (ex P) \/ ex Q.
Proof.
    intros H.
    elim H; intros x Hor.
    elim Hor.

    intros Px.
    left.
    exists x.
    assumption.

    intros Qx.
    right.
    exists x.
    assumption.
Qed.

Theorem th6_9_2 : (ex P) \/ (ex Q) -> exists x : A, (P x \/ Q x).
Proof.
    intros H.
    elim H.

    intros H1.
    elim H1; intros x Px.
    exists x.
    left.
    assumption.

    intros H2.
    elim H2; intros x Qx.
    exists x.
    right.
    assumption.
Qed.

Theorem th6_9_3 : (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
Proof.
    intros H0.
    apply False_ind.
    elim H0; intros x H1.
    apply (H1 (fun y => False)).
Qed.

Theorem th6_9_4 : (forall x : A, P x) -> ~(exists y : A, ~P y).
Proof.
    intros H0.
    red.
    intros H1.
    elim H1; intros y nPy.
    apply nPy.
    apply (H0 y).
Qed.

End ex6_9.

(* Ex 6.10 *)
Theorem plus_permute2 : forall n m p : nat, n+m+p = n+p+m.
Proof.
    intros n m p.
    rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm m p).
    rewrite Nat.add_assoc.
    reflexivity.
Qed.

(* Ex 6.11 *)
Theorem eq_trans : forall (A : Type) (a b c : A), a=b -> b=c -> a=c.
Proof.
    intros A a b c H1 H2.
    apply (eq_ind b (fun d => d=c)).
    assumption.
    rewrite H1.
    reflexivity.
Qed.

Theorem eq_trans' : forall (A : Type) (a b c : A), a=b -> b=c -> a=c.
Proof.
    intros A a b c H1 H2.
    rewrite <- H1 in H2.
    assumption.
Qed.
