Inductive day :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_weekday d :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Compute (next_weekday saturday).

Eval compute in (next_weekday saturday).

Inductive s_list (A: Type) :=
    | n
    | c (x: A) (t: s_list A).

Fixpoint map A B (f: A -> B) l :=
    match l with
        | n _ => n _
        | c _ x xs => c _ (f x) (map A B f xs)
    end.

Fixpoint equal n m :=
    match n, m with
        | 0, 0 =>true
        | 0, S _ | S _, 0 => false
        | S n', S m' => equal n' m'
    end.

Lemma com: forall a b: Prop, a /\ b -> b /\ a.
Proof.
    intros a b.
    intros H.
    split.
    destruct H as [Ha Hb].
    exact Hb.
    destruct H as [Ha Hb].
    exact Ha.
Qed.

Lemma com': forall a b : Prop, a /\ b -> b /\ a.
Proof.
    intros a b.
    intros H.
    split.
    apply H.
    apply H.
Qed.

Lemma barbara: forall p q r : Prop, (p -> q) -> (q -> r) -> (p -> r).
Proof.
    intros p q r.
    intros H.
    intros H'.
    intros P.
    assert q.
    apply H.
    assumption.
    apply H'.
    assumption.
Qed.

Lemma ex:
    forall P Q : nat -> Prop, (forall x : nat, P x -> Q x) /\ (exists x : nat, ~Q x) -> ~forall x : nat, Q x \/ P x.
Proof.
    intros P Q.
    intros H.
    destruct H as [H1 H2].
    intros H3.
    destruct H2 as [x H4].
    destruct (H3 x) as [Hq | Hp].
    assert (Q x /\ ~Q x).
    split.
    exact Hq.
    exact H4.
    contradiction.
    assert (Q x).
    apply H1.
    assumption.
    assert (Q x /\ ~Q x).
    split.
    exact H.
    exact H4.
    contradiction.
Qed.

Lemma ex':
    forall P Q : nat -> Prop, (forall x : nat, P x -> Q x) /\ (exists x : nat, ~Q x) -> ~forall x : nat, Q x \/ P x.
Proof.
    intros P Q.
    intros H.
    intros H1.
    destruct H as [H2 H3].
    destruct H3 as [x H3].
    destruct (H1 x) as [Hq | Hp].
    contradiction.
    assert (Q x).
    apply H2.
    assumption.
    contradiction.
Qed.

Check fun (A B: Type) (x: forall _ : A, B) => x.
Check fun (A B: Type) (x: A -> B) => x.
Check fun (x: forall n: nat, n >= 2) => x.
Definition grt2 := {n : nat | n >= 2}.

Inductive vecteur : nat -> Type :=
    | vnil : vecteur 0
    | vcons : forall n : nat, vecteur n -> vecteur (S n).

Check vcons 1 (vcons 0 vnil).

Inductive vecteur_ae (A: Type) : nat -> Type :=
    | vnil_ae : vecteur_ae A 0
    | vcons_ae : A -> forall n : nat, vecteur_ae A n -> vecteur_ae A (S n).

Check vcons_ae.
Check vnil_ae.
Check vcons_ae day monday 1 (vcons_ae day tuesday 0 (vnil_ae day)).
