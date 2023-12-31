Lemma barbara: forall p q r : Prop, (p -> q) -> (q -> r) -> (p -> r).
Proof.
    intros p q r.
    intros H.
    intros H'.
    intros P.
    apply H'.
    apply H.
    assumption.
Qed.

Lemma ex1_2: forall p q r : Prop, (p -> q -> r) -> (q -> p) -> (q -> r).
Proof.
    intros p q r.
    intros H H'.
    intros Q.
    assert p.
    apply H'.
    assumption.
    apply H.
    assumption.
    assumption.
Qed.

Lemma ex2_1: forall p q : Prop, p /\ q -> q /\ p.
Proof.
    intros p q.
    intros H.
    split.
    destruct H as [P Q].
    assumption.
    destruct H as [P Q].
    assumption.
Qed.

Lemma ex2_2: forall p q r : Prop, (p /\ q) -> r -> (q /\ r).
Proof.
    intros p q r.
    intros H.
    intros R.
    split.
    destruct H as [P Q].
    assumption.
    assumption.
Qed.

Lemma ex2_3: forall p q r : Prop, (p /\ q) -> r -> (p -> (q -> r)).
Proof.
    intros p q r.
    intros H.
    intros R P Q.
    assumption.
Qed.
