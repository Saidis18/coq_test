(* Ex 7.12 *)
Theorem not1_0 : 1<>0.
Proof.
    unfold not.
    intros H.
    change ((fun x => match x with 0 => False | S _ => True end) 0).
    rewrite <- H.
    trivial.
Qed.

Theorem not2_0 : 2<>0.
Proof.
    unfold not.
    intros H.
    change ((fun x => match x with 0 => False | S _ => True end) 0).
    rewrite <- H.
    trivial.
Qed.

Require Import Arith.
Record RatPlus : Set := mkRat {top : nat; bottom : nat; bottom_condition : bottom <> 0}.
Axiom eqRatPlus : forall r r' : RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.

Theorem incoherence : False.
Proof.
    discriminate (eqRatPlus (mkRat 0 1 not1_0) (mkRat 0 2 not2_0)).
    simpl.
    reflexivity.
Qed.