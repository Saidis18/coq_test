Inductive expr :=
    | zero
    | identity
    | const : nat -> expr
    | func : nat -> expr
    | add : expr -> expr -> expr
    | diff : expr -> expr -> expr
    | mul : expr -> expr -> expr
    | div : expr -> expr -> expr.

Fixpoint simplify f :=
    match f with
    | zero => zero
    | identity => identity
    | const n => const n
    | func n => func n
    | add zero f | add f zero => simplify f
    | add f1 f2 => add (simplify f1) (simplify f2)
    | diff f zero => simplify f
    | diff f1 f2 => diff (simplify f1) (simplify f2)
    | mul zero _ | mul _ zero => zero
    | mul f1 f2 => mul (simplify f1) (simplify f2)
    | div zero _ => zero
    | div f1 f2 => div (simplify f1) (simplify f2)
    end.

Fixpoint deriv' d e :=
    match e with
    | zero | const _ => zero
    | identity => const 1
    | func f => d f
    | add f1 f2 => add (deriv' d f1) (deriv' d f2)
    | diff f1 f2 => diff (deriv' d f1) (deriv' d f2)
    | mul f1 f2 => add (mul (deriv' d f1) f2) (mul f1 (deriv' d f2))
    | div f1 f2 => div (diff (mul (deriv' d f1) f2) (mul f1 (deriv' d f2))) (mul f2 f2)
    end.

Definition deriv d f := simplify (deriv' d (simplify f)).

Fixpoint sigma f n :=
    match n with
    | 0 => zero
    | S k => add f (sigma f k)
    end.

Fixpoint pow f n :=
    match n with
    | 0 => const 1
    | S k => mul f (pow f k)
    end.

Lemma  deriv_pow : forall d : nat -> expr, forall f : expr, forall n : nat, simplify ( deriv d (pow f n) ) = simplify (mul (deriv d f) (sigma (pow f (n-1)) n)).
Proof.
    intros d f.
    induction n.
    simpl.