Require Import List.

Fixpoint trie (A: Type) (cmp: A -> A -> Prop) (l : list A) :=
    match l with
        | nil | _::nil => True
        | x::(y::t as l') => (cmp x y) /\ trie A cmp l'
    end.

Fixpoint eliminer A (eq: A -> A -> bool) x l :=
    match l with
        | nil => nil
        | h::t =>
            if eq h x then
                t
            else
                h::eliminer A eq x  t
    end.

Fixpoint permutation A (eq: A -> A -> bool) l l' :=
    match l, l' with
        | nil, nil => True
        | nil, _ => False
        | h1::t1, _ => permutation A eq t1 (eliminer A eq h1 l')
    end.

Fixpoint div (A: Type) l :=
    match l with
        | nil => (nil: list A, nil: list A)
        | x::nil => (x::nil, nil)
        | x::y::t =>
            let (t1, t2) := div A t in
            (x::t1, y::t2)
    end.
