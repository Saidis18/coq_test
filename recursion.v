Inductive month :=
    | January
    | February
    | March
    | April
    | May
    | June
    | July
    | August
    | September
    | October
    | November
    | December.

(* Ex 7.1 *)
Inductive season :=
    | Winter
    | Spring
    | Summer
    | Autumn.

Definition season_of_month := month_rec (fun _ => season) Winter Winter Winter Spring Spring Spring Summer Summer Summer Autumn Autumn Autumn.

(* Ex 7.3 *)
Theorem bool_equal : forall b : bool, b = true \/ b = false.
Proof fun b => bool_ind (fun x => x = true \/ x = false) (or_introl refl_equal) (or_intror refl_equal) b.

Theorem bool_equal' : forall b : bool, b = true \/ b = false.
Proof.
    intro b.
    pattern b.
    apply bool_ind; [left | right]; reflexivity.
Qed.

(* Ex 7.9 *)
Inductive vehicle : Set :=
    | bicycle : nat -> vehicle
    | motorized : nat -> nat -> vehicle.

Definition nb_seats : vehicle -> nat := vehicle_rec (fun _ => nat) (fun x => x) (fun x _ => x).

(* Ex. 7.10 *)
Theorem ineq : true <> false.
Proof.
    unfold not.
    intros H.
    change (bool_rect (fun _ => Prop) True False false).
    rewrite <- H.
    simpl.
    exact I.
Qed.

(* Ex. 7.11 *)
Theorem ineq_vehicle : forall a b c : nat, bicycle a <> motorized b c.
Proof.
    unfold not.
    intros a b c H.
    change (vehicle_rect (fun _ => Prop) (fun _ => True) (fun _ _ => False) (motorized b c)).
    rewrite <- H.
    simpl.
    exact I.
Qed.

(* Ex 7.18 *)
Require Import ZArith.
Definition x1000 := xO (xO (xO (xI (xO (xI (xI (xI (xI xH)))))))).
Definition x25 := xI (xO (xO (xI xH))).
Definition x512 := xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))).

(* Ex 7.19 *)
Definition pos_even_bool p := match p with
    | xO _ => true
    | xI _ | xH => false
end.

(* Ex 7.20 *)
Definition pos_div4 (p : positive) : Z := match p with
    | xH | xO xH | xI xH => 0
    | xO (xO x) | xO (xI x) | xI (xO x) | xI (xI x) => Zpos x
end.

(* Ex 7.25 *)
Fixpoint discrete_log (p : positive) : nat := match p with
    | xH => 0
    | xI x | xO x => S (discrete_log x)
end.

Fixpoint pow2 (n : nat) : positive := match n with
    | 0 => xH
    | S x => xO (pow2 x)
end.

(* Ex 7.27 *)
Inductive Z_inf_branch_tree : Set :=
    | Z_inf_leaf : Z_inf_branch_tree
    | Z_inf_node : Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree.

Fixpoint fold_or (f : nat -> bool) (n : nat) := match n with
    | 0 => f 0
    | S x => if f (S x) then true else fold_or f x
end.

Fixpoint zero_present (t : Z_inf_branch_tree) n := match t with
    | Z_inf_leaf => false
    | Z_inf_node z f =>
        if Zeq_bool z 0 then
            true
        else
            fold_or (fun x => zero_present (f x) n) n
end.

(* Ex 7.28 *)
Theorem plus_n_O : forall n: nat, n = n + 0.
Proof.
    intros n.
    elim n.
    simpl.
    reflexivity.
    intros m H.
    rewrite H at 1.
    apply plus_Sn_m.
Qed.

(* Ex 7.29 *)
Inductive Z_btree :=
    | Z_leaf : Z_btree
    | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Inductive Z_fbtree :=
    | Z_fleaf : Z_fbtree
    | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.

Fixpoint f1 (t : Z_btree) : Z_fbtree := match t with
    | Z_leaf => Z_fleaf
    | Z_bnode z l r => Z_fnode z (fun x => if x then f1 l else f1 r)
end.

Fixpoint f2 (t : Z_fbtree) : Z_btree := match t with
    | Z_fleaf => Z_leaf
    | Z_fnode z f => Z_bnode z (f2 (f true)) (f2 (f false))
end.

Theorem bij1 : forall t : Z_btree, f2 (f1 t) = t.
Proof.
    intros t.
    elim t.
    unfold f1.
    unfold f2.
    reflexivity.
    intros z l Hl r Hr.
    simpl.
    rewrite Hl.
    rewrite Hr.
    reflexivity.
Qed.

Theorem factor : forall (z:Z) (f : bool -> Z_fbtree), f2 (Z_fnode z f) = Z_bnode z (f2 (f true)) (f2 (f false)).
Proof.
    trivial.
Qed.

Theorem factor' : forall (z:Z) (l r : Z_btree), f1 (Z_bnode z l r) = Z_fnode z (fun x => if x then f1 l else f1 r).
Proof.
    trivial.
Qed.

Theorem eq_fun : forall (A : Set) (f : bool -> A) (b : bool), f b = (fun x : bool => if x then f true else f false) b.
Proof.
    intros A f b.
    elim b; reflexivity.
Qed.

Theorem bij2 : forall t : Z_fbtree, f1 (f2 t) = t.
Proof.
    intros t.
    elim t.
    unfold f2.
    unfold f1.
    reflexivity.
    intros z f H.
    rewrite factor.
    rewrite factor'.
    rewrite H.
    rewrite H.
    (* rewrite <- eq_fun. *)
Abort.
(*
Ce qui nous manque est l'égalité de fonctions avec une définition ensembliste.
Ici il est impossible de montrer l'égalité de deux fonctions en disant qu'elle prennent les mêmes valeurs.
*)

(* Ex 7.30 *)
Fixpoint mult2 (n : nat) : nat := match n with
    | 0 => 0
    | S x => S (S (mult2 x))
end.

Theorem mult2_th : forall n : nat, mult2 n = n + n.
Proof.
    intros n.
    elim n.
    unfold mult2.
    simpl.
    reflexivity.
    unfold mult2.
    intros p H.
    rewrite H.
    simpl.
    rewrite <- plus_Sn_m.
    rewrite Nat.add_comm.
    reflexivity.
Qed.

(* Ex 7.31 *)
Fixpoint sum_n (n : nat) : nat := match n with
    | 0 => 0
    | S x => S x + sum_n x
end.

Theorem sum_n_th : forall n : nat, 2 * sum_n n = n * S n.
Proof.
    intro n.
    elim n.
    unfold sum_n.
    simpl.
    reflexivity.
    unfold sum_n.
    intros p H.
    rewrite Nat.mul_add_distr_l.
    rewrite H.
    rewrite <- Nat.mul_add_distr_r.
    rewrite Nat.mul_comm.
    reflexivity.
Qed.

(* Ex 7.32 *)
Theorem n_leq_sum_n : forall n : nat, n <= sum_n n.
Proof.
    intro n.
    elim n.
    simpl.
    reflexivity.
    unfold sum_n.
    intros p H.
    apply Nat.le_add_r.
Qed.

(* Ex 7.41 *)
Require Import List.
Fixpoint split (A B : Set) (l : list (A*B)) := match l with
    | nil => (nil, nil)
    | (a,b)::t =>
        let (la,lb) := split A B t in
        (a::la, b::lb)
end.

Fixpoint combine (A B : Set) (la : list A) (lb : list B) := match (la,lb) with
    | (nil,_) | (_,nil) => nil
    | (a::ta, b::tb) => (a,b)::combine A B ta tb
end.

Definition combine' (A B : Set) (l : list A * list B) :=
    let (la, lb) := l in
    combine A B la lb.

Theorem comb_split : forall (A B : Set) (l : list (A*B)), combine' A B (split A B l) = l.
Proof.
    intros A B l.
    elim l.
    unfold split.
    unfold combine'.
    unfold combine.
    reflexivity.
    unfold combine'.
    intros (a,b) ll H.
    simpl.
    destruct (split A B ll).
    simpl.
    rewrite H.
    reflexivity.
Qed.
