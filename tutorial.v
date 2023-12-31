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

(* Ex 5.5 *)
Theorem all_perm : forall (A : Type) (P : A -> A -> Prop), (forall x y : A, P x y) -> forall x y : A, P y x.
Proof fun A P => fun (f : forall x y : A, P x y) => (fun y x => f x y).
Print all_perm.

Theorem resolution : forall (A: Type) (P Q R H : A -> Prop), (forall a : A, Q a -> R a -> H a) -> (forall b : A, P b -> Q b) -> (forall c : A, P c -> R c -> H c).
Proof fun _ _ _ _ _ f g c pc => f c (g c pc).
Print resolution.
