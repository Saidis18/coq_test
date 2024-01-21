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