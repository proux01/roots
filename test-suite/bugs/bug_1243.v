From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
Open Scope Z_scope.

Theorem r_ex : (forall x y:nat, x + y = x + y)%nat.
Admitted.

Theorem r_ex' : forall x y:nat, (x + y = x + y)%nat.
Admitted.
