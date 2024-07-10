From Stdlib Require Import NsatzTactic ZArith QArith.

Goal forall x y : Z, (x + y = y + x)%Z.
  intros; nsatz.
Qed.

Goal forall x y : Q, Qeq (x + y) (y + x).
  intros; nsatz.
Qed.
