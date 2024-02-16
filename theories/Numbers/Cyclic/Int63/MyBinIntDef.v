From Coq Require Import BinNums.
From Coq Require Import MyBinPosDef MyBinNatDef.

Local Open Scope Z_scope.

Local Notation "0" := Z0.
Local Notation "1" := (Zpos 1).
Local Notation "2" := (Zpos 2).

(***********************************************************)
(** * Binary Integers, Definitions of Operations *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

Module Import Z.

(** ** Nicer names [Z.pos] and [Z.neg] for constructors *)

Notation pos := Zpos.
Notation neg := Zneg.

(** ** Doubling and variants *)

Definition double x :=
  match x with
    | 0 => 0
    | pos p => pos p~0
    | neg p => neg p~0
  end.

Definition succ_double x :=
  match x with
    | 0 => 1
    | pos p => pos p~1
    | neg p => neg (Pos.pred_double p)
  end.

Definition pred_double x :=
  match x with
    | 0 => neg 1
    | neg p => neg p~1
    | pos p => pos (Pos.pred_double p)
  end.

(** ** Subtraction of positive into Z *)

Fixpoint pos_sub (x y:positive) {struct y} : Z :=
  match x, y with
    | p~1, q~1 => double (pos_sub p q)
    | p~1, q~0 => succ_double (pos_sub p q)
    | p~1, xH => pos p~0
    | p~0, q~1 => pred_double (pos_sub p q)
    | p~0, q~0 => double (pos_sub p q)
    | p~0, xH => pos (Pos.pred_double p)
    | xH, q~1 => neg q~0
    | xH, q~0 => neg (Pos.pred_double q)
    | xH, xH => Z0
  end%positive.

(** ** Addition *)

Definition add x y :=
  match x, y with
    | 0, y => y
    | x, 0 => x
    | pos x', pos y' => pos (Pos.add x' y')
    | pos x', neg y' => pos_sub x' y'
    | neg x', pos y' => pos_sub y' x'
    | neg x', neg y' => neg (Pos.add x' y')
  end.

Infix "+" := add : Z_scope.

(** ** Opposite *)

Definition opp x :=
  match x with
    | 0 => 0
    | pos x => neg x
    | neg x => pos x
  end.

Notation "- x" := (opp x) : Z_scope.

(** ** Subtraction *)

Definition sub m n := m + -n.

Infix "-" := sub : Z_scope.

(** ** Multiplication *)

Definition mul x y :=
  match x, y with
    | 0, _ => 0
    | _, 0 => 0
    | pos x', pos y' => pos (Pos.mul x' y')
    | pos x', neg y' => neg (Pos.mul x' y')
    | neg x', pos y' => neg (Pos.mul x' y')
    | neg x', neg y' => pos (Pos.mul x' y')
  end.

Infix "*" := mul : Z_scope.

(** ** Power function *)

Definition pow_pos (z:Z) := Pos.iter (mul z) 1.

Definition pow x y :=
  match y with
    | pos p => pow_pos x p
    | 0 => 1
    | neg _ => 0
  end.

(** ** Comparison *)

Definition compare x y :=
  match x, y with
    | 0, 0 => Eq
    | 0, pos y' => Lt
    | 0, neg y' => Gt
    | pos x', 0 => Gt
    | pos x', pos y' => Pos.compare x' y'
    | pos x', neg y' => Gt
    | neg x', 0 => Lt
    | neg x', pos y' => Lt
    | neg x', neg y' => CompOpp (Pos.compare x' y')
  end.

Infix "?=" := compare (at level 70, no associativity) : Z_scope.

(** ** Sign function *)

Definition sgn z :=
  match z with
    | 0 => 0
    | pos p => 1
    | neg p => neg 1
  end.

(** Boolean equality and comparisons *)

Definition leb x y :=
  match x ?= y with
    | Gt => false
    | _ => true
  end.

Definition ltb x y :=
  match x ?= y with
    | Lt => true
    | _ => false
  end.

Definition eqb x y :=
  match x, y with
    | 0, 0 => true
    | pos p, pos q => Pos.eqb p q
    | neg p, neg q => Pos.eqb p q
    | _, _ => false
  end.

Infix "=?" := eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := leb (at level 70, no associativity) : Z_scope.
Infix "<?" := ltb (at level 70, no associativity) : Z_scope.

(** ** Conversions *)

(** From [nat] to [Z] *)

Definition of_nat (n:nat) : Z :=
  match n with
   | O => 0
   | S n => pos (Pos.of_succ_nat n)
  end.

(** From [N] to [Z] *)

Definition of_N (n:N) : Z :=
  match n with
    | N0 => 0
    | Npos p => pos p
  end.

(** Conversion with a decimal representation for printing/parsing *)

Definition of_uint (d:Decimal.uint) := of_N (Pos.of_uint d).

Definition of_num_uint (d : Number.uint) :=
  match d with
  | Number.UIntDecimal d => Some (of_uint d)
  | Number.UIntHexadecimal d => None
  end.

Definition of_int (d:Decimal.int) :=
  match d with
  | Decimal.Pos d => of_uint d
  | Decimal.Neg d => opp (of_uint d)
  end.

Definition of_num_int (d : Number.int) :=
  match d with
  | Number.IntDecimal d => Some (of_int d)
  | Number.IntHexadecimal d => None
  end.

Definition to_int n :=
  match n with
  | 0 => Decimal.Pos Decimal.zero
  | pos p => Decimal.Pos (Pos.to_uint p)
  | neg p => Decimal.Neg (Pos.to_uint p)
  end.

Definition to_num_int n := Number.IntDecimal (to_int n).

(** ** Euclidean divisions for binary integers *)

(** ** Floor division *)

(** [div_eucl] provides a Truncated-Toward-Bottom (a.k.a Floor)
  Euclidean division. Its projections are named [div] (noted "/")
  and [modulo] (noted with an infix "mod").
  These functions correspond to the `div` and `mod` of Haskell.
  This is the historical convention of Coq.

  The main properties of this convention are :
    - we have [sgn (a mod b) = sgn (b)]
    - [div a b] is the greatest integer smaller or equal to the exact
      fraction [a/b].
    - there is no easy sign rule.

  In addition, note that we take [a/0 = 0] and [a mod 0 = a].
  This choice is motivated by the div-mod equation
    [a = (a / b) * b + (a mod b)] for [b = 0].
*)

(** First, a division for positive numbers. Even if the second
   argument is a Z, the answer is arbitrary if it isn't a Zpos. *)

Fixpoint pos_div_eucl (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if 2 <=? b then (0, 1) else (1, 0)
    | xO a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := 2 * r in
      if r' <? b then (2 * q, r') else (2 * q + 1, r' - b)
    | xI a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := 2 * r + 1 in
      if r' <? b then (2 * q, r') else (2 * q + 1, r' - b)
  end.

(** Then the general euclidean division *)

Definition div_eucl (a b:Z) : Z * Z :=
  match a, b with
    | 0, _ => (0, 0)
    | _, 0 => (0, a)
    | pos a', pos _ => pos_div_eucl a' b
    | neg a', pos _ =>
      let (q, r) := pos_div_eucl a' b in
	match r with
	  | 0 => (- q, 0)
	  | _ => (- (q + 1), b - r)
	end
    | neg a', neg b' =>
      let (q, r) := pos_div_eucl a' (pos b') in (q, - r)
    | pos a', neg b' =>
      let (q, r) := pos_div_eucl a' (pos b') in
	match r with
	  | 0 => (- q, 0)
	  | _ => (- (q + 1), b + r)
	end
  end.

Definition div (a b:Z) : Z := let (q, _) := div_eucl a b in q.
Definition modulo (a b:Z) : Z := let (_, r) := div_eucl a b in r.

Infix "/" := div : Z_scope.
Infix "mod" := modulo (at level 40, no associativity) : Z_scope.

(** Bitwise operations [lor] [land] [ldiff] [lxor] *)

Definition lor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | pos a, pos b => pos (Pos.lor a b)
   | neg a, pos b => neg (N.succ_pos (N.ldiff (Pos.pred_N a) (Npos b)))
   | pos a, neg b => neg (N.succ_pos (N.ldiff (Pos.pred_N b) (Npos a)))
   | neg a, neg b => neg (N.succ_pos (N.land (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition land a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => 0
   | pos a, pos b => of_N (Pos.land a b)
   | neg a, pos b => of_N (N.ldiff (Npos b) (Pos.pred_N a))
   | pos a, neg b => of_N (N.ldiff (Npos a) (Pos.pred_N b))
   | neg a, neg b => neg (N.succ_pos (N.lor (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition lxor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | pos a, pos b => of_N (Pos.lxor a b)
   | neg a, pos b => neg (N.succ_pos (N.lxor (Pos.pred_N a) (Npos b)))
   | pos a, neg b => neg (N.succ_pos (N.lxor (Npos a) (Pos.pred_N b)))
   | neg a, neg b => of_N (N.lxor (Pos.pred_N a) (Pos.pred_N b))
 end.

End Z.
