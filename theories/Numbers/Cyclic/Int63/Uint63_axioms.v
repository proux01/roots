(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(* From Coq Require Export BinInt. *)

From Coq Require Import BinNums.
From Coq Require Import MyBinIntDef.

Local Open Scope Z_scope.

Module Z'.

Include MyBinIntDef.Z.

(** * Logic Predicates *)

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Definition divide x y := exists z, y = z*x.

End Z'.

(** Re-export Notations *)

Number Notation Z Z.of_num_int Z.to_num_int : Z_scope.

Infix "+" := Z.add : Z_scope.
Notation "- x" := (Z.opp x) : Z_scope.
Infix "-" := Z.sub : Z_scope.
Infix "*" := Z.mul : Z_scope.
Infix "^" := Z.pow : Z_scope.
Infix "/" := Z.div : Z_scope.
Infix "mod" := Z.modulo (at level 40, no associativity) : Z_scope.
Infix "?=" := Z.compare (at level 70, no associativity) : Z_scope.
Infix "=?" := Z.eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := Z.leb (at level 70, no associativity) : Z_scope.
Infix "<?" := Z.ltb (at level 70, no associativity) : Z_scope.
Notation "( x | y )" := (Z'.divide x y) (at level 0) : Z_scope.
Infix "<=" := Z'.le : Z_scope.
Infix "<" := Z'.lt : Z_scope.
Infix ">=" := Z'.ge : Z_scope.
Infix ">" := Z'.gt : Z_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.



















From Coq Require Export PrimInt63.

Module Import Uint63NotationsInternalB.
Infix "<<" := lsl (at level 30, no associativity) : uint63_scope.
Infix ">>" := lsr (at level 30, no associativity) : uint63_scope.
Infix "land" := land (at level 40, left associativity) : uint63_scope.
Infix "lor" := lor (at level 40, left associativity) : uint63_scope.
Infix "lxor" := lxor (at level 40, left associativity) : uint63_scope.
Infix "+" := add : uint63_scope.
Infix "-" := sub : uint63_scope.
Infix "*" := mul : uint63_scope.
Infix "/" := div : uint63_scope.
Infix "mod" := PrimInt63.mod (at level 40, no associativity) : uint63_scope.
Infix "=?" := eqb (at level 70, no associativity) : uint63_scope.
Infix "<?" := ltb (at level 70, no associativity) : uint63_scope.
Infix "<=?" := leb (at level 70, no associativity) : uint63_scope.
End Uint63NotationsInternalB.

Definition size := 63%nat.

Local Open Scope uint63_scope.

(** The number of digits as an int *)
Definition digits := 63.

(** The biggest int *)
Definition max_int := Eval vm_compute in 0 - 1.

(** Access to the nth digits *)
Definition get_digit x p := (0 <? (x land (1 << p))).

Definition set_digit x p (b:bool) :=
  if if 0 <=? p then p <? digits else false then
    if b then x lor (1 << p)
    else x land (max_int lxor (1 << p))
  else x.

(** Translation to Z *)
Definition is_zero (i:int) := i =? 0.
Definition is_even (i:int) := is_zero (i land 1).
Fixpoint to_Z_rec (n:nat) (i:int) :=
  match n with
  | O => 0%Z
  | S n =>
    (if is_even i then Z.double else Z.succ_double) (to_Z_rec n (i >> 1))
  end.

Definition to_Z := to_Z_rec size.

Fixpoint of_pos_rec (n:nat) (p:positive) {struct p} :=
  match n, p with
  | O, _ => 0
  | S n, xH => 1
  | S n, xO p => (of_pos_rec n p) << 1
  | S n, xI p => (of_pos_rec n p) << 1 lor 1
  end.

Definition of_pos := of_pos_rec size.

Definition of_Z z :=
  match z with
  | Zpos p => of_pos p
  | Z0 => 0
  | Zneg p => (0 - (of_pos p))%uint63
  end.

Definition wB := (2 ^ (Z.of_nat size))%Z.

(* Notations *)
Local Open Scope Z_scope.

(* Bijection : uint63 <-> Bvector size *)

Axiom of_to_Z : forall x, of_Z (to_Z x) = x.

(** Specification of logical operations *)

Axiom lsl_spec : forall x p, to_Z (x << p)  = to_Z x  * 2 ^ to_Z  p  mod wB.

Axiom lsr_spec : forall x p, to_Z (x >> p) = to_Z x / 2 ^ to_Z p.

Definition bit i n :=  negb (is_zero ((i >> n) << (digits - 1))).

Axiom land_spec: forall x y i , bit (x land y) i = andb (bit x i) (bit y i).

Axiom lor_spec: forall x y i, bit (x lor y) i = orb (bit x i) (bit y i).

Axiom lxor_spec: forall  x y i, bit (x lxor y) i = xorb (bit x i) (bit y i).

(** Specification of basic opetations *)

(* Arithmetic modulo operations *)

(* Remarque : les axiomes seraient plus simple si on utilise of_Z a la place :
   exemple : add_spec : forall x y, of_Z (x + y) = of_Z x + of_Z y. *)

Axiom add_spec : forall x y, to_Z (x + y) = (to_Z x + to_Z y) mod wB.

Axiom sub_spec : forall x y, to_Z (x - y) = (to_Z x - to_Z y) mod wB.

Axiom mul_spec : forall x y, to_Z (x * y) = to_Z x * to_Z y mod wB.

Axiom mulc_spec : forall x y, to_Z x * to_Z y = to_Z (fst (mulc x y)) * wB + to_Z (snd (mulc x y)).

Axiom div_spec : forall x y, to_Z (x / y) = to_Z x / to_Z y.

Axiom mod_spec : forall x y, to_Z (x mod y) = to_Z x mod to_Z y.

(* Comparisons *)
Axiom eqb_correct : forall i j, (i =? j)%uint63 = true -> i = j.

Axiom eqb_refl : forall x, (x =? x)%uint63 = true.

Axiom ltb_spec : forall x y, (x <? y)%uint63 = true <-> to_Z x < to_Z y.

Axiom leb_spec : forall x y, (x <=? y)%uint63 = true <-> to_Z x <= to_Z y.

(** Exotic operations *)

(** Axioms on operations which are just short cut *)

Definition compare_def x y :=
  if (x <? y)%uint63 then Lt
  else if (x =? y)%uint63 then Eq else Gt.

Axiom compare_def_spec : forall x y, compare x y = compare_def x y.

Axiom head0_spec  : forall x,  0 < to_Z x ->
         wB/ 2 <= 2 ^ (to_Z (head0 x)) * to_Z x < wB.

Axiom tail0_spec  : forall x, 0 < to_Z x ->
         (exists y, 0 <= y /\ to_Z x = (2 * y + 1) * (2 ^ to_Z (tail0 x)))%Z.

Definition addc_def x y :=
  let r := (x + y)%uint63 in
  if (r <? x)%uint63 then C1 r else C0 r.

Axiom addc_def_spec : forall x y, addc x y = addc_def x y.

Definition addcarry i j := (i + j + 1)%uint63.
Definition addcarryc_def x y :=
  let r := addcarry x y in
  if (r <=? x)%uint63 then C1 r else C0 r.

Axiom addcarryc_def_spec : forall x y, addcarryc x y = addcarryc_def x y.

Definition subc_def x y :=
  (if y <=? x then C0 (x - y) else C1 (x - y))%uint63.

Axiom subc_def_spec : forall x y, subc x y = subc_def x y.

Definition subcarryc_def x y :=
  if (y <? x)%uint63 then C0 (x - y - 1)%uint63 else C1 (x - y - 1)%uint63.

Axiom subcarryc_def_spec : forall x y, subcarryc x y = subcarryc_def x y.

Definition diveucl_def x y := (x/y, x mod y)%uint63.

Axiom diveucl_def_spec : forall x y, diveucl x y = diveucl_def x y.

Axiom diveucl_21_spec :  forall a1 a2 b,
   let (q,r) := diveucl_21 a1 a2 b in
   let (q',r') := Z.div_eucl (to_Z a1 * wB + to_Z a2) (to_Z b) in
   to_Z a1 < to_Z b -> to_Z q = q' /\ to_Z r = r'.

Definition addmuldiv_def p x y :=
  (x << p) lor (y >> (digits - p)).

Axiom addmuldiv_def_spec : forall p x y,
  addmuldiv p x y = addmuldiv_def p x y.
