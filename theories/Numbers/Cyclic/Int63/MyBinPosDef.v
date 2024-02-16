(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************************************************)
(** * Binary positive numbers, operations *)
(**********************************************************************)

(** Initial development by Pierre Crégut, CNET, Lannion, France *)

(** The type [positive] and its constructors [xI] and [xO] and [xH]
    are now defined in [BinNums.v] *)

From Coq Require Export BinNums.

Local Open Scope positive_scope.

(** Postfix notation for positive numbers, which allows mimicking
    the position of bits in a big-endian representation.
    For instance, we can write [1~1~0] instead of [(xO (xI xH))]
    for the number 6 (which is 110 in binary notation).
*)

Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Notation "1" := xH : positive_scope.
Notation "2" := 1~0 : positive_scope.

Module Pos.

(** * Operations over positive numbers *)

(** ** Successor *)

Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

(** ** Addition *)

Fixpoint add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, 1 => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (succ q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end

with add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, 1 => (succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, 1 => (succ p)~0
    | 1, q~1 => (succ q)~1
    | 1, q~0 => (succ q)~0
    | 1, 1 => 1~1
  end.

(** ** Operation [x -> 2*x-1] *)

Fixpoint pred_double x :=
  match x with
    | p~1 => p~0~1
    | p~0 => (pred_double p)~1
    | 1 => 1
  end.

(** ** The predecessor of a positive number can be seen as a [N] *)

Definition pred_N x :=
  match x with
    | p~1 => Npos (p~0)
    | p~0 => Npos (pred_double p)
    | 1 => N0
  end.

(** ** Multiplication *)

Fixpoint mul x y :=
  match x with
    | p~1 => add y (mul p y)~0
    | p~0 => (mul p y)~0
    | 1 => y
  end.

(** ** Iteration over a positive number *)

Definition iter {A} (f:A -> A) : A -> positive -> A :=
  fix iter_fix x n := match n with
    | xH => f x
    | xO n' => iter_fix (iter_fix x n') n'
    | xI n' => f (iter_fix (iter_fix x n') n')
  end.

(** ** Comparison on binary positive numbers *)

Fixpoint compare_cont (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
    | p~1, q~1 => compare_cont r p q
    | p~1, q~0 => compare_cont Gt p q
    | p~1, 1 => Gt
    | p~0, q~1 => compare_cont Lt p q
    | p~0, q~0 => compare_cont r p q
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

Definition compare := compare_cont Eq.

(** ** Boolean equality and comparisons *)

Fixpoint eqb p q {struct q} :=
  match p, q with
    | p~1, q~1 => eqb p q
    | p~0, q~0 => eqb p q
    | 1, 1 => true
    | _, _ => false
  end.

Definition Nsucc_double x :=
  match x with
  | N0 => Npos 1
  | Npos p => Npos p~1
  end.

Definition Ndouble n :=
  match n with
  | N0 => N0
  | Npos p => Npos p~0
  end.

(** Operation over bits. *)

(** Logical [or] *)

Fixpoint lor (p q : positive) : positive :=
  match p, q with
    | 1, q~0 => q~1
    | 1, _ => q
    | p~0, 1 => p~1
    | _, 1 => p
    | p~0, q~0 => (lor p q)~0
    | p~0, q~1 => (lor p q)~1
    | p~1, q~0 => (lor p q)~1
    | p~1, q~1 => (lor p q)~1
  end.

(** Logical [and] *)

Fixpoint land (p q : positive) : N :=
  match p, q with
    | 1, q~0 => N0
    | 1, _ => Npos 1
    | p~0, 1 => N0
    | _, 1 => Npos 1
    | p~0, q~0 => Ndouble (land p q)
    | p~0, q~1 => Ndouble (land p q)
    | p~1, q~0 => Ndouble (land p q)
    | p~1, q~1 => Nsucc_double (land p q)
  end.

(** Logical [diff] *)

Fixpoint ldiff (p q:positive) : N :=
  match p, q with
    | 1, q~0 => Npos 1
    | 1, _ => N0
    | _~0, 1 => Npos p
    | p~1, 1 => Npos (p~0)
    | p~0, q~0 => Ndouble (ldiff p q)
    | p~0, q~1 => Ndouble (ldiff p q)
    | p~1, q~1 => Ndouble (ldiff p q)
    | p~1, q~0 => Nsucc_double (ldiff p q)
  end.

(** [xor] *)

Fixpoint lxor (p q:positive) : N :=
  match p, q with
    | 1, 1 => N0
    | 1, q~0 => Npos (q~1)
    | 1, q~1 => Npos (q~0)
    | p~0, 1 => Npos (p~1)
    | p~0, q~0 => Ndouble (lxor p q)
    | p~0, q~1 => Nsucc_double (lxor p q)
    | p~1, 1 => Npos (p~0)
    | p~1, q~0 => Nsucc_double (lxor p q)
    | p~1, q~1 => Ndouble (lxor p q)
  end.

(* Another version that converts [n] into [n+1] *)

Fixpoint of_succ_nat (n:nat) : positive :=
  match n with
    | O => 1
    | S x => succ (of_succ_nat x)
  end.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := 1~0~1~0.

Fixpoint of_uint_acc (d:Decimal.uint)(acc:positive) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 l => of_uint_acc l (mul ten acc)
  | Decimal.D1 l => of_uint_acc l (add 1 (mul ten acc))
  | Decimal.D2 l => of_uint_acc l (add 1~0 (mul ten acc))
  | Decimal.D3 l => of_uint_acc l (add 1~1 (mul ten acc))
  | Decimal.D4 l => of_uint_acc l (add 1~0~0 (mul ten acc))
  | Decimal.D5 l => of_uint_acc l (add 1~0~1 (mul ten acc))
  | Decimal.D6 l => of_uint_acc l (add 1~1~0 (mul ten acc))
  | Decimal.D7 l => of_uint_acc l (add 1~1~1 (mul ten acc))
  | Decimal.D8 l => of_uint_acc l (add 1~0~0~0 (mul ten acc))
  | Decimal.D9 l => of_uint_acc l (add 1~0~0~1 (mul ten acc))
  end.

Fixpoint of_uint (d:Decimal.uint) : N :=
  match d with
  | Decimal.Nil => N0
  | Decimal.D0 l => of_uint l
  | Decimal.D1 l => Npos (of_uint_acc l 1)
  | Decimal.D2 l => Npos (of_uint_acc l 1~0)
  | Decimal.D3 l => Npos (of_uint_acc l 1~1)
  | Decimal.D4 l => Npos (of_uint_acc l 1~0~0)
  | Decimal.D5 l => Npos (of_uint_acc l 1~0~1)
  | Decimal.D6 l => Npos (of_uint_acc l 1~1~0)
  | Decimal.D7 l => Npos (of_uint_acc l 1~1~1)
  | Decimal.D8 l => Npos (of_uint_acc l 1~0~0~0)
  | Decimal.D9 l => Npos (of_uint_acc l 1~0~0~1)
  end.

Fixpoint to_little_uint p :=
  match p with
  | 1 => Decimal.D1 Decimal.Nil
  | p~1 => Decimal.Little.succ_double (to_little_uint p)
  | p~0 => Decimal.Little.double (to_little_uint p)
  end.

Definition to_uint p := Decimal.rev (to_little_uint p).

End Pos.
