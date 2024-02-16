(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Coq Require Export BinNums.
From Coq Require Import MyBinPosDef.

(**********************************************************************)
(** * Binary natural numbers, definitions of operations *)
(**********************************************************************)

Module N.

(** ** The successor of a [N] can be seen as a [positive] *)

Definition succ_pos (n : N) : positive :=
 match n with
   | N0 => xH
   | Npos p => Pos.succ p
 end.

(** Operation over bits of a [N] number. *)

(** Logical [or] *)

Definition lor n m :=
 match n, m with
   | N0, _ => m
   | _, N0 => n
   | Npos p, Npos q => Npos (Pos.lor p q)
 end.

(** Logical [and] *)

Definition land n m :=
 match n, m with
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Pos.land p q
 end.

(** Logical [diff] *)

Definition ldiff n m :=
 match n, m with
  | N0, _ => N0
  | _, N0 => n
  | Npos p, Npos q => Pos.ldiff p q
 end.

(** [xor] *)

Definition lxor n m :=
  match n, m with
    | N0, _ => m
    | _, N0 => n
    | Npos p, Npos q => Pos.lxor p q
  end.

End N.
