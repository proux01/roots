(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for binary natural numbers *)

From Coq Require Export BinNums.
From Coq Require Export BinPos.
From Coq Require Export BinNat.
From Coq Require Export Nnat.
From Coq Require Export Ndiv_def.
From Coq Require Export Nsqrt_def.
From Coq Require Export Ngcd_def.
From Coq Require Export Ndigits.

(** [N] contains an [order] tactic for natural numbers *)

(** Note that [N.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Local Open Scope N_scope.

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 N.order.
 Defined.
End TestOrder.
