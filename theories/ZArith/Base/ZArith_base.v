(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for manipulating integers based on binary encoding.
    These are the basic modules, required by [Omega] and [Ring] for instance.
    The full library is [ZArith]. *)

From Coq Require Export BinNums.
From Coq Require Export BinPos.
From Coq Require Export BinNat.
From Coq Require Export BinInt.
From Coq Require Export Zcompare.
From Coq Require Export Zorder.
From Coq Require Export Zeven.
From Coq Require Export Zminmax.
From Coq Require Export Zmin.
From Coq Require Export Zmax.
From Coq Require Export Zabs.
From Coq Require Export Znat.
From Coq Require Export auxiliary.
From Coq Require Export ZArith_dec.
From Coq Require Export Zbool.
From Coq Require Export Zmisc.
From Coq Require Export Wf_Z.

#[global]
Hint Resolve Z.le_refl Z.add_comm Z.add_assoc Z.mul_comm Z.mul_assoc Z.add_0_l
  Z.add_0_r Z.mul_1_l Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_add_distr_l
  Z.mul_add_distr_r: zarith.

Require Export Zhints.
