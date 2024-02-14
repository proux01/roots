(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for manipulating integers based on binary encoding *)

From Coq.ZArith Require Export ZArith_base.

(** Extra definitions *)

From Coq.ZArith Require Export Zpow_def.

(** Extra modules using [Ring]. *)

From Coq Require Export OmegaLemmas.
From Coq Require Export PreOmega.
From Coq Require Export ZArith_hints.
From Coq Require Export Zcomplements.
Require Export Zpower.
From Coq Require Export Zdiv.
Require Export Zbitwise.

Export ZArithRing.
