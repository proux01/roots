(** Extraction of [nat] into Haskell's [Int] *)

From Stdlib Require Extraction.

From Stdlib Require Import Arith.
From Stdlib Require Import ExtrHaskellNatNum.

(**
 * Disclaimer: trying to obtain efficient certified programs
 * by extracting [nat] into [Int] is definitively *not* a good idea.
 * See comments in [ExtrOcamlNatInt.v].
 *)

Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
