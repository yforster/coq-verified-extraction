From VerifiedExtraction
  Require Import Loader.

Definition function_or_nat
  : forall (b:bool), if b then bool -> bool else nat :=
  fun b =>
    match b with
    | true => fun x => x
    | false => S O
    end.

Definition function := function_or_nat true.

Verified Extraction
  function.
MetaCoq Run Print mli function.
(* type bool = True  | False  *)
(* val function : bool -> bool *)

Extraction function_or_nat.

Definition apply_function_or_nat : forall b : bool, (if b then bool -> bool else nat) -> bool :=
  fun b => match b with true => fun f => f true | false => fun _ => false end.

Definition assumes_purity : (unit -> bool) -> bool :=
  fun f => apply_function_or_nat (f tt) (function_or_nat (f tt)).

Require Import Extraction.
Recursive Extraction assumes_purity.

MetaCoq Run Print mli assumes_purity.
(* type unit = Tt  *)
(* type bool = True  | False  *)
(* val assumes_purity : (unit -> bool) (* higher-order functions are not safe to extract *)  -> bool *)
