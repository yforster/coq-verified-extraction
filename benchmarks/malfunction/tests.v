Require Import MetaCoq.VerifiedExtraction.Benchmarks.lib.tests.
From Malfunction Require Import Loader.
From MetaCoq.Utils Require Import bytestring.

Open Scope bs.

Eval compute in "Compiling demo0".

MetaCoq Extraction demo0 "demo0.mlf".

Eval compute in "Compiling demo1".

MetaCoq Extraction demo1 "demo1.mlf".

Eval compute in "Compiling demo2".

MetaCoq Extraction demo2 "demo2.mlf".

Eval compute in "Compiling demo3".

MetaCoq Extraction demo3 "demo3.mlf".

Eval compute in "Compiling list_sum".

MetaCoq Extraction list_sum "list_sum.mlf".

Eval compute in "Compiling vs_easy".

MetaCoq Extraction vs_easy "vs_easy.mlf".

Eval compute in "Compiling vs_hard".

MetaCoq Extraction vs_hard "vs_hard.mlf".

Eval compute in "Compiling binom".

MetaCoq Extraction binom "binom.mlf".

(* Eval compute in "Compiling lazy factorial". *)

(* (* CertiCoq Compile -O 1 lazy_factorial. *)
(* CertiCoq Compile -ext "_opt" lazy_factorial. *)
(* CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" lazy_factorial. *) *)
(* (* CertiCoq Compile -O 0 -cps -ext "_cps" demo1. *) *)
(* (* CertiCoq Compile -cps -ext "_cps_opt" demo1. *) *)

Eval compute in "Compiling color".

MetaCoq Extraction color "color.mlf".

(* (* Don't compile slow sha *) *)
(* (* Eval compute in "Compiling sha". *) *)

(* (* CertiCoq Compile -cps -ext "_cps" sha. *) *)
(* (* CertiCoq Compile sha. *) *)
(* (* CertiCoq Compile -O 1 -cps -ext "_cps_opt" sha. *) *)
(* (* CertiCoq Compile -O 1 -ext "_opt" sha. *) *)

Eval compute in "Compiling sha_fast".

MetaCoq Extraction sha_fast "sha_fast.mlf".
