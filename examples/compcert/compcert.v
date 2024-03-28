From VerifiedExtraction Require Import Extraction.

From compcert Require Import Compiler.

Verified Extraction transf_c_program "compcert.mlf".

(* From MetaCoq Require Import bytestring. *)
(* Open Scope bs. *)
(* MetaCoq Run Print mli transf_c_program. *)
