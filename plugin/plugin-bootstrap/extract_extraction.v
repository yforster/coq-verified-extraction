From Malfunction.Plugin Require Import Loader.
From VerifiedExtraction Require Import PrimInt63 PrimFloat PrimArray.
From Malfunction Require Import Pipeline.
From Malfunction Require Import CoqMsgFFI.

Set Verified Extraction Build Directory "_build".

(* Malfunction.Plugin.Extract binds all primitives to OCaml externals *)
Set Warnings "-primitive-turned-into-axiom".

(* MetaCoq Run Print mli compile_malfunction_gen. *)
Verified Extraction -fmt compile_malfunction_gen "compile_malfunction.mlf".
