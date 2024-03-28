From VerifiedExtraction Require Import Extraction.
From Malfunction Require Import Pipeline.

Set Verified Extraction Build Directory "_build".

(* Malfunction.Plugin.Extract binds all primitives to OCaml externals *)
Set Warnings "-primitive-turned-into-axiom".

(* MetaCoq Run Print mli compile_malfunction_gen. *)
Verified Extraction -fmt compile_malfunction_gen "compile_malfunction_bootstrap.mlf".