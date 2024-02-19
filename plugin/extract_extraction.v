From Malfunction.Plugin Require Import Extract.
From Malfunction Require Import Pipeline.

Set MetaCoq Extraction Build Directory "_build".

(* Malfunction.Plugin.Extract binds all primitives to OCaml externals *)
Set Warnings "-primitive-turned-into-axiom".

(* MetaCoq Run Print mli compile_malfunction_gen. *)
MetaCoq Extraction -fmt compile_malfunction_gen "compile_malfunction.mlf".
