From Malfunction.Plugin Require Import Extract.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Common Require Import Primitive.
From Malfunction.Plugin Require Import OCamlFFI.

Set MetaCoq Extraction Build Directory "_build".

(* Primitives *)

From Coq Require Import PrimInt63 Uint63.

Definition foo : int := (80 + 30)%uint63. 

Set Warnings "-primitive-turned-into-axiom".

Definition prog := (print_int foo).

MetaCoq Extraction -fmt -compile-with-coq -run foo "prim.mlf".