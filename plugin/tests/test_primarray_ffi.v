From Malfunction Require Import utils_array.
From Malfunction.Plugin Require Import Extract.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Common Require Import Primitive.
From Malfunction.Plugin Require Import OCamlFFI.

Set MetaCoq Extraction Build Directory "_build".

(* Primitives *)

From Coq Require Import PrimInt63 Uint63 PArray.

Definition val : array nat := PArray.make 3 2.

Definition gettest : nat := PArray.get val 2. 
Definition settest : array nat := PArray.set val 2 1. 
Definition getsettest : nat := PArray.get settest 2.

Set Warnings "-primitive-turned-into-axiom".

Definition prim_array_get := (print_int (int_of_nat gettest)).
Definition prim_array_get_set := (print_int (int_of_nat getsettest)).

MetaCoq Extraction -fmt -typed -compile-with-coq val "val.mlf".
MetaCoq Extraction -fmt -typed -compile-with-coq -run prim_array_get "prim_array_get.mlf".
MetaCoq Extraction -fmt -typed -compile-with-coq -run prim_array_get_set "prim_array_get_set.mlf".