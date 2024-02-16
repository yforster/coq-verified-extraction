From Malfunction.Plugin Require Import Extract.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import bytestring.
From Malfunction.Plugin Require Import OCamlFFI.

Definition hello_world :=
  print_string "Hello world!"%bs.

MetaCoq Extraction -fmt -compile-with-coq -run 
  (print_string "hello_world"%bs)
  "hello_world.mlf".
