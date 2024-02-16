From Malfunction.Plugin Require Import Extract.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import bytestring.
From Malfunction.Plugin Require Import OCamlFFI.

Set MetaCoq Extraction Build Directory "_build".

Definition hello_world :=
  print_string "Hello world!"%bs.

MetaCoq Extraction -fmt -compile-with-coq -run hello_world "hello_world.mlf".
