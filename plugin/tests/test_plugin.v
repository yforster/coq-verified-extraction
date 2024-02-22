From Malfunction.Plugin Require Import Extract.
From MetaCoq.Utils Require Import bytestring MCString.
Local Open Scope bs. (* bytestrings *)

Set MetaCoq Extraction Build Directory "_build".

Definition test (x : unit) := coq_msg_info "Hello world!".

Set Debug "metacoq-extraction".
Set Warnings "-primitive-turned-into-axiom".

From Coq Require Import PrimFloat.
Definition test_float (thunk : unit) : float := abs (-1.4%float).
MetaCoq Extraction -typed -unsafe -time -fmt -compile-plugin -run (abs 1.5%float).

(* Pure running time of the compiled code *)
Time MetaCoq Eval test_float.
Time MetaCoq Eval test_float.
