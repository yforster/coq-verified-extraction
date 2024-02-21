From Malfunction.Plugin Require Import Extract.
From MetaCoq.Utils Require Import bytestring MCString.
Local Open Scope bs. (* bytestrings *)

Set MetaCoq Extraction Build Directory "_build".

Definition test := coq_msg_info "Hello world!".

(* Set Debug "metacoq-extraction". *)
MetaCoq Extraction -fmt -compile-plugin -run test "test_plugin.mlf".
