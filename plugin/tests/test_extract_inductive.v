From Malfunction.Plugin Require Import Extract OCamlFFI.
From MetaCoq.Template Require Import All.
From Coq Require Import String.

Set MetaCoq Extraction Build Directory "_build".

MetaCoq Extract Inductives [
  bool => "bool" [ 1 0 ]
].

Definition coq_true := true.
Definition coq_false := false.
Set Debug "metacoq-extraction".
MetaCoq Extraction -time -verbose coq_true.
MetaCoq Extraction -unsafe coq_true.
MetaCoq Extraction coq_false.
MetaCoq Extraction -unsafe coq_false.

MetaCoq Extraction andb.
MetaCoq Extraction -unsafe andb.

MetaCoq Extract Inductives [
  option => "option" [ 1 0 ] (* This makes switches look at none cases before some *)
].

Definition test_get := (@option_get nat 0%nat None).
MetaCoq Extraction -unsafe test_get.


