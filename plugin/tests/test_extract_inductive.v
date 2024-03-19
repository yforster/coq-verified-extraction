From Malfunction.Plugin Require Import Extract OCamlFFI.
From MetaCoq.Template Require Import All.
From Coq Require Import String.

Set Verified Extraction Build Directory "_build".

Verified Extract Inductives [
  bool => "bool" [ 1 0 ]
].

Definition coq_true := true.
Definition coq_false := false.
(* Set Debug "verified-extraction". *)
Verified Extraction -time -verbose coq_true.
Verified Extraction -unsafe coq_true.
Verified Extraction coq_false.
Verified Extraction -unsafe coq_false.

Verified Extraction andb.
Verified Extraction -unsafe andb.

Verified Extract Inductives [
  option => "option" [ 1 0 ] (* This makes switches look at none cases before some *)
].

Definition test_get := (@option_get nat 0%nat None).
Verified Extraction -unsafe test_get.


