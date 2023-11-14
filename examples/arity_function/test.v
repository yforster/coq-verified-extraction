From VerifiedExtraction
  Require Import Loader.

Definition arity_function
  : forall (b:bool), if b then nat else bool -> bool :=
  fun b =>
    match b with
    | true => S O
    | false => fun x => x
    end.

Definition main := arity_function false.

MetaCoq Verified Extraction
  main.
MetaCoq Run Print mli main.

