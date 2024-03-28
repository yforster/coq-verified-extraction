From VerifiedExtraction Require Import Extraction.

Verified Extraction (plus, mult).

Verified Extraction (1 + 2).
MetaCoq Run Print mli (1 + 2).

Verified Extraction (plus, mult) "multiple.mlf".
MetaCoq Run Print mli (plus, mult).
