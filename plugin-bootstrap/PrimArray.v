From Malfunction.Plugin Require Loader PrimInt63.
From Coq Require Import PArray.

(* This only interfaces with primitive integers, so no wrapping is needed. *)
(* However the polymorphic functions should be masked to remove type argument 
  applications *)

MetaCoq Extract Constants [ 
  Coq.Array.PArray.array erased,
  Coq.Array.PArray.make => "Parray.make",
  Coq.Array.PArray.get => "Parray.get",
  Coq.Array.PArray.default => "Parray.default",
  Coq.Array.PArray.set => "Parray.set",
  Coq.Array.PArray.length => "Parray.length_int",
  Coq.Array.PArray.copy => "Parray.copy" ]
Packages [ "coq-core.kernel" ].
