Require Import MetaCoq.Utils.bytestring.
From Malfunction.VerifiedPlugin Require Import Loader.
From Malfunction.VerifiedPlugin Require Import PrimInt63 PrimFloat.

Axiom (print_int : PrimInt63.int -> unit).
Axiom (print_float : Coq.Floats.PrimFloat.float -> unit).
Axiom (print_string : string -> unit).
Axiom (print_newline : unit -> unit).
Axiom (print_endline : string -> unit).

Verified Extract Constants [ 
  print_int => "Stdlib.print_int",
  print_float => "Stdlib.print_float",
  print_string => "Coq_verified_extraction_ocaml_ffi__OCaml_stdlib.print_string",
  print_newline => "Coq_verified_extraction_ocaml_ffi__OCaml_stdlib.print_newline",
  print_endline => "Coq_verified_extraction_ocaml_ffi__OCaml_stdlib.print_endline" ]
Packages [ "coq_verified_extraction_ocaml_ffi" ].