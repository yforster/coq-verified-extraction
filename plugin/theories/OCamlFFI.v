Require Import MetaCoq.Utils.bytestring.
From Malfunction.Plugin Require Import Loader.

Axiom (print_string : string -> unit).
Axiom (print_newline : unit -> unit).
Axiom (print_endline : string -> unit).

MetaCoq Extract Constants [ 
  print_string => "Coq_metacoq_extraction_ocaml_ffi__OCaml_stdlib.print_string",
  print_newline => "Coq_metacoq_extraction_ocaml_ffi__OCaml_stdlib.print_newline",
  print_endline => "Coq_metacoq_extraction_ocaml_ffi__OCaml_stdlib.print_endline" ]
Packages [ "coq_metacoq_extraction_ocaml_ffi" ].