open Metacoq_template_plugin

let print_string str = 
  Printf.printf "Calling print_string from OCaml_stdlib";
  Stdlib.print_string (Caml_bytestring.caml_string_of_bytestring str)

let print_endline str =
  Stdlib.print_endline (Caml_bytestring.caml_string_of_bytestring str)

let print_newline () =
  Printf.printf "Calling print_newline from OCaml_stdlib\n%!";
  Stdlib.print_newline ()