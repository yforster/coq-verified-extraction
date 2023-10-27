let main =
  Axioms.print_obj (Obj.magic (Append.append1_and_run [1] 1));
  Printf.printf "\n%!"
