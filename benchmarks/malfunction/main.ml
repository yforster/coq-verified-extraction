open Printf
open Unix

let demo0_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
    (* Printf.printf "%i\n" ( List.length ( *)
     Demo0.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_demo0 ()
    (* )) *)
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "demo0 execution time: %f miliseconds\n" (t'*.1000.0)

let demo1_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
    Demo1.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_demo1 ()
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "demo1 execution time: %f miliseconds\n" (t'*.1000.0)

let demo2_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
    Demo2.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_demo2 ()
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "demo2 execution time: %f miliseconds\n" (t'*.1000.0)
    
let list_sum_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
     List_sum.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_list_sum ()
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "list_sum execution time: %f miliseconds\n" (t'*.1000.0)


let vs_easy_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
    Vs_easy.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_vs_easy ()
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "vs_easy execution time: %f miliseconds\n" (t'*.1000.0)

(* let vs_hard_main = *)
(*   let n = int_of_string Sys.argv.(1) in *)
(*   let t = Unix.gettimeofday () in *)
(*   for i = 1 to n do *)
(*     Vs_hard.vs_hard Tt *)
(*   done; *)
(*   let t' = Unix.gettimeofday () -. t in *)
(*   Printf.printf "vs_hard execution time: %f miliseconds\n" (t'*.1000.0) *)

let binom_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
    Binom.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_binom ()
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "binom execution time: %f miliseconds\n" (t'*.1000.0)

(* Color does not typecheck in OCaml *)
let color_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 0 to 10 * n do
    Color.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_color ()
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "color xecution time: %f seconds\n" t'

(* let sha_main =  
 *   let n = int_of_string Sys.argv.(1) in
 *   let t = Unix.gettimeofday () in
 *   for i = 1 to n do
 *     Sha.sha Tt
 *   done;
 *   let t' = Unix.gettimeofday () -. t in
 *   Printf.printf "sha execution time: %f seconds\n" t' *)

let sha_fast_main =
  let n = int_of_string Sys.argv.(1) in
  let t = Unix.gettimeofday () in
  for i = 1 to n do
    (* Printf.printf "%i\n" (List.length ( *)
        Sha_fast.def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_sha_fast ()
   (* ) ) *)
  done;
  let t' = Unix.gettimeofday () -. t in
  Printf.printf "sha_fast execution time: %f miliseconds\n" (t'*.1000.0)
