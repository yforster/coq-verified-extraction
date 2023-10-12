
let def_Coq_Floats_PrimFloat_normfr_mantissa = Float64.normfr_mantissa

let def_Coq_Floats_PrimFloat_frshiftexp = Float64.frshiftexp

let def_Coq_Floats_PrimFloat_abs = Float64.abs

let def_Coq_Floats_PrimFloat_ltb = fun f1 f2 -> not (Float64.lt f1 f2)

let def_Coq_Floats_PrimFloat_eqb = fun f1 f2 -> not (Float64.eq f1 f2)

let def_Coq_Floats_PrimFloat_div = Float64.div

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_leb = fun i1 i2 -> not (Uint63.le i1 i2)

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lsr = Uint63.l_sr

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lsl = Uint63.l_sl

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_land = Uint63.l_and

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lor = Uint63.l_or

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_sub = Uint63.sub

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_eqb f1 f2 = not (Uint63.equal f1 f2)

(* let print_kername = fun x -> print_string (Metadef_Coq_template_plugin.Caml_bytestring.caml_string_of_bytestring (snd x)) ; Printf.printf ("\n%!") *)


let rec print_obj x =
  if Obj.is_block x then let size = Obj.size x in
                           Printf.printf ("Block with tag %i of size %i\n%!") (Obj.tag x) (Obj.size x) ;
                           for i = 0 to size - 1 do
                             print_obj (Obj.field x i)
                           done
  else  Printf.printf ("Integer: %c\n%!") (Obj.magic x)
 (* = fun x -> Printf.printf ("%i\n%!") (Obj.tag x) ; Printf.printf ("%b\n%!") (Obj.is_block x) ; if Obj.is_block x then Printf.printf ("Size: %i\n%!") (Obj.size x) else () *)

(* let print_obj = fun x -> Printf.printf ("%i\n%!") (Obj.tag x) ; Printf.printf ("%b\n%!") (Obj.is_block x) ; if Obj.is_block x then Printf.printf ("Size: %i\n%!") (Obj.size x) else () *)

let print_int = fun x -> Printf.printf ("%i\n%!") x

(* let print = fun x -> print_string (Metadef_Coq_template_plugin.Caml_bytestring.caml_string_of_bytestring x) ; Printf.printf ("\n%!") *)
