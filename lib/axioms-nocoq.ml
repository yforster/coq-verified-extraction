
(* booleans need to be flipped, because
     Inductive bool : Type := true | false
   and
     type bool = false | true
*)

let flip f x1 x2 = not (f x1 x2)

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lsl = Uint63.l_sl

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lsr = Uint63.l_sr

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_asr = Uint63.a_sr

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_land = Uint63.l_and

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lor = Uint63.l_or

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lxor = Uint63.l_xor

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_add = Uint63.add

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_sub = Uint63.sub

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_mul = Uint63.mul

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_mulc = Uint63.mulc

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_div = Uint63.div

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_mod = Uint63.rem

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_divs = Uint63.divs

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_mods = Uint63.rems

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_eqb = flip Uint63.equal 

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_ltb = flip Uint63.lt

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_leb = flip Uint63.le 

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_ltsb = flip Uint63.lts 

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_lesb = flip Uint63.les

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_addc = Uint63.addc

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_addcarryc = Uint63.addcarryc

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_subc = Uint63.subc

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_subcarryc = Uint63.subcarryc

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_diveucl = Uint63.diveucl

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_diveucl_21 = Uint63.div21

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_addmuldiv = Uint63.addmuldiv

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_compare = fun x y -> let c = Uint63.compare x y in if c = 0 then 0 else if c < 0 then 1 else 2 (* 0 = Eq, 1 = Lt, 2 = Gt *)

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_compares = fun x y -> let c = Uint63.compares x y in if c = 0 then 0 else if c < 0 then 1 else 2 (* 0 = Eq, 1 = Lt, 2 = Gt *)

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_head0 = Uint63.head0

let def_Coq_Numbers_Cyclic_Int63_PrimInt63_tail0 = Uint63.tail0

(* (\* Variant float_class : Set := *\) *)
(* (\*     PNormal : FloatClass.float_class *\) *)
(* (\*   | NNormal : FloatClass.float_class *\) *)
(* (\*   | PSubn : FloatClass.float_class *\) *)
(* (\*   | NSubn : FloatClass.float_class *\) *)
(* (\*   | PZero : FloatClass.float_class *\) *)
(* (\*   | NZero : FloatClass.float_class *\) *)
(* (\*   | PInf : FloatClass.float_class *\) *)
(* (\*   | NInf : FloatClass.float_class *\) *)
(* (\*   | NaN : FloatClass.float_class. *\) *)

(* (\* type float_class = *\) *)
(* (\*   | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN *\) *)

(* let def_Coq_Floats_PrimFloat_classify = Float64.classify *)

(* let def_Coq_Floats_PrimFloat_abs = Float64.abs *)

(* let def_Coq_Floats_PrimFloat_sqrt = Float64.sqrt *)

(* let def_Coq_Floats_PrimFloat_opp = Float64.opp *)

(* let def_Coq_Floats_PrimFloat_eqb = flip Float64.eq *)

(* let def_Coq_Floats_PrimFloat_ltb = flip Float64.lt *)

(* let def_Coq_Floats_PrimFloat_leb = flip Float64.le *)

(* (\* Variant float_comparison : Set := *\) *)
(* (\*     FEq : PrimFloat.float_comparison *\) *)
(* (\*   | FLt : PrimFloat.float_comparison *\) *)
(* (\*   | FGt : PrimFloat.float_comparison *\) *)
(* (\*   | FNotComparable : PrimFloat.float_comparison. *\) *)

(* (\* type float_comparison = FEq | FLt | FGt | FNotComparable *\) *)

(* let def_Coq_Floats_PrimFloat_compare = Float64.compare  *)

(* let def_Coq_Floats_PrimFloat_Leibniz_eq = Float64.equal *)

(* let def_Coq_Floats_PrimFloat_mul = Float64.mul *)

(* let def_Coq_Floats_PrimFloat_add = Float64.add *)

(* let def_Coq_Floats_PrimFloat_sub = Float64.sub *)

(* let def_Coq_Floats_PrimFloat_div = Float64.div *)

(* let def_Coq_Floats_PrimFloat_of_uint63 = Float64.of_uint63 *)

(* let def_Coq_Floats_PrimFloat_normfr_mantissa = Float64.normfr_mantissa *)

(* let def_Coq_Floats_PrimFloat_frshiftexp = Float64.frshiftexp *)

(* let def_Coq_Floats_PrimFloat_ldshiftexp = Float64.ldshiftexp *)

(* let def_Coq_Floats_PrimFloat_next_up = Float64.next_up *)

(* let def_Coq_Floats_PrimFloat_next_down = Float64.next_down *)

let rec print_obj x = 
  let x = Obj.magic x in
  if Obj.is_block x then let size = Obj.size x in
                           if Obj.tag x = 247 then
                              Printf.printf "POINTER%!"
                           else
                           (Printf.printf ("(block[%i] (tag %i) %!") (Obj.size x) (Obj.tag x) ;
                           for i = 0 to size - 1 do
                             print_obj (Obj.field x i)
                           done;
                           Printf.printf ")")
  else  Printf.printf ("%i %!") x

let def_print_arg na x = 
  Printf.printf "Function %s called %!" na ; print_obj x ; Printf.printf "\n%!"

let def_print_string = fun x -> Printf.printf ("Global constant %s\n%!") x

let print_hello = fun (x : unit) -> Printf.printf ("Hello\n%!")
