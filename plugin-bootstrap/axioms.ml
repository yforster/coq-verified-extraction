
let coq_Floats_PrimFloat_normfr_mantissa = Float64.normfr_mantissa

let coq_Floats_PrimFloat_frshiftexp = Float64.frshiftexp

let coq_Floats_PrimFloat_abs = Float64.abs

let coq_Floats_PrimFloat_ltb = fun f1 f2 -> not (Float64.lt f1 f2)

let coq_Floats_PrimFloat_eqb = fun f1 f2 -> not (Float64.eq f1 f2)

let coq_Floats_PrimFloat_div = Float64.div

let coq_Numbers_Cyclic_Int63_PrimInt63_lsr = Uint63.l_sr

let coq_Numbers_Cyclic_Int63_PrimInt63_lsl = Uint63.l_sl

let coq_Numbers_Cyclic_Int63_PrimInt63_land = Uint63.l_and

let coq_Numbers_Cyclic_Int63_PrimInt63_lor = Uint63.l_or

let coq_Numbers_Cyclic_Int63_PrimInt63_sub = Uint63.sub

let coq_Numbers_Cyclic_Int63_PrimInt63_eqb f1 f2 = not (Uint63.equal f1 f2)
