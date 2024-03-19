From Malfunction.Plugin Require Loader.
From Coq.Floats Require Import PrimFloat.

(* FIXNE: compare is wrong todo *)
Verified Extract Constants [ 
  Coq.Floats.PrimFloat.float erased,
  Coq.Floats.PrimFloat.compare => "Float64.compare",
  Coq.Floats.PrimFloat.eqb => "Float64.equal",
  Coq.Floats.PrimFloat.ltb => "Float64.lt",
  Coq.Floats.PrimFloat.leb => "Float64.le",
  Coq.Floats.PrimFloat.frshiftexp => "Float64.frshiftexp",
  Coq.Floats.PrimFloat.ldshiftexp => "Float64.ldshiftexp",
  Coq.Floats.PrimFloat.normfr_mantissa => "Float64.normfr_mantissa",
  Coq.Floats.PrimFloat.classify => "Float64.classify",
  Coq.Floats.PrimFloat.abs => "Float64.abs",
  Coq.Floats.PrimFloat.sqrt => "Float64.sqrt",
  Coq.Floats.PrimFloat.opp => "Float64.opp",
  Coq.Floats.PrimFloat.div => "Float64.div",
  Coq.Floats.PrimFloat.mul => "Float64.mul",
  Coq.Floats.PrimFloat.add => "Float64.add",
  Coq.Floats.PrimFloat.sub => "Float64.sub",
  Coq.Floats.PrimFloat.of_uint63 => "Float64.of_uint63",
  Coq.Floats.PrimFloat.next_up => "Float64.next_up",
  Coq.Floats.PrimFloat.next_down => "Float64.next_down" ]
Packages [ "coq-core.kernel" ].
