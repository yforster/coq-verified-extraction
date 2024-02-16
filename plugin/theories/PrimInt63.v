From Malfunction.Plugin Require Loader.
From Coq.Numbers.Cyclic.Int63 Require Import PrimInt63.

(** Primitives *)

MetaCoq Extract Constants [
  Coq.Numbers.Cyclic.Int63.PrimInt63.add => "+",
  Coq.Numbers.Cyclic.Int63.PrimInt63.sub => "Uint63.sub", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mul => "Uint63.mul", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.div => "Uint63.div", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mod => "Uint63.rem", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lsl => "Uint63.l_sl", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lsr => "Uint63.l_sr", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.land => "Uint63.l_and",
  Coq.Numbers.Cyclic.Int63.PrimInt63.lxor => "Uint63.l_xor",
  Coq.Numbers.Cyclic.Int63.PrimInt63.lor => "Uint63.l_or",
  Coq.Numbers.Cyclic.Int63.PrimInt63.asr => "Uint63.a_sr",
  Coq.Numbers.Cyclic.Int63.PrimInt63.head0 => "Uint63.head0", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.tail0 => "Uint63.tail0", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.eqb => "Uint63.equal",
  Coq.Numbers.Cyclic.Int63.PrimInt63.compare => "Uint63.compare", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.compares => "Uint63.compares", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addc => "Uint63.addc", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "Uint63.addcarryc", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.subc => "Uint63.subc",
  Coq.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "Uint63.subcarryc", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mulc => "Uint63.mulc", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.divs => "Uint63.divs", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.mods => "Uint63.rems", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "Uint63.div21", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.diveucl => "Uint63.diveucl", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "Uint63.addmuldiv", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.leb => "Uint63.le", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.ltb => "Uint63.lt", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.ltsb => "Uint63.lts", 
  Coq.Numbers.Cyclic.Int63.PrimInt63.lesb => "Uint63.les"
] Packages ["coq-core.kernel"].