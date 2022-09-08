From Malfunction Require InterpreterStrict.
From Malfunction Require Import Interpreter Malfunction.
Require Import ZArith String.

Notation sinterpret := InterpreterStrict.interpret.
Notation svalue := InterpreterStrict.value.

Definition Array_map {A B} (f : A -> B) (a : PArray.array A) :=
  Array_of_list (f (PArray.default a))
                (List.map f (List.map (fun n => PArray.get a (Uint63.of_Z (Z.of_nat n))) (List.seq 0 (Z.to_nat (Uint63.to_Z (PArray.length a)))))).

#[bypass_check(guard)]
Fixpoint vtrans (s : svalue) : value :=
  match s with
  | InterpreterStrict.Block (tag, vals) => Block (tag, Array_map vtrans vals)
  | InterpreterStrict.Vec (ty, vals) => Vec (ty, Array_map vtrans vals)
  | InterpreterStrict.Func (x, locals, e) => Func (fun v => interpret (Ident.Map.add x v (fun x => vtrans (locals x))) (fun _ => fail "no globals") e)
  | InterpreterStrict.value_Int (ty, i) => value_Int (ty, i)
  | InterpreterStrict.Float f => Float f
  | InterpreterStrict.Thunk v => Thunk (vtrans v)
  | InterpreterStrict.fail x => fail x
  end.


Theorem interpreter_correct :
  interpret
