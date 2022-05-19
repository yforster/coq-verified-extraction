From Coq Require Import String.
From Ceres Require Import Ceres.
From Malfunction Require Import Pipeline Serialize.

From MetaCoq Require Import ETransform Transform bytestring.
From MetaCoq.Template Require Import All Loader.

Import Transform.

Definition compile_malfunction {cf : config.checker_flags} (p : Ast.Env.program)
  : String.string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs to_string  p'.

Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).

MetaCoq Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv delta in (

                   ack 3 5

               ))
        in exact t).
Compute (compile_malfunction cbv_ack35).

