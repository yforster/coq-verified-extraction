(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq Require Import Common.Transform bytestring config utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq Require Import ETransform EConstructorsAsBlocks.
From MetaCoq.Erasure Require Import EWcbvEvalNamed Erasure.
From Ceres Require Import Ceres.
Import PCUICProgram.
(* Import TemplateProgram (template_eta_expand).
 *)
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Transform.

Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Require Malfunction.SemanticsSpec Malfunction.Semantics.
From Malfunction Require Import Compile Serialize.

Program Definition malfunction_pipeline (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program Malfunction.program
             Ast.term Malfunction.program
             TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  erasure_pipeline_fast ▷ 
  _.
Next Obligation.
  intros. unshelve econstructor.
  - exact (fun _ => True).
  - cbn. intros [Σ s] _. 
    refine (compile_program ( (annotate_env [] Σ, annotate [] s))).
  - exact (fun _ => True).
  - exact (fun _ _ _ _ => True).
  - exact "malfunction"%bs.
  - cbn. eauto.
  - cbn. econstructor. refine ([], Malfunction.Mvar _). red. econstructor. eauto.
Defined.

Definition compile_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p =>(@to_string _ Serialize_program p)) p'.

Definition compile_module_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p => (@to_string _ Serialize_module p)) p'.