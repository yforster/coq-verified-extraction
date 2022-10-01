(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import Transform bytestring config utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require Import ETransform EConstructorsAsBlocks.
From MetaCoq.Erasure Require Import EWcbvEvalNamed.

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

Program Definition block_erasure_pipeline {guard : PCUICWfEnvImpl.abstract_guard_impl} (efl := EWellformed.all_env_flags) :=
  (* Casts are removed, application is binary, case annotations are inferred from the global environment *)
  template_to_pcuic_transform ▷
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform ▷
  (* Simulation of the guarded fixpoint rules with a single unguarded one: 
    the only "stuck" fixpoints remaining are unapplied. 
    This translation is a noop on terms and environments.  *)
  guarded_to_unguarded_fix (wcon := eq_refl) eq_refl ▷
  (* Remove all constructor parameters *)
  remove_params_optimization (wcon := eq_refl) ▷ 
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true ▷
  (* Remove all cases / projections on propositional content *)
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := EWellformed.all_env_flags) false ▷
  (* Constructors are treated as blocks, not higher-order *)
  @constructors_as_blocks_transformation _ _ _ _.
  (*  ▷
  (* Named variables and environment semantics *)
  named_environment_semantics_transformation. *)
Next Obligation.
  intros. cbn. MCUtils.todo "ok"%bs.
Qed.
Next Obligation.
  intros. cbn. MCUtils.todo "ok"%bs.
Qed.
Next Obligation.
  intros. cbn. MCUtils.todo "ok"%bs.
Qed.
Next Obligation.
  intros. cbn. MCUtils.todo "ok"%bs.
Qed.

Require Malfunction.SemanticsSpec Malfunction.Semantics.
Require Import Malfunction.Compile.

Program Definition malfunction_pipeline {guard : PCUICWfEnvImpl.abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program Malfunction.program
             Ast.term Malfunction.program
             TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  block_erasure_pipeline ▷ 
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