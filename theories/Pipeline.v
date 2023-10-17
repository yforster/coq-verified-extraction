(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Utils Require Import bytestring utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq Require Import ETransform EConstructorsAsBlocks.
From MetaCoq.Erasure Require Import EWcbvEvalNamed.
From MetaCoq.ErasurePlugin Require Import Erasure ErasureCorrectness.
From Malfunction Require Import CeresSerialize CompileCorrect.
Import PCUICProgram.
(* Import TemplateProgram (template_eta_expand).
 *)
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Transform.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Require Malfunction.SemanticsSpec.
From Malfunction Require Import Compile Serialize.

Program Definition name_annotation (efl := extraction_env_flags) : Transform.t EAst.global_declarations (list (Kernames.kername × EAst.global_decl))
  EAst.term EAst.term _ EWcbvEvalNamed.value
  (EProgram.eval_eprogram extraction_wcbv_flags) (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) :=
  {| name := "annotate names";
      pre := fun p =>  EProgram.wf_eprogram efl p ;
      transform p _ := (annotate_env [] p.1, annotate [] p.2) ;
      post := fun p => EProgram.wf_eprogram named_extraction_env_flags p ;
      obseq p _ p' v v' := ∥ represents_value v' v∥ |}.
Next Obligation.
  destruct input as [Σ s].
  destruct p as [HΣ Hs].
  split.
  2: now eapply wellformed_annotate with (Γ := []).
  cbn in *. clear Hs.
  induction HΣ.
  - econstructor.
  - cbn in *. destruct d as [ [[]]| ]; cbn in *; econstructor; eauto.
    cbn. now eapply wellformed_annotate with (Γ := []).
    { clear - H0. induction H0; (try destruct x as [? [ [[]]| ]]); cbn in *; econstructor; eauto. }
    { clear - H0. induction H0; (try destruct x as [? [ [[]]| ]]); cbn in *; econstructor; eauto. }
Qed.
Next Obligation.
  red. intros. red in H. sq.
  unshelve eapply eval_to_eval_named_full in H as [v_ Hv].
  - shelve.
  - exists v_. repeat split; sq. cbn. eapply Hv. eapply Hv.
  - eapply pr.
  - destruct pr. clear H1 H.
    generalize (@nil Kernames.ident) at 2. induction H0; cbn; intros.
    + econstructor.
    + destruct d. destruct c. destruct cst_body.
      * econstructor; eauto. cbn in *. eapply sunny_subset. eapply sunny_annotate.
        intros ? [].
      * econstructor; eauto. cbn in *. eauto.
      * econstructor; eauto. cbn in *. eauto.
  - destruct pr. clear - H0.
    induction p.1.
    + cbn. econstructor.
    + cbn. destruct a as [? [ [[]]| ]]; intros; econstructor; eauto; cbn; eauto.
      2-4: eapply IHg; now invs H0.
      split; eauto. eexists. split. cbn. reflexivity.
      eapply nclosed_represents; cbn. invs H0. cbn in *. eauto.
  - eapply pr.
Qed.

Program Definition compile_to_malfunction (efl : EWellformed.EEnvFlags) `{SemanticsSpec.Heap}:
  Transform.t (list (Kernames.kername × EAst.global_decl)) _ _ _
    EWcbvEvalNamed.value SemanticsSpec.value
    (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) (fun _ _ => True) :=
  {| name := "compile to Malfunction";
      pre := fun p =>   EWellformed.wf_glob p.1 /\ EWellformed.wellformed p.1 0 p.2;
      transform p _ := compile_program p ;
      post := fun p =>  True ;
      obseq p _ p' v v' := v' = CompileCorrect.compile_value p.1 v
  |}.
Next Obligation.
  rename H into HP; rename H0 into HH. 
  red. intros. sq.
  eapply compile_correct in H.
  - eauto.
  - intros. todo "wf".
  - intros.  todo "wf".
  - intros. todo "wf".
    Unshelve. all: todo "wf".
Qed.

Program Definition verified_malfunction_pipeline (efl := EWellformed.all_env_flags) `{SemanticsSpec.Heap}:
 Transform.t global_env_ext_map _ _ _ _ SemanticsSpec.value 
             PCUICTransform.eval_pcuic_program
             (fun _ _ => True) :=
  verified_erasure_pipeline ▷
  implement_box_transformation (has_app := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl) ▷
  name_annotation ▷
  compile_to_malfunction _.
Next Obligation.
  todo "wf".
Qed.
Next Obligation.
  cbn in *. todo "wf".
Qed.
Next Obligation.
  todo "wf".
Qed.
Next Obligation.
  todo "wf".
Qed.
Next Obligation.
  todo "wf".
Qed.

Section malfunction_pipeline_theorem.

  Local Existing Instance SemanticsSpec.CanonicalHeap.

  Instance cf_ : checker_flags := extraction_checker_flags.
  Instance nf_ : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

  Variable HP : SemanticsSpec.Pointer.
  Variable HH : SemanticsSpec.Heap.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.

  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable typing : PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args).

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Normalisation :  PCUICSN.NormalizationIn Σ.

  Lemma precond_ : pre verified_erasure_pipeline (Σ, t).
  Proof.
    eapply precond; eauto. todo "wf".
  Qed.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Let Σ_t := (transform verified_malfunction_pipeline (Σ, t) precond_).1.

  Program Definition Σ_b := (transform (verified_erasure_pipeline ▷ name_annotation) (Σ, t) precond_).1.
  Next Obligation.
    todo "admit".
  Qed.

  Let t_t := (transform verified_malfunction_pipeline (Σ, t) precond_).2.

  Fixpoint compile_value_mf (Σb : list (Kernames.kername × EAst.global_decl)) (t : PCUICAst.term) (acc : list SemanticsSpec.value) : SemanticsSpec.value :=
    match t with
    | PCUICAst.tApp f a => compile_value_mf Σb f (acc ++ [compile_value_mf Σb a []])
    | PCUICAst.tConstruct i n _ => SemanticsSpec.Block (int_of_nat n, acc)
    | _ => SemanticsSpec.not_evaluated
    end.

  Variables (Σ' : _) (HΣ' : (forall (c : Kernames.kername) (decl : EAst.constant_body) 
                               (body : EAst.term) (v : EWcbvEvalNamed.value),
                                EGlobalEnv.declared_constant Σ_b c decl ->
                                EAst.cst_body decl = Some body ->
                                EWcbvEvalNamed.eval Σ_b [] body v ->
                                In (Kernames.string_of_kername c, compile_value Σ_b v) Σ')).

  Lemma verified_malfunction_pipeline_theorem h :
    ∥ SemanticsSpec.eval [] (fun _ => SemanticsSpec.not_evaluated) h t_t h (compile_value_mf Σ_b v [])∥.
  Proof.
    unshelve epose proof (verified_erasure_pipeline_theorem _ _ _ _ _ _ _ _ _ _ _ _ _ Heval); eauto.
    pose proof compile_correct.
    sq.
  Admitted.

  (* Lemma verified_erasure_pipeline_lambda : *)
  (*   PCUICAst.isLambda t -> EAst.isLambda t_t. *)
  (* Proof. *)
  (*   unfold t_t. clear. *)
  (* Admitted. *)

End malfunction_pipeline_theorem.

About verified_malfunction_pipeline_theorem.

Program Definition malfunction_pipeline (efl := EWellformed.all_env_flags) `{SemanticsSpec.Heap}:
 Transform.t _ _ _ _ _ _ TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  pre_erasure_pipeline ▷ verified_malfunction_pipeline.

Local Existing Instance SemanticsSpec.CanonicalHeap.

Definition compile_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program) `{SemanticsSpec.Heap}
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p =>(@to_string _ Serialize_program p)) p'.

About compile_malfunction.

Definition compile_module_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program) `{SemanticsSpec.Heap}
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p => (@to_string _ Serialize_module p)) p'.
