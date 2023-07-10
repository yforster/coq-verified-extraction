(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Utils Require Import bytestring utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq Require Import ETransform EConstructorsAsBlocks.
From MetaCoq.Erasure Require Import EWcbvEvalNamed.
From MetaCoq.ErasurePlugin Require Import Erasure.
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

Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Require Malfunction.SemanticsSpec.
From Malfunction Require Import Compile Serialize.

Definition transform_compose
  {program program' program'' value value' value'' : Type}
  {eval : program -> value -> Prop} {eval' : program' -> value' -> Prop}
  {eval'' : program'' -> value'' -> Prop}
  (o : t program program' value value' eval eval')
  (o' : t program' program'' value' value'' eval' eval'')
  (pre : forall p : program', post o p -> pre o' p) :
  forall x p1, exists p3,
    transform (compose o o' pre) x p1 = transform o' (transform o x p1) p3.
Proof.  
  cbn. intros.
  unfold run, time.
  eexists; reflexivity.
Qed.

Section pipeline_theorem.

  Fixpoint compile_value_box (t : PCUICAst.term) (acc : list EAst.term) : EAst.term :=
    match t with
    | PCUICAst.tApp f a => compile_value_box f (acc ++ [compile_value_box a []])
    | PCUICAst.tConstruct i n _ => EAst.tConstruct i n acc
    | _ => EAst.tVar "error"
    end.

  Instance cf : checker_flags := extraction_checker_flags.
  Instance nf : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

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

  Lemma precond : pre verified_erasure_pipeline (Σ, t).
  Proof.
    hnf. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. eauto.
    - todo "normalization".
    - todo "normalization".
  Qed.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma precond2 : pre verified_erasure_pipeline (Σ, v).
  Proof.
    cbn.  repeat eapply conj; sq; cbn; eauto.
    - red. cbn. split; eauto.
      eexists.
      eapply PCUICClassification.subject_reduction_eval; eauto.
    - todo "preservation of eta expandedness".
    - todo "normalization".
    - todo "normalization".
  Qed.

  Let Σ_t := (transform verified_erasure_pipeline (Σ, t) precond).1.
  Let t_t := (transform verified_erasure_pipeline (Σ, t) precond).2.
  Let v_t := compile_value_box v [].

  Lemma fo_v : PCUICFirstorder.firstorder_value Σ [] v.
  Proof.
    sq.
    eapply PCUICFirstorder.firstorder_value_spec; eauto.
    - eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply PCUICWcbvEval.eval_to_value; eauto.
  Qed.

  Ltac destruct_compose :=
    match goal with
    |- context [ transform (compose ?x ?y ?pre) ?p ?pre' ] => 
      let pre'' := fresh in 
      let H := fresh in 
      destruct (transform_compose x y pre p pre') as [pre'' H];
      rewrite H; clear H; revert pre''
    end.

  Lemma v_t_spec : v_t = (transform verified_erasure_pipeline (Σ, v) precond2).2.
  Proof.
    unfold v_t. generalize fo_v, precond2. clear.
    induction 1.
    intros. unfold verified_erasure_pipeline.

    (* repeat destruct_compose. intros. *)
    (* destruct_compose. intros. *)
    (* cbn [transform rebuild_wf_env_transform]. *)
    (* cbn [transform constructors_as_blocks_transformation]. *)
    (* cbn [transform inline_projections_optimization]. *)
    (* cbn [transform remove_match_on_box_trans]. *)
    (* cbn [transform remove_params_optimization]. *)
    (* cbn [transform guarded_to_unguarded_fix]. *)
    (* cbn [transform erase_transform]. *)
    (* cbn [transform pcuic_expand_lets_transform]. *)
    (* unfold PCUICExpandLets.expand_lets_program. *)

  Admitted.

  Lemma verified_erasure_pipeline_theorem :
    ∥ eval (wfl := extraction_wcbv_flags) Σ_t t_t v_t∥.
  Proof.
    (* hnf. *)
    (* pose proof (preservation verified_erasure_pipeline (Σ, t)) as Hcorr. *)
    (* unshelve eapply Hcorr in Heval as Hev. eapply precond. *)
    (* destruct Hev as [v' [[H1] H2]]. *)

    (* repeat match goal with *)
    (*   [ H : obseq _ _ _ _ _ |- _ ] => hnf in H ;  decompose [ex and prod] H ; subst *)
    (* end. *)
    (* rewrite v_t_spec. *)
    (* unfold verified_erasure_pipeline. *)
    (* repeat destruct_compose.      *)
    (* intros. *)
    (* destruct_compose. intros. *)
    (* cbn [transform rebuild_wf_env_transform] in *. *)
    (* cbn [transform constructors_as_blocks_transformation] in *. *)
    (* cbn [transform inline_projections_optimization] in *. *)
    (* cbn [transform remove_match_on_box_trans] in *. *)
    (* cbn [transform remove_params_optimization] in *. *)
    (* cbn [transform guarded_to_unguarded_fix] in *. *)
    (* cbn [transform erase_transform] in *. *)
    (* cbn [transform pcuic_expand_lets_transform] in *. *)
    (* eapply ErasureFunction.firstorder_erases_deterministic in b0; eauto. *)
    (* - rewrite b0 in H1. clear b0. subst v_t Σ_t t_t. *)
    (*   sq. match goal with [ H1 : eval _ _ ?v1 |- eval _ _ ?v2 ] => enough (v2 = v1) as -> by exact H1 end. *)
    (*   clear. todo "matthieu?". *)
    (* - admit. *)
    (* - admit. *)
    (* - eapply PCUICWcbvEval.value_final. admit. *)
  Admitted.

  Lemma verified_erasure_pipeline_lambda :
    PCUICAst.isLambda t -> EAst.isLambda t_t.
  Proof.
    unfold t_t. clear.
  Admitted.

End pipeline_theorem.

Program Definition name_annotation (efl : EWellformed.EEnvFlags) : Transform.t EProgram.eprogram (list (Kernames.kername × EAst.global_decl) × EAst.term) EAst.term EWcbvEvalNamed.value (EProgram.eval_eprogram extraction_wcbv_flags) (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) :=
  {| name := "annotate names";
      pre := fun p =>  EProgram.wf_eprogram efl p ;
      transform p _ := (annotate_env [] p.1, annotate [] p.2) ;
      post := fun p =>  EWellformed.wf_glob p.1 /\ EWellformed.wellformed p.1 0 p.2;
      obseq p p' v v' := ∥represents_value v' v∥ |}.
Next Obligation.
  todo "wellformed annotate".
Qed.
Next Obligation.
  red. intros. red in H. sq.
  unshelve eapply eval_to_eval_named_full in H;
  todo "preserves eval".
Qed.

Program Definition compile_to_malfunction (efl : EWellformed.EEnvFlags) {hp : SemanticsSpec.Heap}:
  Transform.t (list (Kernames.kername × EAst.global_decl) × EAst.term) Malfunction.program
    EWcbvEvalNamed.value SemanticsSpec.value
    (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) (fun _ _ => True) :=
  {| name := "compile to Malfunction";
      pre := fun p =>   EWellformed.wf_glob p.1 /\ EWellformed.wellformed p.1 0 p.2;
      transform p _ := compile_program p ;
      post := fun p =>  True ;
      obseq p p' v v' := v' = CompileCorrect.compile_value p.1 v
  |}.
Next Obligation.
  red. intros. sq.
  eapply compile_correct in H. eauto.
  all: todo "side conditions".
  Unshelve. all: todo "".
Qed.

Program Definition verified_malfunction_pipeline (efl := EWellformed.all_env_flags)  {hp : SemanticsSpec.Heap}:
 Transform.t pcuic_program Malfunction.program
             PCUICAst.term SemanticsSpec.value
             PCUICTransform.eval_pcuic_program
             (fun _ _ => True) :=
  verified_erasure_pipeline ▷
  name_annotation _ ▷
  compile_to_malfunction _.
Next Obligation.
  todo "wf".
Qed.

Section malfunction_pipeline_theorem.

  Local Existing Instance SemanticsSpec.CanonicalHeap.

  Instance cf_ : checker_flags := extraction_checker_flags.
  Instance nf_ : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

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
    eapply precond; eauto.
  Qed.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Let Σ_t := (transform verified_malfunction_pipeline (Σ, t) precond_).1.

  Program Definition Σ_b := (transform (verified_erasure_pipeline ▷ name_annotation (switch_cstr_as_blocks
           (EInlineProjections.disable_projections_env_flag
              (ERemoveParams.switch_no_params EWellformed.all_env_flags))))  (Σ, t) precond_).1.
  
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
    unshelve epose proof (verified_erasure_pipeline_theorem _ _ _ _ _ _ _ _ _ _ _ _ Heval); eauto.
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

Program Definition malfunction_pipeline (efl := EWellformed.all_env_flags) {hp : SemanticsSpec.Heap}:
 Transform.t TemplateProgram.template_program Malfunction.program
             Ast.term SemanticsSpec.value
             TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  pre_erasure_pipeline ▷ verified_malfunction_pipeline.

Local Existing Instance SemanticsSpec.CanonicalHeap.

Definition compile_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p =>(@to_string _ Serialize_program p)) p'.

About compile_malfunction.



Definition compile_module_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p => (@to_string _ Serialize_module p)) p'.
