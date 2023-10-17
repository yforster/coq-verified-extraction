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
From Malfunction Require Import CeresSerialize CompileCorrect SemanticsSpec.
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

Program Definition compile_to_malfunction (efl : EWellformed.EEnvFlags) `{Heap}:
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

Program Definition verified_malfunction_pipeline (efl := EWellformed.all_env_flags) `{Heap}:
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

  Local Existing Instance CanonicalHeap.

  Instance cf_ : checker_flags := extraction_checker_flags.
  Instance nf_ : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

  Variable HP : Pointer.
  Variable HH : Heap.

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

  Variable Normalisation : forall Σ0 : PCUICAst.PCUICEnvironment.global_env_ext,
  PCUICTyping.wf_ext Σ0 -> PCUICSN.NormalizationIn Σ0.

  Lemma precond_ : pre verified_erasure_pipeline (Σ, t).
  Proof.
    eapply precond; eauto.
  Qed.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Let Σ_t := (transform verified_malfunction_pipeline (Σ, t) precond_).1.

  Program Definition Σ_b := (transform (verified_erasure_pipeline ▷ name_annotation) (Σ, t) precond_).1.
  Next Obligation.
    todo "admit".
  Qed.

  Let t_t := (transform verified_malfunction_pipeline (Σ, t) precond_).2.

  Fixpoint compile_value_mf_acc (Σb : list (Kernames.kername × EAst.global_decl))  (acc : list SemanticsSpec.value) (t : PCUICAst.term) : SemanticsSpec.value :=
    match t with
    | PCUICAst.tApp f a => compile_value_mf_acc Σb (acc ++ [compile_value_mf_acc Σb acc a]) f
    | PCUICAst.tConstruct i n _ => 
    match acc with
    | [] =>
        match lookup_constructor_args Σb i with
        | Some num_args =>
            let num_args_until_m := firstn n num_args in
            let index :=
              #|filter
                  (fun x : nat =>
                   match x with
                   | 0 => true
                   | S _ => false
                   end) num_args_until_m| in
            value_Int (Malfunction.Int, Z.of_nat index)
        | None => fail "inductive not found"
        end
    | _ :: _ =>
        match lookup_constructor_args Σb i with
        | Some num_args =>
            let num_args_until_m := firstn n num_args in
            let index :=
              #|filter
                  (fun x : nat =>
                   match x with
                   | 0 => false
                   | S _ => true
                   end) num_args_until_m| in
            Block
              (utils_array.int_of_nat index, acc)
        | None => fail "inductive not found"
        end
    end
    | _ => not_evaluated
    end.
    
  Definition compile_value_mf Σb t := compile_value_mf_acc Σb [] t.

  Fixpoint map_acc_ {A B} (f : list B -> A -> B) (acc:list B) (l : list A) : list B :=
    match l with 
    | [] => [] 
    | a :: l => let b := f acc a in b :: map_acc_ f (acc ++ [b]) l
    end.
    
  Definition map_acc {A B} f l := @map_acc_ A B f [] l.

  Lemma compile_value_mf_mkApps Σb i0 n ui args0:
    compile_value_mf Σb (PCUICAst.mkApps (PCUICAst.tConstruct i0 n ui) args0) =
    compile_value_mf_acc Σb (map_acc (compile_value_mf_acc Σb) (List.rev args0)) (PCUICAst.tConstruct i0 n ui).
  Proof.
    unfold compile_value_mf, map_acc. rewrite <- (app_nil_l (map_acc_ _ _ _)). 
    generalize (@nil SemanticsSpec.value). induction args0 using rev_ind; cbn.
    - intro l; case_eq l; intros; destruct lookup_constructor_args; eauto.
      now rewrite app_nil_r.      
    - intros l. rewrite PCUICAstUtils.mkApps_nonempty; eauto.
      cbn. rewrite removelast_last last_last. rewrite IHargs0; cbn.
      rewrite rev_app_distr. cbn. rewrite <- app_assoc. destruct (app l _); cbn; eauto. 
  Qed.
  
  Lemma compile_value_box_mkApps Σb i0 n ui args0: 
    compile_value_box Σb (PCUICAst.mkApps (PCUICAst.tConstruct i0 n ui) args0) [] =
    compile_value_box Σb (PCUICAst.tConstruct i0 n ui) (map (fun v => compile_value_box Σb v []) args0).
  Proof.
    unfold compile_value_mf. rewrite <- (app_nil_r (map _ _)). 
    generalize (@nil EAst.term) at 1 3. induction args0 using rev_ind; cbn.
    - intro l; case_eq l; intros; destruct pcuic_lookup_inductive_pars; eauto.
    - intros l. rewrite PCUICAstUtils.mkApps_nonempty; eauto.
      cbn. rewrite removelast_last last_last. rewrite IHargs0. cbn. destruct pcuic_lookup_inductive_pars; eauto.
      do 2 f_equal. repeat rewrite map_app. cbn. now repeat rewrite <- app_assoc.
  Qed.

  Lemma compile_value_mf_eq Σb p v' : 
    PCUICFirstorder.firstorder_value Σ [] p ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    EWcbvEvalNamed.eval Σb [] v v' ->   
    compile_value_mf Σb p = compile_value Σb v'.
  Proof.
    intros H tv. destruct H. rewrite compile_value_mf_mkApps. unfold tv. clear tv. rewrite compile_value_box_mkApps.   
    clear H. cbn. destruct pcuic_lookup_inductive_pars; cbn ; eauto.
    2: { inversion 1; subst. cbn in H2. inversion H2. }
    assert (n0 = 0) by admit. subst.  
    intro H. rewrite skipn_0 in H. depind H; subst; cbn. 
    - destruct lookup_constructor_args. 2: { destruct map_acc, args'; eauto. }
      destruct args0.
      + cbn in a. clear IHa. inversion a; now subst.
      + cbn in a. revert a IHa. depind a; subst. intros IHa'. cbn.
        case_eq (map_acc_ (compile_value_mf_acc Σb) [] (List.rev args0 ++ [t0])).
        { intro. clear -H. exfalso. induction args0 using rev_ind ; cbn in H; [inversion H|].
          rewrite rev_app_distr in H. cbn in H; inversion H. }
        intros. rewrite <- H. repeat f_equal. clear v0 l1 H.
  Admitted. 

  Variables (Σ' : _) (HΣ' : (forall (c : Kernames.kername) (decl : EAst.constant_body) 
                               (body : EAst.term) (v : EWcbvEvalNamed.value),
                                EGlobalEnv.declared_constant Σ_b c decl ->
                                EAst.cst_body decl = Some body ->
                                EWcbvEvalNamed.eval Σ_b [] body v ->
                                In (Kernames.string_of_kername c, compile_value Σ_b v) Σ')).

  Variable (Haxiom_free : Extract.axiom_free Σ).

  Lemma verified_malfunction_pipeline_theorem h :
    ∥ SemanticsSpec.eval [] (fun _ => not_evaluated) h t_t h (compile_value_mf Σ_b v)∥.
  Proof.
    unshelve epose proof (verified_erasure_pipeline_theorem _ _ _ _ _ _ _ _ _ _ _ _ _ Heval); eauto.
    intros. pose proof compile_correct.
    unfold t_t, verified_malfunction_pipeline. sq. repeat destruct_compose; intros.
    unfold compile_value_mf.
     
    rewrite transform_compose. cbn.  
    sq.
  Admitted.

  (* Lemma verified_erasure_pipeline_lambda : *)
  (*   PCUICAst.isLambda t -> EAst.isLambda t_t. *)
  (* Proof. *)
  (*   unfold t_t. clear. *)
  (* Admitted. *)

End malfunction_pipeline_theorem.

About verified_malfunction_pipeline_theorem.

Program Definition malfunction_pipeline (efl := EWellformed.all_env_flags) `{Heap}:
 Transform.t _ _ _ _ _ _ TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  pre_erasure_pipeline ▷ verified_malfunction_pipeline.

Local Existing Instance CanonicalHeap.

Definition compile_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program) `{Heap}
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p =>(@to_string _ Serialize_program p)) p'.

About compile_malfunction.

Definition compile_module_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program) `{Heap}
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p => (@to_string _ Serialize_module p)) p'.
