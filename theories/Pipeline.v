(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Utils Require Import bytestring utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICProgram.
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

#[local] Arguments transform : simpl never. 

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

From Malfunction Require Import Compile Serialize.

Record good_for_extraction (p : program (list (kername × EAst.global_decl)) EAst.term) := 
  {
    few_enough_constructors :
    forall (i : inductive) (mb : EAst.mutual_inductive_body)
      (ob : EAst.one_inductive_body),
      EGlobalEnv.lookup_inductive p.1 i = Some (mb, ob) ->
      #|EAst.ind_ctors ob| < Z.to_nat Malfunction.Int63.wB ;
    few_enough_arguments_in_constructors :
    forall (i : inductive) (mb : EAst.mutual_inductive_body)
      (ob : EAst.one_inductive_body),
      EGlobalEnv.lookup_inductive p.1 i = Some (mb, ob) ->
                             (forall (n : nat) (b : EAst.constructor_body),
                                 nth_error (EAst.ind_ctors ob) n = Some b ->
                                 EAst.cstr_nargs b < utils_array.int_to_nat PArray.max_length) ;
    right_flags_in_glob : @EWellformed.wf_glob extraction_env_flags p.1 ;
    right_flags_in_term : @EWellformed.wellformed extraction_env_flags p.1 0 p.2
  }.

Inductive check_good :=
| Good
| Error of string.

Definition bind_good a b :=
  match a with
  | Good => b
  | Error s => Error s
  end.

Notation "a &|& b" := (bind_good a b) (at level 70).

Definition bool_good_error a s :=
  match a with
  | true => Good
  | false => Error s
  end.

Notation "a >>> s" := (bool_good_error a s) (at level 65).

Fixpoint check_good_for_extraction_rec (Σ : (list (kername × EAst.global_decl))) :=
  match Σ with
  | nil => Good
  | (kn, EAst.ConstantDecl d) :: Σ =>
      forallb (fun x : kername × EAst.global_decl => negb (x.1 == kn)) Σ >>> "environment re-declares names"
      &|&
      option_default (fun b : EAst.term => @EWellformed.wellformed extraction_env_flags Σ 0 b) (EAst.cst_body d) false >>> "environment contains non-extractable constant"
      &|&
      check_good_for_extraction_rec Σ
  | (kn, EAst.InductiveDecl mind) :: Σ =>
      forallb (fun ob => #|EAst.ind_ctors ob| <? Z.to_nat Malfunction.Int63.wB) mind.(EAst.ind_bodies) >>> "inductive with too many constructors"
      &|&
      forallb (fun ob => forallb (fun b => EAst.cstr_nargs b <? utils_array.int_to_nat PArray.max_length ) (EAst.ind_ctors ob)) mind.(EAst.ind_bodies) >>> "inductive with too many constructor arguments"
      &|&
      forallb (fun x : kername × EAst.global_decl => negb (x.1 == kn)) Σ >>> "environment re-declares names"
      &|& @EWellformed.wf_minductive extraction_env_flags mind >>> "environment contains non-extractable inductive"
      &|& check_good_for_extraction_rec Σ
  end.

Definition check_good_for_extraction (p : program (list (kername × EAst.global_decl)) EAst.term) :=
  @EWellformed.wellformed extraction_env_flags p.1 0 p.2 >>> "term contains non-extractable constructors"
    &|& check_good_for_extraction_rec p.1.

Lemma check_good_for_extraction_correct (p : program (list (kername × EAst.global_decl)) EAst.term) :
  good_for_extraction p <-> check_good_for_extraction p = Good.
Proof.
  split.
  - intros []. unfold check_good_for_extraction. rtoProp. admit.
  - unfold check_good_for_extraction. rtoProp. intros []. admit.
Admitted.

Obligation Tactic := try now program_simpl.

Program Definition enforce_extraction_conditions (efl := EWellformed.all_env_flags) `{Pointer} `{Heap} :
  t EAst.global_declarations EAst.global_declarations EAst.term EAst.term EAst.term
    EAst.term
    (EProgram.eval_eprogram EImplementBox.block_wcbv_flags) (EProgram.eval_eprogram EImplementBox.block_wcbv_flags) :=
  {|
    name := "Enforce the term is extractable" ;
    transform p _ := p ;
    pre p := True ;
    post p := good_for_extraction p ;
    obseq p1 _ p2 v1 v2 := p1 = p2 /\ v1 = v2
  |}.
Next Obligation.
  program_simpl. todo "assuming that pipeline is run on terms that can be extracted".
Qed.
Next Obligation.
  program_simpl. red. program_simpl.  exists v. auto.
Qed.

From MetaCoq.Erasure Require Import EImplementBox EWellformed EProgram.

Program Definition implement_box_transformation (efl := extraction_env_flags) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming to constuctors as blocks";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := good_for_extraction p ;
    post p := good_for_extraction p /\ wf_eprogram (switch_off_box efl) p ;
    obseq p hp p' v v' := v' = implement_box v |}.

Next Obligation.
  intros. cbn in *. split. 2: split.
  - todo "implement box good".
  - eapply implement_box_env_wf_glob; eauto. apply p.
  - eapply transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Next Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply implement_box_eval; cbn; eauto.
  all: reflexivity.
Qed.

#[global]
Instance implement_box_extends (efl := extraction_env_flags) :
   TransformExt.t (implement_box_transformation) extends_eprogram extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /implement_box_program /=.
  split => /=.
  eapply (implement_box_env_extends). all: try reflexivity.
  exact ext.
  apply pr.
  apply pr'.
  now rewrite -eq.
Qed.

Obligation Tactic := program_simpl.

Program Definition name_annotation (efl := extraction_env_flags) : Transform.t EAst.global_declarations (list (Kernames.kername × EAst.global_decl))
  EAst.term EAst.term _ EWcbvEvalNamed.value
  (EProgram.eval_eprogram extraction_wcbv_flags) (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) :=
  {| name := "annotate names";
      pre := fun p =>  good_for_extraction p /\ EProgram.wf_eprogram efl p ;
      transform p _ := (annotate_env [] p.1, annotate [] p.2) ;
      post := fun p => good_for_extraction p /\ EProgram.wf_eprogram named_extraction_env_flags p ;
      obseq p _ p' v v' := ∥ represents_value v' v∥ |}.
Next Obligation.
  destruct input as [Σ s].
  split. todo "annotate good".
  destruct H0 as [HΣ Hs].
  split.
  2: now eapply wellformed_annotate with (Γ := []).
  cbn in *. clear Hs. clear H.
  induction HΣ.
  - econstructor.
  - cbn in *. destruct d as [ [[]]| ]; cbn in *; econstructor; eauto.
    cbn. now eapply wellformed_annotate with (Γ := []).
    { clear - H0. induction H0; (try destruct x as [? [ [[]]| ]]); cbn in *; econstructor; eauto. }
    { clear - H0. induction H0; (try destruct x as [? [ [[]]| ]]); cbn in *; econstructor; eauto. }
Qed.
Next Obligation.
  red. intros. destruct pr as [_ pr]. red in H. sq.
  unshelve eapply eval_to_eval_named_full in H as [v_ Hv].
  - shelve.
  - exists v_. repeat split; sq. cbn. eapply Hv. eapply Hv.
  - eapply pr.
  - destruct pr. clear H1 H.
    generalize (@nil Kernames.ident) at 2. induction H0; cbn; intros.
    + econstructor.
    + destruct d. destruct c. destruct cst_body0.
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
      pre := fun p =>   EWellformed.wf_glob p.1 /\ EWellformed.wellformed p.1 0 p.2 /\
                       good_for_extraction p ;
      transform p _ := compile_program p ;
      post := fun p =>  True ;
      obseq p _ p' v v' := v' = CompileCorrect.compile_value p.1 v
  |}.
Next Obligation.
  rename H into HP; rename H0 into HH. 
  red. intros. sq.
  eapply compile_correct in H.
  - eauto.
  - intros. split. eapply pr. eauto. eapply pr. eauto.
  - intros. unfold lookup. cbn. instantiate (1 := fun _ =>  SemanticsSpec.fail "notfound"). reflexivity.
  - intros. todo "global env".
    Unshelve. all: todo "global env".
Qed.

Program Definition verified_malfunction_pipeline (efl := EWellformed.all_env_flags) `{Heap}:
 Transform.t global_env_ext_map _ _ _ _ SemanticsSpec.value 
             PCUICTransform.eval_pcuic_program
             (fun _ _ => True) :=
  verified_erasure_pipeline ▷
  enforce_extraction_conditions ▷
  implement_box_transformation ▷
  name_annotation ▷
  compile_to_malfunction named_extraction_env_flags.
Next Obligation.
  cbn. intros.
  destruct p as [Σ t]. split. apply H2. split. eapply H2.
  eapply H1.
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

  Variable fo : forall i, @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable noParam : forall i mdecl, lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0. 

  Variable Normalisation : forall Σ0 : PCUICAst.PCUICEnvironment.global_env_ext,
  PCUICTyping.wf_ext Σ0 -> PCUICSN.NormalizationIn Σ0.

  Lemma precond_ : pre verified_erasure_pipeline (Σ, t).
  Proof.
    eapply precond; eauto.
  Defined.

  Let Σ_t := (transform verified_malfunction_pipeline (Σ, t) precond_).1.

  Program Definition Σ_b `{EWellformed.EEnvFlags} := (transform (verified_erasure_pipeline ▷  enforce_extraction_conditions ▷ implement_box_transformation ▷ name_annotation) (Σ, t) precond_).1.

  Let t_t := (transform verified_malfunction_pipeline (Σ, t) precond_).2.

  Fixpoint compile_value_mf_acc (Σb : list (Kernames.kername × EAst.global_decl)) (t : PCUICAst.term) (acc : list SemanticsSpec.value) : SemanticsSpec.value :=
    match t with
    | PCUICAst.tApp f a => compile_value_mf_acc Σb f (compile_value_mf_acc Σb a [] :: acc)
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
    
  Definition compile_value_mf Σb t := compile_value_mf_acc Σb t [].

  Lemma compile_value_box_mkApps Σb i0 n ui args0: 
    compile_value_box Σb (PCUICAst.mkApps (PCUICAst.tConstruct i0 n ui) args0) [] =
    compile_value_box Σb (PCUICAst.tConstruct i0 n ui) (map (fun v => compile_value_box Σb v []) args0).
  Proof.
    rewrite <- (app_nil_r (map _ _)). 
    generalize (@nil EAst.term) at 1 3. induction args0 using rev_ind; cbn.
    - intro l; case_eq l; intros; destruct pcuic_lookup_inductive_pars; eauto.
    - intros l. rewrite PCUICAstUtils.mkApps_nonempty; eauto.
      cbn. rewrite removelast_last last_last. rewrite IHargs0. cbn. destruct pcuic_lookup_inductive_pars; eauto.
      do 2 f_equal. repeat rewrite map_app. cbn. now repeat rewrite <- app_assoc.
  Qed.

  Lemma compile_value_mf_mkApps Σb i0 n ui args0: 
    compile_value_mf Σb (PCUICAst.mkApps (PCUICAst.tConstruct i0 n ui) args0) =
    compile_value_mf_acc Σb (PCUICAst.tConstruct i0 n ui) (map (fun v => compile_value_mf Σb v) args0).
  Proof.
    unfold compile_value_mf. rewrite <- (app_nil_r (map _ _)). 
    generalize (@nil SemanticsSpec.value) at 1 3. induction args0 using rev_ind; cbn.
    - intro l; case_eq l; intros; destruct lookup_constructor_args; eauto.
    - intros l. rewrite PCUICAstUtils.mkApps_nonempty; eauto.
      cbn. rewrite removelast_last last_last. rewrite IHargs0. cbn. 
      repeat rewrite map_app; cbn; repeat rewrite <- app_assoc.
      destruct lookup_constructor_args; eauto.
  Qed.

  Fixpoint eval_fo kn (t: EAst.term) : EWcbvEvalNamed.value :=   
    match t with 
      | EAst.tConstruct ind c args => vConstruct ind c (map (eval_fo kn) args)
      | _ => vConstruct kn 0 []
    end. 

  Lemma compile_value_eval_fo {Henvflags:EWellformed.EEnvFlags} kn : 
    PCUICFirstorder.firstorder_value Σ [] t ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) t [] in
    ∥EWcbvEvalNamed.eval Σ_b [] v (eval_fo kn v)∥.
  Proof.
    intro H. unfold Σ_b. repeat destruct_compose; intros. cbn.
    unfold precond_ in *. clear Σ_t t_t. 
    revert typing expt H0 H1 H2.
    refine (PCUICFirstorder.firstorder_value_inds _ _ (fun t => forall (typing : Σ;;; [] |- t : mkApps (tInd i u) args)
    (expt : PCUICEtaExpand.expanded Σ.1 [] t)
    (H0 : pre enforce_extraction_conditions
            (transform verified_erasure_pipeline (Σ, t)
               (precond Σ HΣ expΣ t expt i u args typing Normalisation)))
    (H1 : pre implement_box_transformation
            (transform enforce_extraction_conditions
               (transform verified_erasure_pipeline (Σ, t)
                  (precond Σ HΣ expΣ t expt i u args typing Normalisation)) H0))
    (H2 : pre name_annotation
            (transform implement_box_transformation
               (transform enforce_extraction_conditions
                  (transform verified_erasure_pipeline (
                     Σ, t) (precond Σ HΣ expΣ t expt i u args typing Normalisation))
                  H0) H1)),
  ∥ EWcbvEvalNamed.eval
      (transform name_annotation
         (transform implement_box_transformation
            (transform enforce_extraction_conditions
               (transform verified_erasure_pipeline (Σ, t)
                  (precond Σ HΣ expΣ t expt i u args typing Normalisation)) H0) H1)
         H2).1 [] (compile_value_box (PCUICExpandLets.trans_global_env Σ.1) t [])
      (eval_fo kn (compile_value_box (PCUICExpandLets.trans_global_env Σ.1) t [])) ∥) _ _ H); intros; clear H.
    rewrite compile_value_box_mkApps.
    eapply Forall_All in H1. cbn. pose proof (X' := X).
    eapply PCUICValidity.validity in X. eapply PCUICInductiveInversion.wt_ind_app_variance in X as [mdecl [? ?]].  
    unfold pcuic_lookup_inductive_pars. unfold lookup_inductive,lookup_inductive_gen,lookup_minductive_gen in e.
    rewrite PCUICExpandLetsCorrectness.trans_lookup. specialize (noParam (inductive_mind i0)). 
    case_eq (lookup_env Σ (inductive_mind i0)); cbn.  
    2: { intro neq. rewrite neq in e. inversion e. }
    intros ? Heq. rewrite Heq in e. rewrite Heq. destruct g; cbn; [inversion e |]. destruct nth_error; inversion e; subst; cbn.  
    assert (ind_npars m = 0) by eauto. rewrite H. rewrite skipn_0.
    eapply PCUICValidity.inversion_mkApps in X' as [A [X' ?]].  
    eapply PCUICInversion.inversion_Construct in X' as [? [? [? [? [? [? ?]]]]]]; eauto.
    eapply map_squash. intro. econstructor. 3: exact X. 1-2: admit. 
    induction H1; cbn. econstructor; eauto. inversion t0; subst; clear t0. inversion H0; subst.
(*    specialize (p _ _ _).    
    eapply map_squash. intro; econstructor. [apply p | eauto].
    eapply IHAll; eauto. inversion H0; eauto. }
    eapply declared_constructor_to_gen in d. 
    rewrite /declared_constructor_gen /declared_inductive_gen /declared_minductive_gen in d.
    unfold Σ_b. repeat destruct_compose; intros. 
    rewrite /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive.
    rewrite EExtends. lookup_env_In. 
    rewrite <- EEnvMap.GlobalContextMap.lookup_env_spec.
    cbn. 
    destruct EGlobalEnv.lookup_env eqn:Henv => //=.
    destruct g => //.
    eapply he in declm; tea. subst m.
    rewrite nth_error_map decli /=.
    rewrite nth_error_map declc /=. intuition congruence.
    unfold Σ_b. repeat destruct_compose; intros.
    

      
      
    
    
    (* revert typing Σ_b.  refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in *)
    (* ∥EWcbvEvalNamed.eval Σ_b [] v (eval_fo kn v)∥) _ _ H); intros; clear H.  *)
    (* unfold v0. clear v0. rewrite compile_value_box_mkApps. *)
    (* eapply Forall_All in H1. cbn. pose proof (X' := X). *)
    (* eapply PCUICValidity.validity in X. eapply PCUICInductiveInversion.wt_ind_app_variance in X as [mdecl [? ?]].   *)
    (* unfold pcuic_lookup_inductive_pars. unfold lookup_inductive,lookup_inductive_gen,lookup_minductive_gen in e. *)
    (* rewrite PCUICExpandLetsCorrectness.trans_lookup. specialize (noParam (inductive_mind i0)).  *)
    (* case_eq (lookup_env Σ (inductive_mind i0)); cbn.   *)
    (* 2: { intro neq. rewrite neq in e. inversion e. } *)
    (* intros ? Heq. rewrite Heq in e. rewrite Heq. destruct g; cbn; [inversion e |]. destruct nth_error; inversion e; subst; cbn.   *)
    (* assert (ind_npars m = 0) by eauto. rewrite H. rewrite skipn_0. *)
    (* eapply PCUICValidity.inversion_mkApps in X' as [A [X' ?]].   *)
    (* eapply PCUICInversion.inversion_Construct in X' as [? [? [? [? [? [? ?]]]]]]; eauto. *)
    (* eapply map_squash. intro. econstructor. 3: exact X. *)
    (* 3 :{ clear t0.  induction H1; cbn. econstructor; eauto. *)
    (* cbn in p0. destruct p0 as [p0]. eapply map_squash. intro; econstructor; [exact p0 | eauto]. *)
    (* eapply IHAll; eauto. inversion H0; eauto. } *)
    (* eapply declared_constructor_to_gen in d.  *)
    (* rewrite /declared_constructor_gen /declared_inductive_gen /declared_minductive_gen in d. *)
    (* unfold Σ_b. repeat destruct_compose; intros.  *)
    (* rewrite /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive. *)
    (* rewrite EExtends. lookup_env_In.  *)
    (* rewrite <- EEnvMap.GlobalContextMap.lookup_env_spec. *)
    (* cbn.  *)
    (* destruct EGlobalEnv.lookup_env eqn:Henv => //=. *)
    (* destruct g => //. *)
    (* eapply he in declm; tea. subst m. *)
    (* rewrite nth_error_map decli /=. *)
    (* rewrite nth_error_map declc /=. intuition congruence. *)
    (* unfold Σ_b. repeat destruct_compose; intros. *)
    

    (* 2: { rewrite map_length.  } *) *)
  Admitted.

  From Equations Require Import Equations.

  Lemma implement_box_fo {Henvflags:EWellformed.EEnvFlags} p : 
  PCUICFirstorder.firstorder_value Σ [] p ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    v = EImplementBox.implement_box v.
  Proof.
  intro H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
  v = EImplementBox.implement_box v) _ _ H); intros. revert v0. 
  rewrite compile_value_box_mkApps. intro v0. cbn in v0. destruct pcuic_lookup_inductive_pars; eauto. 
  assert (n0 = 0) by admit. subst. revert v0; rewrite skipn_0. set (map _ _). simpl. rewrite EImplementBox.implement_box_unfold_eq. simpl.
  f_equal. erewrite MCList.map_InP_spec. clear -H1. unfold l; clear l. induction H1; eauto. simpl. f_equal; eauto.
  Admitted.
        
  Lemma represent_value_eval_fo p kn : 
    PCUICFirstorder.firstorder_value Σ [] p ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    forall v', represents_value v' v -> v' = eval_fo kn v.
  Proof.
    intro H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    forall v', represents_value v' v -> v' = eval_fo kn v) _ _ H); intros. revert H3. 
    unfold v0. clear v0. rewrite compile_value_box_mkApps.
    eapply Forall_All in H1. cbn. destruct pcuic_lookup_inductive_pars; [| admit].
    assert (n0 = 0) by admit. subst. rewrite skipn_0. cbn. inversion 1; subst; eauto. clear H3. 
    f_equal. clear X H0 H2. revert vs H6. induction H1; cbn; inversion 1; f_equal; subst. 
    - eapply p0; eauto.
    - eapply IHAll; eauto.
  Admitted. 

  Lemma compile_value_mf_eq {Henvflags: EWellformed.EEnvFlags} p kn : 
    PCUICFirstorder.firstorder_value Σ [] p ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    compile_value_mf Σ_b p = compile_value Σ_b (eval_fo kn v).
  Proof.
    intros H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    compile_value_mf Σ_b p = compile_value Σ_b (eval_fo kn v)) _ _ H).
    intros. rewrite compile_value_mf_mkApps. unfold v0. clear v0. rewrite compile_value_box_mkApps.    
    clear H. cbn. unfold pcuic_lookup_inductive_pars. 
    destruct PCUICAst.PCUICEnvironment.lookup_env ; [|admit].
    destruct g ; [admit|].
    assert ((PCUICAst.PCUICEnvironment.ind_npars m) = 0) by admit. rewrite H. rewrite skipn_0. cbn. 
    destruct lookup_constructor_args. 2: { clear; destruct map; destruct map; eauto. }
    destruct args0; cbn; eauto.
    repeat f_equal; inversion H1; subst; clear H1; eauto.
    repeat rewrite map_map. eapply map_ext_Forall; eauto.
  Admitted. 
    
  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Variables (Σ' : _) (Henvflags:EWellformed.EEnvFlags)  (HΣ' : (forall (c : Kernames.kername) (decl : EAst.constant_body) 
                               (body : EAst.term) (v : EWcbvEvalNamed.value),
                                EGlobalEnv.declared_constant Σ_b c decl ->
                                EAst.cst_body decl = Some body ->
                                EWcbvEvalNamed.eval Σ_b [] body v ->
                                In (Kernames.string_of_kername c, compile_value Σ_b v) Σ')).

  Variable (Haxiom_free : Extract.axiom_free Σ).


  Lemma verified_malfunction_pipeline_theorem h :
    ∥ SemanticsSpec.eval Σ' (fun _ => fail "notfound") h t_t h (compile_value_mf Σ_b v)∥.
  Proof.
    unshelve epose proof (verified_erasure_pipeline_theorem _ _ _ _ _ _ _ _ _ _ _ _ _ Heval); eauto.
    erewrite compile_value_mf_eq with (kn:=i). 
    2: { eapply fo_v; eauto. }
    unfold t_t, verified_malfunction_pipeline. sq. repeat destruct_compose; intros.
    unfold compile_to_malfunction. unfold transform at 1. unfold compile_program. 
    cbn. unfold Σ_b in *. revert HΣ'. repeat destruct_compose; intros.
    (* YF: Had to comment this out because the apply is looping *)
    (* eapply compile_correct with (Γ := []). intros.  *) 
    (* - admit. (* bounds stuff *)  *)
    (* - eauto.  *)
    (* - eauto. *)
    (* - cbn in H0, H1, H2, H3, H4. unfold name_annotation. unfold transform at 1 4. cbn.  *)
    (*   epose proof (eval_to_eval_named_full _ _ _ _ _) as [? [? ?]]. *)
    (*   5: { eapply represent_value_eval_fo in r. rewrite r in e. eapply e. eapply fo_v; eauto. } *)
    (*   { admit. } *)
    (*   { admit. } *)
    (*   { rewrite implement_box_fo. eapply fo_v; eauto. eapply EImplementBox.implement_box_eval. 1-6: admit. *)
    (*     eapply H. } *)
    (*   admit.  *)
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

Definition compile_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program) `{Heap}
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p =>(@to_string _ Serialize_program p)) p'.

About compile_malfunction.

Definition compile_module_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program) `{Heap}
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (fun p => (@to_string _ Serialize_module p)) p'.
