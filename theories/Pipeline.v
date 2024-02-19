(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Utils Require Import bytestring utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICReduction PCUICAstUtils PCUICSN
    PCUICTyping PCUICProgram PCUICFirstorder PCUICEtaExpand.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EImplementBox EPretty Extract.
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

  Lemma All_sq {A} (P : A -> Type) l :
    Forall (fun x => squash (P x)) l ->
    squash (All P l).
  Proof using Type.
    induction 1.
    - repeat econstructor.
    - sq. now constructor.
  Qed.
  
Import Transform.Transform.

#[local] Arguments transform : simpl never. 

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

#[local] Existing Instance extraction_normalizing.

Import EWcbvEval.

From Malfunction Require Import Compile Serialize.

Definition int_to_nat (i : Uint63.int) : nat :=
  Z.to_nat (Uint63.to_Z i).

Definition array_length := Eval cbv in PArray.max_length.

Record good_for_extraction (fl : EWellformed.EEnvFlags) (p : program (list (kername × EAst.global_decl)) EAst.term) := 
  {
    few_enough_blocks :
      forall (i : inductive) (args : list nat), lookup_constructor_args p.1 i = Some args -> blocks_until #|args| args < 200 ;
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
                                 EAst.cstr_nargs b < int_to_nat array_length) ;
    right_flags_in_glob : @EWellformed.wf_glob fl p.1 ;
    right_flags_in_term : @EWellformed.wellformed fl p.1 0 p.2
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

Fixpoint check_good_for_extraction_rec (fl : EWellformed.EEnvFlags) (Σ : (list (kername × EAst.global_decl))) :=
  match Σ with
  | nil => Good
  | (kn, EAst.ConstantDecl d) :: Σ =>
      forallb (fun x : kername × EAst.global_decl => negb (x.1 == kn)) Σ >>> "environment re-declares names"
      &|&
      option_default (fun b : EAst.term => @EWellformed.wellformed fl Σ 0 b) (EAst.cst_body d) false >>> "environment contains non-extractable constant"
      &|&
      check_good_for_extraction_rec fl Σ
  | (kn, EAst.InductiveDecl mind) :: Σ =>
      forallb (fun ob => let args := map EAst.cstr_nargs (EAst.ind_ctors ob) in
                 blocks_until #|args| args <? 200)  mind.(EAst.ind_bodies) >>> "inductive with too many blocks"
      &|&
      forallb (fun ob => #|EAst.ind_ctors ob| <? Z.to_nat Malfunction.Int63.wB) mind.(EAst.ind_bodies) >>> "inductive with too many constructors"
      &|&
      forallb (fun ob => forallb (fun b => EAst.cstr_nargs b <? int_to_nat array_length ) (EAst.ind_ctors ob)) mind.(EAst.ind_bodies) >>> "inductive with too many constructor arguments"
      &|&
      forallb (fun x : kername × EAst.global_decl => negb (x.1 == kn)) Σ >>> "environment re-declares names"
      &|& @EWellformed.wf_minductive fl mind >>> "environment contains non-extractable inductive"
      &|& check_good_for_extraction_rec fl Σ
  end.

Definition check_good_for_extraction fl (p : program (list (kername × EAst.global_decl)) EAst.term) :=
  @EWellformed.wellformed fl p.1 0 p.2 >>> "term contains non-extractable constructors"
    &|& check_good_for_extraction_rec fl p.1.

#[local] Obligation Tactic := try now program_simpl.

Axiom assume_can_be_extracted : forall erased_program, good_for_extraction extraction_env_flags erased_program.

Program Definition enforce_extraction_conditions (efl := EWellformed.all_env_flags) `{Pointer} `{Heap} :
  t EAst.global_declarations EAst.global_declarations EAst.term EAst.term EAst.term
    EAst.term
    (EProgram.eval_eprogram block_wcbv_flags) (EProgram.eval_eprogram block_wcbv_flags) :=
  {|
    name := "Enforce the term is extractable" ;
    transform p _ := p ;
    pre p := True ;
    post p := good_for_extraction extraction_env_flags p ;
    obseq p1 _ p2 v1 v2 := p1 = p2 /\ v1 = v2
  |}.
Next Obligation.
  program_simpl. apply assume_can_be_extracted.
Qed.
Next Obligation.
  program_simpl. red. program_simpl.  exists v. auto.
Qed.

From MetaCoq.Erasure Require Import EImplementBox EWellformed EProgram.

Program Definition implement_box_transformation (efl := extraction_env_flags) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := good_for_extraction extraction_env_flags p ;
    post p := good_for_extraction extraction_env_flags p /\ wf_eprogram (switch_off_box efl) p ;
    obseq p hp p' v v' := v' = implement_box v |}.

Next Obligation.
  intros. cbn in *. split. 2: split.
  - destruct input as [Σ t]. 
    split.
    + intros.
      unfold lookup_constructor_args in H.
      rewrite lookup_inductive_implement_box in H. now eapply few_enough_blocks.
    + intros.
      rewrite lookup_inductive_implement_box in H. now eapply few_enough_constructors.
    + intros. rewrite lookup_inductive_implement_box in H. now eapply few_enough_arguments_in_constructors.
    + cbn. refine (@implement_box_env_wf_glob _ Σ _ _ _). reflexivity. reflexivity. apply p.
    + apply transform_wellformed'. all: try reflexivity. apply p. apply p.
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

#[local] Obligation Tactic := program_simpl.

Definition annotate_decl Γ (d : EAst.global_decl) :=
  match d with
    | EAst.ConstantDecl (EAst.Build_constant_body (Some b)) => EAst.ConstantDecl (EAst.Build_constant_body (Some (annotate Γ b)))
  | d => d
  end.

Lemma lookup_env_annotate {Σ : EAst.global_declarations} Γ kn :
  EGlobalEnv.lookup_env (annotate_env Γ Σ) kn =
  option_map (annotate_decl Γ) (EGlobalEnv.lookup_env Σ kn).
Proof.
  induction Σ at 1 2; simpl; auto.
  destruct a. destruct g0. destruct c. destruct cst_body0.
  all: cbn; case: eqb_spec => //.
Qed.

Lemma lookup_inductive_annotate_env (Σ : EAst.global_declarations) Γ (ind : inductive) :
  EGlobalEnv.lookup_inductive (annotate_env Γ Σ) ind =
  EGlobalEnv.lookup_inductive Σ ind.
Proof.
  unfold EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive.
  rewrite !lookup_env_annotate.
  destruct EGlobalEnv.lookup_env; try reflexivity.
  cbn.
  destruct g; cbn; try reflexivity. 
  destruct c; cbn; try reflexivity.
  destruct cst_body0; reflexivity.
Qed.

Lemma annotate_env_fresh(k : kername) (Σ : list (kername × EAst.global_decl)) :
  EGlobalEnv.fresh_global k Σ -> EGlobalEnv.fresh_global k (annotate_env [] Σ).
Proof.
  induction 1.
  - econstructor.
  - cbn. destruct x. destruct g. destruct c.
    destruct cst_body0.
    all: econstructor; eauto.
Qed.
  
Program Definition name_annotation (efl := extraction_env_flags) : Transform.t EAst.global_declarations (list (Kernames.kername × EAst.global_decl))
  EAst.term EAst.term _ EWcbvEvalNamed.value
  (EProgram.eval_eprogram extraction_wcbv_flags) (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) :=
  {| name := "annotate names";
      pre := fun p =>  good_for_extraction extraction_env_flags p /\ EProgram.wf_eprogram efl p ;
      transform p _ := (annotate_env [] p.1, annotate [] p.2) ;
      post := fun p => good_for_extraction named_extraction_env_flags p /\
                      exists t, wellformed (efl := extraction_env_flags) p.1 0 t /\ ∥represents [] [] p.2 t∥ ;
      obseq p _ p' v v' := ∥ represents_value v' v∥ |}.
Next Obligation.
  destruct input as [Σ s].
  split.
  { split.
    + intros. eapply few_enough_blocks. eassumption.
      unfold lookup_constructor_args in *.
      instantiate (1 := i).
      erewrite <- lookup_inductive_annotate_env.
      eassumption.
    + intros. eapply few_enough_constructors. eassumption.
      unfold lookup_constructor_args in *.
      instantiate (1 := mb). instantiate (1 := i).
      erewrite <- lookup_inductive_annotate_env.
      eassumption.
    + intros.
      rewrite lookup_inductive_annotate_env in H1.
      eapply few_enough_arguments_in_constructors; eauto.
    + cbn. destruct H0.
      clear H1. cbn in *. clear H. induction Σ; cbn.
      - econstructor.
      - destruct a. destruct g. destruct c. destruct cst_body0.
        * invs H0. constructor; eauto. 
          cbn in *. now eapply wellformed_annotate.
          cbn in *. now eapply annotate_env_fresh.
        * invs H0. econstructor; eauto.
          now eapply annotate_env_fresh.
        * invs H0. econstructor; eauto.
          now eapply annotate_env_fresh.
    + cbn. destruct H0. eapply wellformed_annotate with (Γ := nil) in H1.
      cbn in *. assumption.
  }
  destruct H0 as [HΣ Hs]. cbn. exists s.
  cbn in *. split.
  2:{ sq. eapply nclosed_represents. cbn. eassumption. }
  clear - Hs. revert Hs. generalize 0. intros.
  induction s using EInduction.term_forall_list_ind in n, Hs |- *; cbn in *; eauto; rtoProp; eauto. 
  all: try now rtoProp; eauto. 
  - unfold EGlobalEnv.lookup_constant in *. rewrite lookup_env_annotate. destruct EGlobalEnv.lookup_env as [ [[ [] ] | ] | ]; cbn in *; eauto.
  - unfold EGlobalEnv.lookup_constructor_pars_args, EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. rewrite lookup_env_annotate. 
    destruct EGlobalEnv.lookup_env as [ [[ [] ] | ] | ]; cbn in *; eauto.
    destruct nth_error; cbn in *; try congruence.
    destruct nth_error; cbn in *; try congruence.
    repeat split; eauto.
    solve_all.
  - unfold EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. rewrite lookup_env_annotate. 
    destruct EGlobalEnv.lookup_env as [ [[ [] ] | ] | ]; cbn in *; eauto.
    destruct nth_error; cbn in *; try congruence.  
    repeat split; eauto.
    solve_all.
  - solve_all. unfold wf_fix in *. rtoProp. solve_all.
  - solve_all. destruct p as [? []]; cbn in *; eauto. 
    apply andb_and in H0 as [? ?]. inversion X; subst. clear X. destruct X0.
    solve_all. apply andb_and; split; solve_all.
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

Lemma annotate_extends (efl := extraction_env_flags) Σ Σ' :
   EGlobalEnv.extends Σ Σ' ->
   EGlobalEnv.extends (annotate_env [] Σ) (annotate_env [] Σ').
Proof.
  red. intros ext kn decl Hdecl. rewrite lookup_env_annotate in Hdecl.
  rewrite lookup_env_annotate. eapply option_map_Some in Hdecl as [? [? ?]]. 
  erewrite ext; cbn; eauto. now f_equal.
Qed.

Module evalnamed.

  Import EWcbvEvalNamed.
  Derive Signature for eval.

  Lemma eval_det Σ Γ t v1 v2 :
    eval Σ Γ t v1 -> eval Σ Γ t v2 -> v1 = v2.
  Proof.
    intros H.
    revert v2.
    induction H; intros v2 Hev; depelim Hev.
    - congruence.
    - Ltac appIH H1 H2 := apply H1 in H2; invs H2.
      appIH IHeval1 Hev1.
      appIH IHeval2 Hev2.
      appIH IHeval3 Hev3.
      eauto.
    - appIH IHeval1 Hev1.
    - reflexivity.
    - appIH IHeval1 Hev1.
      appIH IHeval2 Hev2.
      reflexivity.
    - appIH IHeval1 Hev1.
      rewrite e0 in e. invs e.
      rewrite e1 in e4. invs e4.
      assert (nms = nms0) as ->.
      { clear - f f4. revert nms f4. induction f; cbn; intros; depelim f4.
        + reflexivity.
        + f_equal; eauto; congruence.
      }
      now appIH IHeval2 Hev2.
    - appIH IHeval1 Hev1.
    - appIH IHeval1 Hev1.
      rewrite e0 in e. invs e.
      appIH IHeval3 Hev3.
      now appIH IHeval2 Hev2.
    - repeat f_equal.
      { clear - f f6. revert nms f6. induction f; cbn; intros; depelim f6.
        + reflexivity.
        + f_equal. rewrite <- H0 in H. invs H. eauto. eauto.
      }
    - eapply EGlobalEnv.declared_constant_lookup in isdecl, isdecl0.
      rewrite isdecl in isdecl0. invs isdecl0.
      rewrite e in e0. invs e0.
      now appIH IHeval Hev.
    - f_equal.
      rewrite e in e0. invs e0.
      clear - IHa a0. revert args'0 a0.
      induction a; cbn in *; intros; invs a0.
      + reflexivity.
      + f_equal. eapply IHa. eauto. eapply IHa0; eauto.
        eapply IHa.
    - depelim a. reflexivity.
    - depelim a; reflexivity.
    - reflexivity.
    - inversion evih; rewrite <- H in e; inversion e; subst; eauto.
      eapply EPrimitive.All2_over_undep in X.
      unfold a', a'0. repeat f_equal; eauto. clear H4. eapply EPrimitive.All2_Set_All2 in ev0, ev1.
      clear -X ev1. revert v'0 ev1.  
      induction X; intros; inversion ev1; eauto. f_equal; eauto.
  Qed.

End evalnamed.

Program Definition compile_to_malfunction (efl := named_extraction_env_flags) `{Heap}:
  Transform.t (list (Kernames.kername × EAst.global_decl)) _ _ _
    EWcbvEvalNamed.value SemanticsSpec.value
    (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) (fun _ _ => True) :=
  {| name := "compile to Malfunction";
      pre := fun p =>   EWellformed.wf_glob p.1 /\ (exists t, EWellformed.wellformed (efl := extraction_env_flags) p.1 0 t /\ ∥ represents [] [] p.2 t∥) /\
                       good_for_extraction named_extraction_env_flags p ;
      transform p _ := compile_program p ;
      post := fun p => CompileCorrect.wellformed (map (fun '(i,_) => i) p.1) [] p.2 ;
      obseq p _ p' v v' := forall (hh:heap), v' = CompileCorrect.compile_value p.1 v
  |}.
Next Obligation. sq.
  erewrite map_ext.
  eapply compile_wellformed.
  eapply H3. eapply H4. eapply H5.
  intros. now destruct x.
Qed.
Next Obligation.
  red. intros. exists (compile_value p.1 v); eauto. 
Qed.

Program Definition post_verified_named_erasure_pipeline (efl := EWellformed.all_env_flags) `{Heap}:
 Transform.t EAst.global_declarations _ _ _ _ EWcbvEvalNamed.value  
 (eval_eprogram EConstructorsAsBlocks.block_wcbv_flags)
 (fun p v => ∥ EWcbvEvalNamed.eval p.1 [] p.2 v ∥)  :=
  enforce_extraction_conditions ▷
  implement_box_transformation ▷
  name_annotation.

Program Definition verified_named_erasure_pipeline (efl := EWellformed.all_env_flags) `{Heap}:
 Transform.t global_env_ext_map _ _ _ _ EWcbvEvalNamed.value 
             PCUICTransform.eval_pcuic_program
             (fun p v => ∥ EWcbvEvalNamed.eval p.1 [] p.2 v ∥) :=
  verified_erasure_pipeline ▷
  post_verified_named_erasure_pipeline.

Program Definition verified_malfunction_pipeline (efl := EWellformed.all_env_flags) `{Heap} :
 Transform.t global_env_ext_map _ _ _ _ SemanticsSpec.value 
             PCUICTransform.eval_pcuic_program
             (fun _ _ => True) :=
  verified_named_erasure_pipeline ▷
  compile_to_malfunction.
Next Obligation.
  cbn. intros.
  destruct p as [Σ t]. split. apply H1. sq. split. 2: eauto.
  eexists. split. 2:sq. all:eauto. 
Qed.

Section compile_malfunction_pipeline.

  Variable HP : Pointer.
  Variable HH : Heap.

  Variable Σ : global_env_ext_map.
  Variable t : term.
  Variable T : term.

  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.
  Variable expt : expanded Σ.1 [] t.
  Variable typing : ∥Σ ;;; [] |- t : T∥.

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Definition compile_malfunction_pipeline := transform verified_malfunction_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _).
  
End compile_malfunction_pipeline. 

Arguments compile_malfunction_pipeline {_ _ _ _ _ _} _ _ _ {_}.

Lemma annotate_firstorder_evalue_block Σ v_t :
  firstorder_evalue_block Σ v_t ->
  firstorder_evalue_block (annotate_env [] Σ) v_t.
Proof.
  eapply firstorder_evalue_block_elim. intros.
  econstructor; eauto.
  unfold EGlobalEnv.lookup_constructor_pars_args,
    EGlobalEnv.lookup_constructor,
    EGlobalEnv.lookup_inductive,
    EGlobalEnv.lookup_minductive in *.
  rewrite lookup_env_annotate.
  destruct EGlobalEnv.lookup_env; cbn in *; try congruence.
  destruct g; cbn in *; congruence.
Qed.

Lemma implement_box_firstorder_evalue_block {efl : EEnvFlags} Σ v_t :
  firstorder_evalue_block Σ v_t ->
  firstorder_evalue_block (implement_box_env Σ) v_t.
Proof.
  eapply firstorder_evalue_block_elim. intros.
  econstructor; eauto.
  erewrite lookup_constructor_pars_args_implement_box.
  eassumption.
Qed.

Lemma compile_value_box_mkApps x Σb args0: 
compile_value_box Σb (PCUICAst.mkApps x args0) [] =
compile_value_box Σb x (map (fun v => compile_value_box Σb v []) args0).
Proof.
rewrite <- (app_nil_r (map _ _)). 
generalize (@nil EAst.term) at 1 3. induction args0 using rev_ind; cbn.
- eauto.
- intros l. rewrite PCUICAstUtils.mkApps_nonempty; eauto.
  cbn. rewrite removelast_last last_last. rewrite IHargs0. 
  destruct x; cbn; eauto.
  + do 2 f_equal. repeat rewrite map_app. cbn. now repeat rewrite <- app_assoc.   
  + destruct pcuic_lookup_inductive_pars; eauto.
    do 2 f_equal. repeat rewrite map_app. cbn. now repeat rewrite <- app_assoc.
Qed.

Fixpoint compile_value_mf_aux `{Pointer} Σb (t : EAst.term) : SemanticsSpec.value :=
  match t with
  | EAst.tConstruct i m [] =>
    match lookup_constructor_args Σb i with
      | Some num_args => 
          let num_args_until_m := firstn m num_args in
          let index := #| filter (fun x => match x with 0 => true | _ => false end) num_args_until_m| in
          SemanticsSpec.value_Int (Malfunction.Int, BinInt.Z.of_nat index)
      | None => fail "inductive not found"
    end
  | EAst.tConstruct i m args =>
    match lookup_constructor_args Σb i with
      | Some num_args => 
          let num_args_until_m := firstn m num_args in
          let index := #| filter (fun x => match x with 0 => false | _ => true end) num_args_until_m| in
          Block (utils_array.int_of_nat index, map (compile_value_mf_aux Σb) args)
      | None => fail "inductive not found"
    end
  | _ => not_evaluated
  end.

Definition compile_value_mf' `{Pointer} Σ Σb t :=   
  compile_value_mf_aux Σb (compile_value_box (PCUICExpandLets.trans_global_env Σ) t []).


Fixpoint eval_fo (t: EAst.term) : EWcbvEvalNamed.value :=   
  match t with 
    | EAst.tConstruct ind c args => vConstruct ind c (map eval_fo args)
    | _ => vClos "" (EAst.tVar "error") []
  end. 


Section compile_value_mf.

  Variable HP : Pointer.
  Variable HH : Heap.

  Variable Σ : global_env_ext_map.
  Variable no_axioms : PCUICClassification.axiom_free Σ.
  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.

  Variable t : term.
  Variable expt : expanded Σ.1 [] t.

  Variable v : term.

  Variable i : inductive.
  Variable u : Instance.t.
  Variable args : list term.

  Variable fo : firstorder_ind Σ (firstorder_env Σ) i.

  Variable noParam : forall i mdecl, lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0. 

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.


  Lemma compile_value_eval_fo_repr {Henvflags:EWellformed.EEnvFlags} :
    PCUICFirstorder.firstorder_value Σ [] t ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) t [] in
    ∥ EWcbvEvalNamed.represents_value (eval_fo v) v∥.
  Proof.
  intro H. cbn. pattern t.
  refine (PCUICFirstorder.firstorder_value_inds _ _ _ _ _ H). 
  intros. rewrite compile_value_box_mkApps. cbn.
  eapply PCUICValidity.validity in X. eapply PCUICInductiveInversion.wt_ind_app_variance in X as [mdecl [? ?]].  
  unfold pcuic_lookup_inductive_pars. unfold lookup_inductive,lookup_inductive_gen,lookup_minductive_gen in e.
  rewrite PCUICExpandLetsCorrectness.trans_lookup. specialize (noParam (inductive_mind i0)). 
  case_eq (lookup_env Σ (inductive_mind i0)); cbn.  
  2: { intro neq. rewrite neq in e. inversion e. }
  intros ? Heq. rewrite Heq in e. rewrite Heq. destruct g; cbn; [inversion e |]. destruct nth_error; inversion e; subst; cbn.  
  assert (ind_npars m = 0) by eauto. rewrite H3. rewrite skipn_0.
  rewrite map_map.
  eapply All_sq in H1. sq. constructor.
  eapply EPrimitive.All2_All2_Set. solve_all.
  Qed.    

  Lemma implement_box_fo {Henvflags:EWellformed.EEnvFlags} p : 
  PCUICFirstorder.firstorder_value Σ [] p ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env (trans_env_env Σ)) p [] in
    v = implement_box v.
  Proof.
  intro H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
  v = implement_box v) _ _ H); intros. revert v0. 
  rewrite compile_value_box_mkApps. intro v0. cbn in v0. revert v0.
  unfold pcuic_lookup_inductive_pars. rewrite PCUICExpandLetsCorrectness.trans_lookup.
  case_eq (lookup_env Σ (inductive_mind i0)).
  2: { intro Hlookup; now rewrite Hlookup. }       
  intros ? Hlookup; rewrite Hlookup. destruct g; eauto; simpl.
  specialize (noParam (inductive_mind i0)). assert (ind_npars m = 0) by eauto. rewrite H3. 
  rewrite skipn_0. set (map _ _). simpl. rewrite EImplementBox.implement_box_unfold_eq. simpl.
  f_equal. erewrite MCList.map_InP_spec. clear -H1. unfold l; clear l. induction H1; eauto. simpl. f_equal; eauto.
  Qed. 
        
  Lemma represent_value_eval_fo p : 
    PCUICFirstorder.firstorder_value Σ [] p ->
    let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    forall v', represents_value v' v -> v' = eval_fo v.
  Proof.
    intro H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
    forall v', represents_value v' v -> v' = eval_fo v) _ _ H); intros. revert H3. 
    unfold v0. clear v0. rewrite compile_value_box_mkApps.
    eapply Forall_All in H1. cbn.
    unfold pcuic_lookup_inductive_pars. rewrite PCUICExpandLetsCorrectness.trans_lookup.
    case_eq (lookup_env Σ (inductive_mind i0)).
    2: { intro Hlookup; now rewrite Hlookup. }
    intros ? Hlookup; rewrite Hlookup. destruct g; eauto; simpl.
    { inversion 1. }
    specialize (noParam (inductive_mind i0)). assert (ind_npars m = 0) by eauto. rewrite H3. 
    rewrite skipn_0. inversion 1; subst; eauto. clear H3 H4. 
    f_equal. clear X H0 H2. revert vs H7. induction H1; cbn; inversion 1; f_equal; subst. 
    - eapply p0; eauto.
    - eapply IHAll; eauto.
  Qed.


  Lemma verified_named_erasure_pipeline_lookup_env_in kn  
  (efl := EInlineProjections.switch_no_params all_env_flags)  {has_rel : has_tRel} {has_box : has_tBox}  
  T (typing : ∥Σ ;;; [] |- t : T∥) :
  let Σ_t := (transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _)).1 in
  forall decl, 
    EGlobalEnv.lookup_env Σ_t kn = Some decl ->
    exists decl', 
    PCUICAst.PCUICEnvironment.lookup_global (PCUICExpandLets.trans_global_decls
    (PCUICAst.PCUICEnvironment.declarations
       Σ.1)) kn = Some decl'
     /\ erase_decl_equal (fun decl' => ERemoveParams.strip_inductive_decl (ErasureFunction.erase_mutual_inductive_body decl'))
                          decl decl'.
  Proof.
    intros ? decl. unfold Σ_t, verified_named_erasure_pipeline.
    destruct_compose; intro; cbn. rewrite lookup_env_annotate. unfold run, time.  
    destruct_compose; intro; cbn. rewrite lookup_env_implement_box.
    unfold enforce_extraction_conditions. unfold transform at 1.
    intro Hlookup. set (EGlobalEnv.lookup_env _ _) in Hlookup. case_eq o.
    2:{ intro Heq; rewrite Heq in Hlookup; inversion Hlookup. }
    intros decl' Heq.
    unshelve epose proof (verified_erasure_pipeline_lookup_env_in _ _ _ _ _ _ _ _ _ _ Heq) as [? [? ?]]; eauto.
    eexists; split; eauto. rewrite Heq in Hlookup.
    inversion Hlookup; subst; clear Hlookup. 
    destruct decl', x; cbn in *; eauto.
    destruct EAst.cst_body; eauto.
  Qed.

  Definition compile_named_value p := eval_fo (compile_value_box (PCUICExpandLets.trans_global_env Σ) p []).

  Variable T : term. 
  Variable typing : ∥Σ ;;; [] |- t : T∥.

  Let Σ_t := (compile_malfunction_pipeline expΣ expt typing).1.
  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.
  
  Let Σ_v := (transform verified_named_erasure_pipeline (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ _ Heval)).1.
  Let Σ_t' := (transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _)).1.

  Let compile_value_mf Σ v := compile_value_mf' Σ Σ_v v.

  Lemma compile_value_mf_eq {Henvflags: EWellformed.EEnvFlags} p : 
    PCUICFirstorder.firstorder_value Σ [] p ->
    compile_value_mf Σ p = compile_value Σ_v (compile_named_value p).
  Proof.
    intros H. refine (PCUICFirstorder.firstorder_value_inds _ _ 
      (fun p => compile_value_mf Σ p = compile_value Σ_v (compile_named_value p)) _ _ H).
    unfold compile_named_value.
    intros. unfold compile_value_mf, compile_value_mf'. repeat rewrite compile_value_box_mkApps. 
    clear H. cbn. specialize (noParam (inductive_mind i0)). 
    unfold pcuic_lookup_inductive_pars. rewrite PCUICExpandLetsCorrectness.trans_lookup.
    eapply PCUICValidity.validity in X. eapply PCUICInductiveInversion.wt_ind_app_variance in X as [mdecl [? _]].  
    unfold lookup_inductive,lookup_inductive_gen,lookup_minductive_gen in e.
    destruct lookup_env; cbn; try inversion e.
    destruct g; cbn; try inversion e. 
    assert (Hnpars: ind_npars m = 0) by eauto. rewrite Hnpars. 
    rewrite skipn_0. destruct lookup_constructor_args; cbn.
    2: { destruct map; eauto. }
    destruct args0; cbn; eauto.
    repeat f_equal; inversion H1; subst; clear H1; eauto.
    repeat rewrite map_map. eapply map_ext_Forall; eauto.
  Qed. 

End compile_value_mf.

Section malfunction_pipeline_theorem.

  Variable HP : Pointer.
  Variable HH : Heap.

  Variable Σ : global_env_ext_map.
  Variable no_axioms : PCUICClassification.axiom_free Σ.
  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.

  Variable t : term.
  Variable expt : expanded Σ.1 [] t.

  Variable v : term.

  Variable i : inductive.
  Variable u : Instance.t.
  Variable args : list term.

  Variable fo : firstorder_ind Σ (firstorder_env Σ) i.

  Variable noParam : forall i mdecl, lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0. 

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Variable typing : ∥Σ ;;; [] |- t : mkApps (tInd i u) args∥. 
  Let Σ_t := (compile_malfunction_pipeline expΣ expt typing).1.
  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.
  
  Let Σ_v := (transform verified_named_erasure_pipeline (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ _ Heval)).1.
  Let Σ_t' := (transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _)).1.

  Variable (Henvflags:EWellformed.EEnvFlags).
  
  Variable (Haxiom_free : Extract.axiom_free Σ).

  Opaque compose. 

  Lemma verified_malfunction_pipeline_lookup (efl := extraction_env_flags) kn g : 
    EGlobalEnv.lookup_env Σ_v kn = Some g ->
    EGlobalEnv.lookup_env Σ_t' kn = Some g. 
  Proof.
    unfold Σ_t', Σ_v. unfold verified_named_erasure_pipeline, post_verified_named_erasure_pipeline.
    repeat (destruct_compose; intro). 
    unfold transform at 1 3; cbn -[transform].
    repeat (destruct_compose; intro).  
    unfold transform at 1 3; cbn -[transform].
    repeat (destruct_compose; intro). 
    unfold transform at 1 3; cbn -[transform].
    intro Hlookup.
    rewrite lookup_env_annotate. rewrite lookup_env_annotate in Hlookup.  
    rewrite lookup_env_implement_box. rewrite lookup_env_implement_box in Hlookup.
    case_eq (EGlobalEnv.lookup_env (transform verified_erasure_pipeline (Σ, v)
               (precond2 Σ t ( mkApps (tInd i u) args) HΣ expΣ expt typing Normalisation v Heval)).1 kn).
    2: { intros He. rewrite He in Hlookup; inversion Hlookup. }
    intros ? Heq. rewrite Heq in Hlookup. cbn in Hlookup. 
    eapply extends_lookup in Heq. rewrite Heq. eauto.
    2: { eapply verified_erasure_pipeline_extends; eauto. }
    epose proof (correctness _ _ H4). cbn in H5. now destruct H4.
  Qed.


  Lemma verified_malfunction_pipeline_compat p (efl := extraction_env_flags) 
    : firstorder_evalue_block Σ_v p -> compile_value Σ_t' (eval_fo p) = compile_value Σ_v (eval_fo p).
  Proof.
    intros H. eapply firstorder_evalue_block_elim with (P := fun p => compile_value Σ_t' (eval_fo p) = compile_value Σ_v (eval_fo p)); [|eauto] ; intros. 
    cbn. set (precond2 _ _ _ _ _ _ _ _ _ _) in Σ_v. unfold EGlobalEnv.lookup_constructor_pars_args in H0. cbn in H0.  
    unfold lookup_constructor_args, EGlobalEnv.lookup_constructor,
      EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. cbn.
    case_eq (EGlobalEnv.lookup_env Σ_v (inductive_mind i0)).
    2:{ intro HNone. rewrite HNone in H0; inversion H0. } 
    intros ? HSome. rewrite HSome in H0; cbn in H0.
    eapply verified_malfunction_pipeline_lookup in HSome.
    rewrite HSome.
    destruct args0; cbn in *.  
    { destruct g; cbn; eauto. }
    { destruct g; cbn; [eauto|]. 
      destruct (nth_error _ _); cbn; [|eauto].
      inversion H2. subst. destruct H5.   
      enough (map (compile_value Σ_t') (map eval_fo args0) = map (compile_value Σ_v) (map eval_fo args0)).
      { now destruct H3. }
      { clear - H6. induction H6; cbn. eauto. now destruct H, IHForall. } 
    }
  Qed.

  Import SemanticsSpec.

  Let compile_value_mf Σ v := compile_value_mf' Σ Σ_v v.

  Lemma verified_malfunction_pipeline_theorem_gen (efl := extraction_env_flags) Σ' :
    malfunction_env_prop Σ_t' Σ' ->
    forall (h:heap), eval Σ' empty_locals h (compile_malfunction_pipeline expΣ expt typing).2 h (compile_value_mf Σ v).
  Proof.
    intros HΣ'; cbn.  
    unshelve epose proof (verified_erasure_pipeline_theorem _ _ _ _ _ _ _ _ _ _ _ _ _ Heval); eauto.
    unfold compile_value_mf; rewrite compile_value_mf_eq; eauto. 
    { eapply fo_v; eauto. }
    unfold compile_named_value. rewrite <- verified_malfunction_pipeline_compat.
    2: { unfold Σ_v,verified_named_erasure_pipeline, post_verified_named_erasure_pipeline. repeat (destruct_compose ; intros).
         unfold transform at 1; cbn -[transform]. 
         unfold transform at 1; cbn -[transform].
         unfold transform at 1; cbn -[transform].
         unshelve epose proof (verified_erasure_pipeline_firstorder_evalue_block _ _ _ _ _ _ _ _ _ _ _ typing _ _); eauto.
         eapply annotate_firstorder_evalue_block.
         eapply implement_box_firstorder_evalue_block.
         eassumption.
       }
    unfold compile_malfunction_pipeline, verified_malfunction_pipeline, verified_named_erasure_pipeline,
       post_verified_named_erasure_pipeline in *.
    intros. destruct_compose ; intros. 
    unfold compile_to_malfunction. unfold transform at 1. simpl.  
    repeat (destruct_compose ; intros). unfold name_annotation. unfold transform at 1 4.
    repeat (destruct_compose ; intros). simpl. unfold enforce_extraction_conditions. unfold transform at 1 3.
    unshelve epose proof (Himpl := implement_box_transformation.(preservation) _ _ _ _); try eapply H1; eauto.
    destruct Himpl as [? [Himpl_eval Himpl_obs]].
    unfold obseq in Himpl_obs. simpl in Himpl_obs. rewrite Himpl_obs in Himpl_eval.
    unshelve epose proof (Hname := name_annotation.(preservation) _ _ _ _); try eapply H2; eauto.
    { rewrite Himpl_obs; eauto. }
    destruct Hname as [? [Hname_eval Hname_obs]]. simpl in *. revert Hname_eval. destruct_compose; intros.
    unfold Σ_t'. repeat (destruct_compose ; intros).
    unfold name_annotation. unfold transform at 3.
    repeat (destruct_compose ; intros). simpl. unfold enforce_extraction_conditions. unfold transform at 3. sq.
    eapply compile_correct with (Γ := []). intros.
    -  rename H7 into H7'.  rename H8 into H7.  split.
      + eapply H3. unfold enforce_extraction_conditions. unfold transform at 1.
        unfold EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *.
        rewrite lookup_env_annotate lookup_env_implement_box in H7. cbn in H7. clear - H7.
        instantiate (2:= i0).
        destruct EGlobalEnv.lookup_env; cbn in *; try inversion H7.  destruct g; cbn in *; eauto.
        destruct c; cbn in *. destruct cst_body0; cbn in *; inversion H7.           
        + eapply H3. unfold enforce_extraction_conditions. unfold transform at 1.
        unfold EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. 
        rewrite lookup_env_annotate lookup_env_implement_box in H7. cbn in H7. clear - H7.
        instantiate (2:= i0).
        destruct EGlobalEnv.lookup_env; cbn in *; try inversion H7.  destruct g; cbn in *; eauto.
        destruct c; cbn in *. destruct cst_body0; cbn in *; inversion H7.           
    - eauto.  
    - revert HΣ'. unfold malfunction_env_prop, Σ_t'.
      destruct_compose ; intros. 
      revert HΣ'. destruct_compose ; intros. unfold name_annotation in *.
      unfold transform at 1 4 7 in HΣ'. 
      revert HΣ'. destruct_compose ; intros. simpl in HΣ'.
      eapply HΣ'; eauto.
    - rewrite Himpl_obs in Hname_obs.
      rewrite <- implement_box_fo in Hname_obs; eauto. 2: { eapply fo_v; eauto. }
      eapply represent_value_eval_fo in Hname_obs; eauto. 2: { eapply fo_v; eauto. }
      now rewrite Hname_obs in Hname_eval.
  Qed. 

  Lemma verified_named_erasure_pipeline_fo :
    firstorder_evalue_block Σ_v (compile_value_box (PCUICExpandLets.trans_global_env Σ) v []).
  Proof.
    unfold Σ_v, verified_named_erasure_pipeline, post_verified_named_erasure_pipeline.
    repeat (destruct_compose; simpl; intro).
    unshelve epose proof ErasureCorrectness.verified_erasure_pipeline_firstorder_evalue_block _ _ _ _ _ _ _ _ _ _ _ typing _ _; eauto using Heval.
    set (v' := compile_value_box _ _ _) in *. clearbody v'.
    clear -H2. eapply firstorder_evalue_block_elim; eauto. clear. intros; econstructor; eauto. 
    clear -H0. cbn in *. 
    unfold EGlobalEnv.lookup_constructor_pars_args, EGlobalEnv.lookup_constructor,
    EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. cbn.
    rewrite lookup_env_annotate lookup_env_implement_box.
    unfold enforce_extraction_conditions. unfold transform at 1.
    destruct EGlobalEnv.lookup_env; [|inversion H0].
    destruct g; inversion H0; subst; eauto.
  Qed.    
    
  Transparent compose.  
  
  Lemma verified_named_erasure_pipeline_lookup_env_in' kn  
  (efl := EInlineProjections.switch_no_params all_env_flags)  {has_rel : has_tRel} {has_box : has_tBox}  :
  forall decl, 
    EGlobalEnv.lookup_env Σ_v kn = Some decl ->
    exists decl', 
    PCUICAst.PCUICEnvironment.lookup_global (PCUICExpandLets.trans_global_decls
    (PCUICAst.PCUICEnvironment.declarations
       Σ.1)) kn = Some decl'
     /\ erase_decl_equal (fun decl' => ERemoveParams.strip_inductive_decl (ErasureFunction.erase_mutual_inductive_body decl'))
                          decl decl'.
  Proof.
    intros; eapply verified_named_erasure_pipeline_lookup_env_in. 1-2: eauto.  
    apply verified_malfunction_pipeline_lookup in H. exact H.
  Qed. 

End malfunction_pipeline_theorem.

Section malfunction_pipeline_theorem_red.

  Variable HP : Pointer.
  Variable HH : Heap.

  Variable Σ : global_env_ext_map.
  Variable no_axioms : PCUICClassification.axiom_free Σ.
  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.

  Variable t : term.
  Variable expt : expanded Σ.1 [] t.

  Variable v : term.

  Variable i : inductive.
  Variable u : Instance.t.
  Variable args : list term.

  Variable typing : ∥Σ ;;; [] |- t : mkApps (tInd i u) args∥.

  Variable fo : firstorder_ind Σ (firstorder_env Σ) i.

  Variable noParam : forall i mdecl, lookup_env Σ i = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0. 

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Let Σ_t := (compile_malfunction_pipeline expΣ expt typing).1.

  Variable v_red : ∥Σ;;; [] |- t ⇝* v∥.
  Variable v_irred : forall t', (Σ;;; [] |- v ⇝ t') -> False.

  Lemma red_eval : ∥PCUICWcbvEval.eval Σ t v∥.
  Proof.
    destruct typing as [typing']. sq. 
    eapply PCUICValidity.validity in typing' as Hv.
    destruct Hv as [_ [? [HA _]]].
    eapply PCUICValidity.inversion_mkApps in HA as (A & HA & _).
    eapply PCUICInversion.inversion_Ind in HA as (mdecl & idecl & _ & HA & _); eauto.

    eapply PCUICNormalization.wcbv_standardization_fst; eauto.
    instantiate (1 := mdecl).
    1: { destruct HΣ. 
         unshelve eapply declared_inductive_to_gen in HA; eauto. }
    intros [t' ht]. eauto.
  Qed.

  Let Σ_v := (transform verified_named_erasure_pipeline (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ _ red_eval)).1.
  Let Σ_t' := (transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _)).1.

  Let compile_value_mf Σ v := compile_value_mf' Σ Σ_v v.

  Variables (Henvflags:EWellformed.EEnvFlags).
  
  Variable (Haxiom_free : Extract.axiom_free Σ).

  Import SemanticsSpec.

  Lemma verified_malfunction_pipeline_theorem (efl := extraction_env_flags) Σ' :
    malfunction_env_prop Σ_t' Σ' ->
    forall h, eval Σ' empty_locals h (compile_malfunction_pipeline expΣ expt typing).2 h (compile_value_mf Σ v).
  Proof. 
    now eapply verified_malfunction_pipeline_theorem_gen.
  Qed.  

End malfunction_pipeline_theorem_red.

Section malfunction_pipeline_wellformed.

  Variable HP : Pointer.
  Variable HH : Heap.

  Variable Σ : global_env_ext_map.
  Variable no_axioms : PCUICClassification.axiom_free Σ.
  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.

  Opaque implement_box.

  Lemma verified_named_erasure_pipeline_eta_app t u pre :
    ∥ Extract.nisErasable Σ [] (tApp t u) ∥ ->
   PCUICEtaExpand.expanded Σ.1 [] t ->
    exists pre' pre'',
  let trapp := transform verified_named_erasure_pipeline (Σ, tApp t u) pre in
  let trt := transform verified_named_erasure_pipeline (Σ, t) pre' in
  let tru := transform verified_named_erasure_pipeline (Σ, u) pre'' in
    (EGlobalEnv.extends trt.1 trapp.1 /\ EGlobalEnv.extends tru.1 trapp.1) /\ 
    trapp = (trapp.1, EAst.tApp trt.2 tru.2).
  Proof.
    set (P := Transform.pre _). intros.  
    unshelve epose proof (erasure_pipeline_extends_app _ _ _ pre _ _) as [pre' [pre'' [ [? ?] Happ]]]; eauto.
    exists pre', pre''. unfold verified_named_erasure_pipeline, post_verified_named_erasure_pipeline.
    repeat (destruct_compose; intros).
    unfold transform at 1 4 7 10 13 16 19 22. cbn -[P transform].
    repeat (destruct_compose; intros).   
    unfold transform at 1 4 7 10 13 16 19 22. cbn -[P transform].
    repeat split. 
    { unshelve eapply annotate_extends, implement_box_env_extends.
      - exact extraction_env_flags. 
      - eauto.
      - exact H1. 
      - now eapply right_flags_in_glob.
      - now eapply right_flags_in_glob. }
    { unshelve eapply annotate_extends, implement_box_env_extends.
      - exact extraction_env_flags. 
      - eauto.
      - exact H2. 
      - now eapply right_flags_in_glob.
      - now eapply right_flags_in_glob. }
    rewrite Happ.  now rewrite (implement_box_mkApps _ [_]).
  Qed.

  Transparent implement_box.
  
  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Lemma compile_malfunction_pipeline_app : forall t u Hpre,
  ∥Extract.nisErasable Σ [] (tApp t u) ∥ ->
  expanded Σ.1 [] t ->
  exists pre' pre'',
  (transform verified_malfunction_pipeline (Σ, tApp t u) Hpre).2 = 
  Mapply_u (transform verified_malfunction_pipeline (Σ, t) pre').2 (transform verified_malfunction_pipeline (Σ, u) pre'').2.
  Proof.
    intros ? ? ? Herase Hexpand. unfold verified_malfunction_pipeline.
    unshelve epose proof (verified_named_erasure_pipeline_eta_app _ _ Hpre Herase Hexpand) as [pre' [pre'' [[? ?] Happ]]].
    exists pre', pre''. 
    repeat (destruct_compose; intros).
    unfold transform at 1 3 5. cbn -[transform].
    revert Happ. set (transform _ _ _). intro. 
    rewrite Happ.  
    destruct H2 as [? [[? [? ?]] ?]]. sq.   
    eapply compile_extends in H. 2-3: eauto. 
    destruct H3 as [? [[? [? ?]] ?]]. sq.
    eapply compile_extends in H0. 2-3: eauto.
    revert H H0. clear. unfold p. clear p.
    repeat set (transform _ _ _). clearbody p p0 p1.
    rewrite compile_equation_7; intros; f_equal; eauto. 
  Qed. 

  Variable t A : term.
  Variable expt : expanded Σ.1 [] t.

  Variable typing : ∥Σ ;;; [] |- t : A∥.

  Let Σ_t := (transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _)).1.

  Lemma verified_malfunction_pipeline_wellformed (efl := named_extraction_env_flags) : 
    CompileCorrect.wellformed (map fst (compile_env Σ_t)) [] (compile_malfunction_pipeline expΣ expt typing).2.
  Proof.  
    unfold Σ_t, compile_malfunction_pipeline, verified_malfunction_pipeline.
    destruct_compose; intro; cbn.
    unfold compile_to_malfunction, transform at 1. cbn.  
    epose proof (correctness verified_named_erasure_pipeline) as [? [? [? ?]]]. destruct H2. 
    eapply compile_wellformed; eauto. 
    eapply few_enough_blocks; eauto.
  Qed. 

  Lemma verified_named_erasure_pipeline_inductive_irrel t' expt'
  (efl := EInlineProjections.switch_no_params all_env_flags) {has_rel : has_tRel} {has_box : has_tBox}  
  T' (typing' : ∥Σ ;;; [] |- t' : T'∥) :
  let Σ_u := (transform verified_named_erasure_pipeline (Σ, t') (precond _ _ _ _ expΣ expt' typing' _)).1 in 
  forall kn m m', 
    EGlobalEnv.lookup_env Σ_t kn = Some (EAst.InductiveDecl m) ->
    EGlobalEnv.lookup_env Σ_u kn = Some (EAst.InductiveDecl m')  -> m = m'.
  Proof.
    intros ? ? ? ? Hdecl Hdecl'.
    eapply verified_named_erasure_pipeline_lookup_env_in in Hdecl as [? [? ?]]; eauto.
    eapply verified_named_erasure_pipeline_lookup_env_in in Hdecl' as [? [? ?]]; eauto.
    rewrite H1 in H. inversion H; subst. clear H H1. cbn in H0, H2.
    destruct x; inversion H2. now subst.
  Qed.

  Derive Signature for firstorder_evalue_block.
  
  Opaque EGlobalEnv.lookup_env.

  Lemma compile_value_mf_fo' `{Pointer} (efl := named_extraction_env_flags) X u expu T' (typing' : ∥Σ ;;; [] |- u : T'∥) : 
     let Σ_u := (Transform.transform verified_named_erasure_pipeline (Σ, u) (precond _ _ _ _ expΣ expu typing' _)).1 in
     firstorder_evalue_block Σ_t X ->
     firstorder_evalue_block Σ_u X -> 
     (forall kn m m', 
     EGlobalEnv.lookup_env Σ_t kn = Some (EAst.InductiveDecl m) ->
     EGlobalEnv.lookup_env Σ_u kn = Some (EAst.InductiveDecl m')  -> m = m') ->
     compile_value_mf_aux Σ_u X = 
     compile_value_mf_aux Σ_t X.
  Proof.
    intros ?. revert X. apply: firstorder_evalue_block_elim.
    intros. rename H4 into Hirr. depelim H3. cbn. clearbody Σ_t Σ_u. unfold lookup_constructor_args.
    unfold EGlobalEnv.lookup_constructor_pars_args, EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *.
    cbn in H0, H3. case_eq (EGlobalEnv.lookup_env Σ_t (inductive_mind i)).
    2: { intro e. rewrite e in H0. depelim H0. }
    case_eq (EGlobalEnv.lookup_env Σ_u (inductive_mind i)).
    2: { intro e; rewrite e in H3. depelim H3. }
    intros [] Hdecl' [] Hdecl; rewrite Hdecl in H0; rewrite Hdecl' in H3; inversion H0; inversion H3.
    cbn. enough (m = m0).
    { subst. destruct args; cbn; [eauto|].
      destruct nth_error; cbn; [|eauto]. do 2 eapply f_equal. inversion H2; inversion H4. subst. 
      specialize (H9 H13). eapply Forall_mix in H10; try exact H14. eapply Forall_impl in H10.
      erewrite map_ext_Forall. 2: exact H10. 2: { intros ? [? ?]. eapply H8; eauto. } set (map _ _). 
      apply f_equal2; eauto. }
    symmetry. eapply Hirr; eauto.
  Qed. 
  
  Transparent EGlobalEnv.lookup_env.

  Lemma compile_value_mf_fo `{Pointer} (efl := named_extraction_env_flags) X u expu T' (typing' : ∥Σ ;;; [] |- u : T'∥) : 
  let Σ_u := (Transform.transform verified_named_erasure_pipeline (Σ, u) (precond _ _ _ _ expΣ expu typing' _)).1 in
  firstorder_evalue_block Σ_t X ->
  firstorder_evalue_block Σ_u X -> 
  compile_value_mf_aux Σ_u X = 
  compile_value_mf_aux Σ_t X.
  Proof.
    intros ? Hfo Hfo'. eapply compile_value_mf_fo'. 1: exact Hfo. 1: exact Hfo'.
    eapply verified_named_erasure_pipeline_inductive_irrel; eauto.
  Qed.  

End malfunction_pipeline_wellformed.

About verified_malfunction_pipeline_theorem.
Print Assumptions verified_malfunction_pipeline_theorem.

Local Existing Instance CanonicalHeap.
Local Existing Instance CanonicalPointer.

Record malfunction_pipeline_config := 
  { erasure_config :> erasure_configuration; 
    prims : list (kername * (string * string)) }.

(* This also optionally runs typed erasure and/or the cofix to fix translation *)
Program Definition switchable_erasure_pipeline econf :=
  if econf.(enable_typed_erasure) then verified_typed_erasure_pipeline econf
  else verified_erasure_pipeline ▷ (optional_cofix_to_fix_transform econf).
Next Obligation.
Proof.
  unfold optional_cofix_to_fix_transform.
  destruct enable_cofix_to_fix => //.
Qed.

Program Definition malfunction_pipeline (efl := EWellformed.all_env_flags) 
  (config : malfunction_pipeline_config) :
  Transform.t _ _ _ _ _ _ TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  pre_erasure_pipeline ▷ 
  switchable_erasure_pipeline config ▷ 
  post_verified_named_erasure_pipeline ▷ 
  compile_to_malfunction .
Next Obligation.
  unfold switchable_erasure_pipeline.
  destruct enable_typed_erasure => //.
Qed.
Next Obligation.
  intuition auto; destruct H; intuition eauto.
Qed.

Fixpoint extract_names (t : Ast.term) : list ident :=
  match t with
  | Ast.tConst kn _ => [Kernames.string_of_kername kn]
  | Ast.tApp (Ast.tConstruct _ _ _) [_ ; _ ; l ; Ast.tConst kn _ ] => (Kernames.string_of_kername kn) :: extract_names l
  | _ => []
  end.

Definition compile_malfunction_gen (cf := config.extraction_checker_flags) config (p : Ast.Env.program) 
  : string :=
  let nms := extract_names p.2 in
  let p' := run (malfunction_pipeline config) p (todo "assume we run compilation on a welltyped term"%bs) in
  time "Pretty printing"%bs (fun p_c =>(@to_string _ (Serialize_module config.(prims) (rev nms)) p_c)) p'.

Definition default_malfunction_config : malfunction_pipeline_config :=
  {| erasure_config := safe_erasure_config; prims := [] |}.

Definition compile_malfunction (cf := config.extraction_checker_flags) := 
  compile_malfunction_gen default_malfunction_config.

About compile_malfunction.
