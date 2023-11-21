Require Import ssreflect ssrbool Eqdep_dec.
From Equations Require Import Equations. 
From MetaCoq.Utils Require Import All_Forall MCSquash MCList utils.
From MetaCoq.Common Require Import Transform config Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICFirstorder PCUICCasesHelper BDStrengthening PCUICCumulativity PCUICProgram.
From MetaCoq.Erasure Require Import EWcbvEval EWcbvEvalNamed.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.

From Malfunction Require Import Malfunction Interpreter SemanticsSpec utils_array 
  Compile RealizabilitySemantics Pipeline.

Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.
From MetaCoq.Utils Require Import bytestring.


Section firstorder.

  Context {Σb : list (kername * bool)}.

  Definition CoqType_to_camlType_oneind_type n k decl_type :
    is_true (@firstorder_type Σb n k decl_type) -> camlType.
  Proof.
    unfold firstorder_type. destruct (fst _).
    all: try solve [inversion 1].
    (* case of tRel with a valid index *)
    - intro; exact (Rel (n - S (n0-k))).  (* n0 - k *)  
    (* case of tInd where Σb is saying that inductive_mind is first order *)
    - intro; destruct ind. exact (Adt inductive_mind inductive_ind []).
  Defined.
  

(*  MetaCoq Quote Recursively nat. *)

  Fixpoint CoqType_to_camlType_ind_ctor n m cstr :
    is_true
    (alli
       (fun (k : nat) '{| decl_type := t |} =>
        @firstorder_type Σb m k t) n cstr) -> list camlType. 
  Proof. 
    destruct cstr; cbn; intros. 
    (* no more arguments *)
    * exact [].
    * apply andb_and in H. destruct H. destruct c.
    (* we convert the type of the first type of the constructor *)
      apply CoqType_to_camlType_oneind_type in H.
      refine (H :: _).
    (* we recursively convert *)
      exact (CoqType_to_camlType_ind_ctor _ _ _ H0).
  Defined. 

  Fixpoint CoqType_to_camlType_ind_ctors mind ind_ctors : 
    ind_params mind = [] -> 
    is_true (forallb (@firstorder_con Σb mind) ind_ctors) -> list (list camlType).
  Proof. 
    destruct ind_ctors; intros Hparam H.
    (* no more constructor *)
    - exact [].
    (* a :: ind_ctors constructors *)
    - cbn in H. apply andb_and in H. destruct H. 
      refine (_ :: CoqType_to_camlType_ind_ctors _ _ Hparam H0). clear H0.
      destruct c. unfold firstorder_con in H. cbn in H.
      eapply CoqType_to_camlType_ind_ctor; eauto.     
  Defined. 

  Definition CoqType_to_camlType_oneind mind ind : 
    ind_params mind = [] -> 
    is_true (@firstorder_oneind Σb mind ind) -> list (list camlType).
  Proof.
    destruct ind. intros Hparam H. apply andb_and in H.
    destruct H as [H _]. cbn in *. clear -H Hparam.
    eapply CoqType_to_camlType_ind_ctors; eauto. 
  Defined.

  Lemma bool_irr b (H H' : is_true b) : H = H'.
    destruct b; [| inversion H].
    assert (H = eq_refl).
    eapply (K_dec (fun H => H = eq_refl)); eauto.
    etransitivity; eauto. 
    eapply (K_dec (fun H => eq_refl = H)); eauto.
    Unshelve. all: cbn; eauto. 
    all: intros b b'; pose (Coq.Bool.Bool.bool_dec b b'); intuition. 
  Qed.

  Lemma CoqType_to_camlType_oneind_type_fo n k decl_type Hfo :
    let T := CoqType_to_camlType_oneind_type n k decl_type Hfo in
    is_true (negb (isArrow T)).
  Proof.
    unfold CoqType_to_camlType_oneind_type.
    unfold firstorder_type in Hfo.
    set (fst (PCUICAstUtils.decompose_app decl_type)) in *.
    destruct t; inversion Hfo; cbn; eauto. 
    now destruct ind.
  Qed.     

  Lemma CoqType_to_camlType_oneind_fo mind ind Hparam Hfo larg T : 
    In larg (CoqType_to_camlType_oneind mind ind Hparam Hfo) -> 
    In T larg -> is_true (negb (isArrow T)).
  Proof. 
    destruct mind, ind. revert Hfo. induction ind_ctors0; intros Hfo Hlarg HT.
    - cbn in *; destruct andb_and. destruct (a Hfo). destruct (in_nil Hlarg).
    - cbn in Hlarg. destruct andb_and. destruct (a0 Hfo). 
      destruct andb_and. destruct (a1 i0). destruct a.
      unfold In in Hlarg. destruct Hlarg.
      2: { eapply IHind_ctors0; eauto. cbn. destruct andb_and.
            destruct (a _). rewrite (bool_irr _ i6 i4). eauto.
            Unshelve.
            cbn. apply andb_and. split; cbn; eauto. }
      cbn in Hparam, i3. rewrite Hparam in i3, H. rewrite app_nil_r in i3, H.
      clear - i3 HT H. set (rev cstr_args0) in *. rewrite <- H in HT. revert T HT. clear H. 
      set (Datatypes.length ind_bodies0) in *. revert i3. generalize n 0. clear.
      induction l; cbn; intros; [inversion HT|].
      destruct andb_and. destruct (a0 i3). destruct a.
      unfold In in HT. destruct HT.
      + rewrite <- H; eapply CoqType_to_camlType_oneind_type_fo; eauto.
      + eapply IHl. eauto.
  Qed.    

  (* The following function morally do (map CoqType_to_camlType_oneind) while passing 
  the proof that everything is first order *)

  Fixpoint CoqType_to_camlType_fix ind_bodies0 
    ind_finite0 
    ind_params0 ind_npars0 ind_universes0 
    ind_variance0 {struct ind_bodies0}: 
  ind_params0 = [] -> 
  forall ind_bodies1 : list one_inductive_body,
  is_true
    (forallb
     (@firstorder_oneind Σb
        {|
          Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
          Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
          Erasure.P.PCUICEnvironment.ind_params := ind_params0;
          Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
          Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
          Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
        |}) ind_bodies0) -> list (list (list camlType)).
  Proof.
    destruct ind_bodies0; cbn in *; intros.
    - exact [].
    - refine (CoqType_to_camlType_oneind _ _ _ _ :: CoqType_to_camlType_fix _ _ _ _ _ _ _ _ _); eauto. 
      2-3: unfold firstorder_oneind, firstorder_con; apply andb_and in H0; destruct H0; eauto.
      eauto.
  Defined.   

  Definition CoqType_to_camlType' mind : 
    ind_params mind = [] -> 
    is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind)) -> 
    list (list (list camlType)).
  Proof.
    intros Hparam. destruct mind; unshelve eapply CoqType_to_camlType_fix; eauto.
  Defined.

  Lemma CoqType_to_camlType'_fo mind Hparam Hfo lind larg T : 
    In lind (CoqType_to_camlType' mind Hparam Hfo) -> 
    In larg lind ->
    In T larg -> is_true (negb (isArrow T)).
  Proof.
    destruct mind. cbn in Hparam. unfold CoqType_to_camlType'. cbn in *.
    revert Hfo. 
    enough (forall ind_bodies1
    (Hfo : is_true
            (forallb
               (firstorder_oneind
                  {|
                    Erasure.P.PCUICEnvironment.ind_finite :=
                      ind_finite0;
                    Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
                    Erasure.P.PCUICEnvironment.ind_params :=
                      ind_params0;
                    Erasure.P.PCUICEnvironment.ind_bodies :=
                      ind_bodies1;
                    Erasure.P.PCUICEnvironment.ind_universes :=
                      ind_universes0;
                    Erasure.P.PCUICEnvironment.ind_variance :=
                      ind_variance0
                  |}) ind_bodies0)),
  In lind
    (CoqType_to_camlType_fix ind_bodies0 ind_finite0 ind_params0
       ind_npars0 ind_universes0 ind_variance0 Hparam ind_bodies1 Hfo) ->
  In larg lind -> In T larg -> is_true (negb (isArrow T))).
  eapply H; eauto. 
  induction ind_bodies0; cbn in * ; [now intros |].   
  intros bodies1 Hfo Hlind Hlarg HT. unfold In in Hlind. destruct Hlind.
    - rewrite <- H in Hlarg. eapply CoqType_to_camlType_oneind_fo; eauto.
    - eapply IHind_bodies0; eauto.
  Qed. 

  Lemma CoqType_to_camlType'_fo_alt T1 T2 Ts mind ind Hparam Hfo:
    In Ts
       (nth ind (CoqType_to_camlType'
           mind Hparam Hfo) []) -> ~ In (T1 → T2) Ts.
  Proof.
    intros H H0. 
    epose proof (CoqType_to_camlType'_fo _ _ _ _ _ _ _ _ H0).
    now cbn in H1. Unshelve. all:eauto.  
    case_eq (Nat.ltb ind (List.length (CoqType_to_camlType' mind
    Hparam Hfo))); intro Hleq.
    - apply nth_In. apply leb_complete in Hleq. lia. 
    - apply leb_complete_conv in Hleq. 
      assert (Datatypes.length (CoqType_to_camlType' mind Hparam Hfo) <= ind) by lia.
      pose proof (nth_overflow _ [] H1).
      rewrite H2 in H. destruct (in_nil H).
  Qed.  

  Lemma CoqType_to_camlType'_length mind Hparam Hfo :
    List.length (CoqType_to_camlType' mind Hparam Hfo) 
    = List.length (ind_bodies mind).
  Proof.
    destruct mind. cbn in *. revert Hfo.
    enough (forall ind_bodies1
      (Hfo : is_true
            (forallb
               (firstorder_oneind
                  {|
                    Erasure.P.PCUICEnvironment.ind_finite :=
                      ind_finite0;
                    Erasure.P.PCUICEnvironment.ind_npars :=
                      ind_npars0;
                    Erasure.P.PCUICEnvironment.ind_params :=
                      ind_params0;
                    Erasure.P.PCUICEnvironment.ind_bodies :=
                      ind_bodies1;
                    Erasure.P.PCUICEnvironment.ind_universes :=
                      ind_universes0;
                    Erasure.P.PCUICEnvironment.ind_variance :=
                      ind_variance0
                  |}) ind_bodies0)),
    #|CoqType_to_camlType_fix
        ind_bodies0 ind_finite0
        ind_params0 ind_npars0
        ind_universes0 ind_variance0
        Hparam ind_bodies1 Hfo| =
    #|ind_bodies0|); eauto.
    induction ind_bodies0; cbn; eauto.
    intros. f_equal. destruct andb_and.
    destruct (a0 Hfo). eauto. 
  Qed.      

  
  Lemma CoqType_to_camlType_oneind_length mind Hparam x Hfo:
  List.length
      (CoqType_to_camlType_oneind
            mind x Hparam Hfo) =
  List.length (ind_ctors x).
  Proof.
    destruct x; cbn. destruct andb_and.
    destruct (a Hfo). clear.
    induction ind_ctors0; cbn; eauto.
    destruct andb_and. destruct (a0 i0).
    destruct a. cbn. f_equal. eapply IHind_ctors0.
  Qed. 

  Lemma CoqType_to_camlType'_nth mind Hparam x Hfo Hfo' ind:
  nth_error (ind_bodies mind) ind = Some x -> 
  ind < Datatypes.length (ind_bodies mind) -> 
    nth ind
         (CoqType_to_camlType'
            mind
            Hparam
            Hfo) [] =
    CoqType_to_camlType_oneind mind x Hparam Hfo'.
  Proof.
    destruct mind. revert ind. cbn in *. revert Hfo Hfo'.
    enough (
    forall ind_bodies1 (Hfo : is_true
           (forallb
              (firstorder_oneind
              (Build_mutual_inductive_body
              ind_finite0 ind_npars0
              ind_params0 ind_bodies1
              ind_universes0 ind_variance0)) ind_bodies0))
  (Hfo' : is_true
            (firstorder_oneind
            (Build_mutual_inductive_body
            ind_finite0 ind_npars0
            ind_params0 ind_bodies1
            ind_universes0 ind_variance0) x)) (ind : nat),
nth_error ind_bodies0 ind = Some x ->
ind < Datatypes.length ind_bodies0 ->
nth ind
  (CoqType_to_camlType_fix ind_bodies0 ind_finite0
     ind_params0 ind_npars0 ind_universes0
     ind_variance0 Hparam ind_bodies1 Hfo) [] =
CoqType_to_camlType_oneind
(Build_mutual_inductive_body
ind_finite0 ind_npars0
ind_params0 ind_bodies1
ind_universes0 ind_variance0) x Hparam Hfo'); eauto.
    induction ind_bodies0; intros. cbn in *; lia.
    destruct ind; cbn.
    - destruct andb_and. destruct (a0 Hfo).  
      cbn in H. inversion H. subst. f_equal. clear. apply bool_irr.
    - eapply IHind_bodies0; eauto.
      cbn in *; lia.
  Qed.

  Lemma CoqType_to_camlType'_nth_length mind Hparam Hfo ind x:
    nth_error (ind_bodies mind) ind = Some x -> 
    ind < Datatypes.length (ind_bodies mind) -> 
    List.length
        (nth ind
           (CoqType_to_camlType'
              mind
              Hparam
              Hfo) []) =
    List.length (ind_ctors x).
  Proof.
    intros; erewrite CoqType_to_camlType'_nth; eauto.
    eapply CoqType_to_camlType_oneind_length; eauto. 
    Unshelve. eapply forallb_nth_error in Hfo.
      erewrite H in Hfo. exact Hfo.         
  Qed. 

  Definition CoqType_to_camlType mind : 
    ind_params mind = [] -> 
    is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind)) -> ADT :=
    fun Hparam H => (0, CoqType_to_camlType' mind Hparam H).
  
  Lemma CoqType_to_camlType_ind_ctors_nth 
    mind ind_ctors Hparam a k i :
    nth_error (CoqType_to_camlType_ind_ctors mind ind_ctors Hparam i) k
    = Some a ->
    exists a', nth_error ind_ctors k = Some a' /\
    exists i', 
    a = CoqType_to_camlType_ind_ctor 0 #|ind_bodies mind| (rev (cstr_args a' ++ ind_params mind)) i'.
  Proof. 
    revert a k i.
    induction ind_ctors; cbn; intros.
    - destruct k; inversion H.
    - destruct andb_and. destruct (a1 _).
      destruct k; destruct a.
      + inversion H. eexists; split; [reflexivity|].
        cbn. unfold firstorder_con in i. cbn in i.
        apply andb_and in i. destruct i as [i ?]. 
        exists i. repeat f_equal. apply bool_irr.
      + eapply IHind_ctors; eauto.
  Qed. 

  Lemma CoqType_to_camlType_ind_ctors_length 
  l n m i:
  List.length (CoqType_to_camlType_ind_ctor n m l i) = List.length l.
  revert n m i. induction l; cbn; eauto; intros. 
  destruct andb_and. destruct (a0 _). destruct a.
  cbn. now f_equal.
  Qed. 

  Lemma CoqType_to_camlType_ind_ctor_app
  l l' n m i : { i' & { i'' &  CoqType_to_camlType_ind_ctor n m (l++l') i = CoqType_to_camlType_ind_ctor n m l i' ++ CoqType_to_camlType_ind_ctor (#|l| + n) m l' i''}}.
  pose proof (ii := i). rewrite alli_app in ii. eapply andb_and in ii. destruct ii as [i' i''].
  exists i', i''. revert n i i' i''. induction l; cbn in *; intros.  
  - f_equal. eapply bool_irr.
  - destruct andb_and. destruct (a0 _). destruct a.      
    destruct andb_and. destruct (a _). rewrite <- app_comm_cons; repeat f_equal.
    * apply bool_irr.
    * assert (S (#|l| + n) = #|l| + S n) by lia. revert i''. rewrite H. apply IHl.
  Qed.      
    
  Lemma CoqType_to_camlType_oneind_nth mind Hparam x Hfo k l :
  nth_error (CoqType_to_camlType_oneind mind x Hparam Hfo) k = Some l
  -> exists l', nth_error (ind_ctors x) k = Some l' /\ #|l| = #|cstr_args l'|.
  Proof.
    destruct x; cbn. destruct andb_and.
    destruct (a Hfo). clear.
    revert k l. induction ind_ctors0; cbn; eauto.
    - intros k l H. rewrite nth_error_nil in H. inversion H.
    - destruct andb_and. destruct (a0 i0).
      destruct a. intros k l H. destruct k; cbn. 
      + eexists; split; [reflexivity |]. cbn in *.
        inversion H. rewrite CoqType_to_camlType_ind_ctors_length.
        rewrite Hparam. rewrite app_nil_r. apply rev_length.
      + cbn in *. now eapply IHind_ctors0. 
  Qed. 

  Lemma CoqType_to_camlType_oneind_nth' mind Hparam x Hfo k l :
  nth_error (ind_ctors x) k = Some l 
  -> exists l', nth_error (CoqType_to_camlType_oneind mind x Hparam Hfo) k = Some l' /\ #|l'| = #|cstr_args l|.
  Proof.
    destruct x; cbn. destruct andb_and.
    destruct (a Hfo). clear.
    revert k l. induction ind_ctors0; cbn; eauto.
    - intros k l H. rewrite nth_error_nil in H. inversion H.
    - destruct andb_and. destruct (a0 i0).
      destruct a. intros k l H. destruct k; cbn. 
      + eexists; split; [reflexivity |]. cbn in *.
        inversion H. rewrite CoqType_to_camlType_ind_ctors_length.
        rewrite Hparam. rewrite app_nil_r. apply rev_length.
      + cbn in *. now eapply IHind_ctors0. 
  Qed. 


  #[local] Instance cf_ : checker_flags := extraction_checker_flags.
  #[local] Instance nf_ : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

  Parameter Normalisation : forall Σ0 : PCUICAst.PCUICEnvironment.global_env_ext, PCUICTyping.wf_ext Σ0 -> PCUICSN.NormalizationIn Σ0.

  Parameter compile_pipeline : global_env -> term -> t.
  
  Parameter compile_pipeline_tConstruct_nil : forall Σ i n inst,
    compile_pipeline Σ (tConstruct i n inst) =
    match lookup_constructor_args Σ i with
    | Some num_args =>
      Mnum (numconst_Int (int_of_nat (nonblocks_until n num_args)))
    | None => Mstring "error: inductive not found"
    end.

  Parameter compile_pipeline_tConstruct_cons : forall Σ i n inst l, 
    #|l| > 0 ->
    compile_pipeline Σ (mkApps (tConstruct i n inst) l) =
    match lookup_constructor_args Σ i with
    | Some num_args =>
      Mblock
        (int_of_nat (blocks_until n num_args),
         map_InP l (fun (x : term) (_ : In x l) => compile_pipeline Σ x))
    | None => Mstring "error: inductive not found"
    end.

  Parameter compile_app : forall `{Heap} `{WcbvFlags} 
  (cf:=config.extraction_checker_flags) 
  (Σ:global_env_ext_map) t u na A B,
  ∥ Σ ;;; [] |- t : tProd na A B ∥ ->
  ~ ∥Extract.isErasable Σ [] t∥ -> 
  compile_pipeline Σ (tApp t u) = 
  Mapply (compile_pipeline Σ t, [compile_pipeline Σ u]).

  Parameter compile_function : forall `{Heap} `{WcbvFlags} 
  (cf:=config.extraction_checker_flags)
  (Σ:global_env_ext_map) h h' f v na A B,
  ∥ Σ ;;; [] |- f : tProd na A B ∥ ->
  ~ ∥Extract.isErasable Σ [] f∥ ->
  eval [] empty_locals h (compile_pipeline Σ f) h' v ->
  isFunction v = true.    

  Parameter compile_pure : forall `{Heap} `{WcbvFlags} Σ t, is_true (isPure (compile_pipeline Σ t)).

  Lemma filter_length_nil ind k mind Eind Hparam Hfo :
    nth_error (ind_bodies mind) ind = Some Eind ->
  List.length
  (filter (fun x0 : nat =>  match x0 with
      | 0 => true
      | S _ => false
      end)
     (firstn k (map cstr_nargs (ind_ctors Eind)))) = 
  List.length
           (filter (fun x : list camlType =>
               match x with
               | [] => true
               | _ :: _ => false
               end)
              (firstn k
                 (nth ind
                    (CoqType_to_camlType' mind
                       Hparam Hfo) []))).
   Proof. 
    intro Hind. unshelve erewrite CoqType_to_camlType'_nth; eauto.
    - eapply nth_error_forallb in Hfo; eauto.
    - destruct Eind; cbn. destruct andb_and. destruct (a _).
      rewrite (filter_ext _ (fun x =>
      match #|x| with
      | 0 => true
      | S _ => false
      end)).
      { clear. intro l; induction l; eauto. }
      revert k i0. clear Hind i i1 a. induction ind_ctors0; cbn; intros. 
      + intros. now repeat rewrite firstn_nil.
      + destruct k; eauto; cbn. destruct andb_and. destruct (a0 _). cbn.
        destruct a. cbn. rewrite CoqType_to_camlType_ind_ctors_length.
        revert i1. cbn. rewrite Hparam app_nil_r. cbn.
        rewrite rev_length. intro.  
        destruct cstr_args0; cbn. 
        * intros; f_equal. eapply IHind_ctors0; eauto.
        * eapply IHind_ctors0.
    - now eapply nth_error_Some_length. 
  Qed.                       

    Lemma filter_length_not_nil ind k mind Eind Hparam Hfo :
    nth_error (ind_bodies mind) ind = Some Eind ->
  List.length
  (filter (fun x0 : nat =>  match x0 with
      | 0 => false
      | S _ => true 
      end)
     (firstn k (map cstr_nargs (ind_ctors Eind)))) = 
  List.length
           (filter (fun x : list camlType =>
               match x with
               | [] => false
               | _ :: _ => true
               end)
              (firstn k
                 (nth ind
                    (CoqType_to_camlType' mind
                       Hparam Hfo) []))).
  Proof. 
    intro Hind. unshelve erewrite CoqType_to_camlType'_nth; eauto.
    - eapply nth_error_forallb in Hfo; eauto.
    - destruct Eind; cbn. destruct andb_and. destruct (a _).
      rewrite (filter_ext _ (fun x =>
      match #|x| with
      | 0 => false
      | S _ => true
      end)).
      { clear. intro l; induction l; eauto. }
      revert k i0. clear Hind i i1 a. induction ind_ctors0; cbn; intros. 
      + intros. now repeat rewrite firstn_nil.
      + destruct k; eauto; cbn. destruct andb_and. destruct (a0 _). cbn.
        destruct a. cbn. rewrite CoqType_to_camlType_ind_ctors_length.
        revert i1. cbn. rewrite Hparam app_nil_r. cbn.
        rewrite rev_length. intro.  
        destruct cstr_args0; cbn. 
        * eapply IHind_ctors0.
        * intros; f_equal. eapply IHind_ctors0; eauto.
    - now eapply nth_error_Some_length. 
  Qed. 
End firstorder.

Lemma CoqType_to_camlType_oneind_type_Rel n k decl_type Hfo :
let T := CoqType_to_camlType_oneind_type (Σb := []) n k decl_type Hfo in
exists i,  (k <= i) /\ (i < n + k) /\ T = Rel (n - S (i-k)).
Proof.
unfold CoqType_to_camlType_oneind_type.
unfold firstorder_type in Hfo.
set (fst (PCUICAstUtils.decompose_app decl_type)) in *.
set (snd (PCUICAstUtils.decompose_app decl_type)) in *.
destruct t; destruct l; inversion Hfo; cbn; eauto.
- apply andb_and in H0. destruct H0. apply leb_complete in H, H0.
  exists n0; repeat split; eauto.
- destruct ind; inversion Hfo.
- destruct ind; inversion Hfo.
Qed.   

Lemma CoqType_to_camlType_oneind_Rel mind ind Hparam Hfo larg T k : 
In larg (CoqType_to_camlType_oneind (Σb := []) mind ind Hparam Hfo) ->
nth_error larg k = Some T -> exists i, (k <= i) /\ (i < #|ind_bodies mind| + k) /\ T = Rel (#|ind_bodies mind| - S (i-k)).
Proof. 
destruct mind, ind. revert k Hfo. induction ind_ctors0; intros k Hfo Hlarg HT.
- cbn in *; destruct andb_and. destruct (a Hfo). destruct (in_nil Hlarg).
- cbn; cbn in Hlarg. destruct andb_and. cbn in Hfo. destruct (a0 Hfo). 
  destruct andb_and. destruct (a1 i0). destruct a.
  unfold In in Hlarg. destruct Hlarg.
  2: { eapply IHind_ctors0; eauto. cbn. destruct andb_and.
        destruct (a _). rewrite (bool_irr _ i6 i4). eauto.
        Unshelve.
        cbn. apply andb_and. split; cbn; eauto. }
  cbn in Hparam, i3. rewrite Hparam in i3, H. rewrite app_nil_r in i3, H.
  clear - i3 HT H. set (rev cstr_args0) in *. rewrite <- H in HT.
  pose proof (nth_error_Some_length HT).
  revert T HT. clear H H0. cbn; set (#|ind_bodies0|) in *. 
  setoid_rewrite <- (Nat.sub_0_r k) at 1. assert (k >= 0) by lia. revert H.  
  revert k i3. generalize 0 at 1 2 3 4.
  induction l; cbn; intros. 1: { rewrite nth_error_nil in HT. inversion HT. }
  destruct andb_and. destruct (a0 i3). destruct a.
  cbn in HT. 
  case_eq (k - n0).
  + intro Heq.
    rewrite Heq in HT. inversion HT. 
    unshelve epose (CoqType_to_camlType_oneind_type_Rel _ _ _ _).
    5: erewrite H1 in e. rewrite H1. destruct e as [i2 [? [? ?]]]. exists (i2 + k - n0).
    repeat split. all: try lia. rewrite H3; f_equal. lia. 
  + intros ? Heq. rewrite Heq in HT. cbn in HT. eapply IHl.
    2: { assert (n1 = k - S n0) by lia. now rewrite H0 in HT. }
    lia.  
Qed.  

Lemma CoqType_to_camlType'_unfold mind Hparam Hfo l : 
In l (CoqType_to_camlType' (Σb := []) mind Hparam Hfo) ->
exists ind Hfo', l =  CoqType_to_camlType_oneind (Σb := []) mind ind Hparam Hfo'.
Proof.
  destruct mind; cbn in *. revert Hfo.
  enough (forall ind_bodies1, forall
  Hfo : is_true
          (forallb
             (firstorder_oneind
                {|
                  Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
                  Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
                  Erasure.P.PCUICEnvironment.ind_params := ind_params0;
                  Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
                  Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
                  Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
                |}) ind_bodies0),
In l
  (CoqType_to_camlType_fix (Σb := []) ind_bodies0 ind_finite0 ind_params0 ind_npars0 ind_universes0 ind_variance0
     Hparam ind_bodies1 Hfo) ->
exists
  (ind : one_inductive_body) (Hfo' : is_true
                                       (firstorder_oneind
                                          {|
                                            Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
                                            Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
                                            Erasure.P.PCUICEnvironment.ind_params := ind_params0;
                                            Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
                                            Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
                                            Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
                                          |} ind)),
  l =
  CoqType_to_camlType_oneind (Σb := [])
    {|
      Erasure.P.PCUICEnvironment.ind_finite := ind_finite0;
      Erasure.P.PCUICEnvironment.ind_npars := ind_npars0;
      Erasure.P.PCUICEnvironment.ind_params := ind_params0;
      Erasure.P.PCUICEnvironment.ind_bodies := ind_bodies1;
      Erasure.P.PCUICEnvironment.ind_universes := ind_universes0;
      Erasure.P.PCUICEnvironment.ind_variance := ind_variance0
    |} ind Hparam Hfo').
  { eapply H; eauto. }
  induction ind_bodies0; cbn; intros.
  - inversion H.
  - destruct andb_and. destruct (a0 Hfo). destruct H.
    + exists a. now exists i0.
    + eapply IHind_bodies0; eauto.
  Qed.  
    
Lemma CoqType_to_camlType'_Rel mind ind Hparam Hfo larg T k : 
let typ := (CoqType_to_camlType' (Σb := []) mind Hparam Hfo) in
In larg (nth ind typ []) -> 
nth_error larg k = Some T -> exists i, (k <= i) /\ (i < #|ind_bodies mind| + k) /\ T = Rel (#|ind_bodies mind| - S (i-k)).
Proof.
  intro typ. destruct (nth_in_or_default ind typ []).
  2: { rewrite e. intros Hlarg; destruct (in_nil Hlarg). }
  intro Hlarg. unfold typ in *. eapply CoqType_to_camlType'_unfold in i.
  destruct i as [ind' [Hfo' i]]. rewrite i in Hlarg. now eapply CoqType_to_camlType_oneind_Rel.
Qed.

Lemma CoqType_to_camlType'_Rel' mind ind Hparam Hfo larg T k : 
let typ := (CoqType_to_camlType' (Σb := []) mind Hparam Hfo) in
In larg (nth ind typ []) -> 
nth_error larg k = Some T -> exists i, (0 <= i) /\ (i < #| ind_bodies mind|) /\ T = Rel (#|ind_bodies mind| - S i).
Proof.
  intros. unshelve epose (CoqType_to_camlType'_Rel _ ind); eauto. 
  edestruct e as [i [? [? ?]]]; eauto. exists (i - k). repeat split; eauto.
  all: lia.
Qed.

  Inductive nonDepProd : term -> Type :=
    | nonDepProd_tInd : forall i u, nonDepProd (tInd i u)
    | nonDepProd_Prod : forall na A B, closed A -> nonDepProd B -> nonDepProd (tProd na A B).

  Lemma nonDep_closed t : nonDepProd t -> closed t.  
  Proof.
    induction 1; cbn; eauto. 
    rewrite i; cbn. eapply PCUICLiftSubst.closed_upwards; eauto.
  Qed. 

  Fixpoint nonDep_decompose (t:term) (HnonDep : nonDepProd t) : list term * term
    := match HnonDep with 
    | nonDepProd_tInd i u => ([], tInd i u)
    | nonDepProd_Prod na A B clA ndB => let IH := nonDep_decompose B ndB in (A :: fst IH, snd IH)
    end.

  Lemma nonDep_typing_spine (cf:=config.extraction_checker_flags) (Σ:global_env_ext) us u_ty s (nonDep : nonDepProd u_ty) :
    PCUICTyping.wf Σ ->
    Σ ;;; [] |- u_ty : tSort s -> 
    All2 (fun u uty => Σ ;;; [] |- u : uty) us (fst (nonDep_decompose u_ty nonDep))  ->
    PCUICGeneration.typing_spine Σ [] u_ty us (snd (nonDep_decompose u_ty nonDep)).
  Proof.
  revert s us. induction nonDep; cbn in *; intros s us wfΣ Hty; cbn.
  - intro H; depelim H. econstructor; [|reflexivity]. eexists; eauto.
  - set (PCUICInversion.inversion_Prod Σ wfΣ Hty) in *.
    destruct s0 as [s1 [s2 [HA [HB ?]]]]; cbn. intro H; depelim H.   
    epose (strengthening_type [] ([],, vass na A) [] B s2).
    pose proof (nonDep_closed _ nonDep).
    edestruct s0 as [s' [Hs _]]. cbn.  rewrite PCUICLiftSubst.lift_closed; eauto.
    econstructor; try reflexivity; eauto.
    + eexists; eauto.
    + rewrite /subst1 PCUICClosed.subst_closedn; eauto.
  Qed.      

  Lemma firstorder_con_notApp `{checker_flags} mind a :
    firstorder_con (Σb := []) mind a -> 
    All (fun decl => ~ (isApp (decl_type decl))) (cstr_args a).
  Proof.
    intros Hfo. destruct a; cbn in *. induction cstr_args0; eauto.
    cbn in Hfo. rewrite rev_app_distr in Hfo. cbn in Hfo.
    rewrite alli_app in Hfo. rewrite <- plus_n_O in Hfo. apply andb_and in Hfo. destruct Hfo as [? Hfo].
    econstructor.
    - clear H0 IHcstr_args0. destruct a.
      simpl in *. apply andb_and in Hfo. destruct Hfo as [Hfo _].
      unfold firstorder_type in Hfo. cbn in Hfo. 
      assert (snd (PCUICAstUtils.decompose_app decl_type) = []).
      { destruct snd; eauto. destruct fst; try destruct ind; inversion Hfo. } 
      destruct decl_type; try solve [inversion Hfo]; eauto. intros _.
      cbn in H0. pose proof (PCUICInduction.decompose_app_rec_length decl_type1 [decl_type2]).
      rewrite H0 in H1. cbn in H1. lia. 
    - apply IHcstr_args0. now rewrite rev_app_distr.
  Qed. 

  Lemma firstorder_type_closed kn l k T :
    ~ (isApp T) -> 
    firstorder_type (Σb := []) #|ind_bodies l| k T -> 
    closed (subst (inds kn [] (ind_bodies l)) k T@[[]]).
  Proof. 
    intro nApp; destruct T; try solve [inversion 1]; cbn in *; eauto.  
    - intro H; apply andb_and in H. destruct H. rewrite H.
      eapply leb_complete in H, H0. rewrite nth_error_inds; [lia|eauto].
    - now destruct nApp.
  Qed. 

  Lemma firstorder_nonDepProd mind kn Eind cstr_args0 x lind ind :
  nth_error (ind_bodies mind) ind = Some Eind ->
  is_assumption_context cstr_args0 ->
  All (fun decl => ~ (isApp (decl_type decl))) cstr_args0 ->
  let Ts := CoqType_to_camlType_ind_ctor (Σb := []) 0 #|ind_bodies mind| (rev cstr_args0) x in 
  All2 (fun a b => 0 <= a /\ a < #|ind_bodies mind| /\ b = Rel (#|ind_bodies mind| - S a)) lind Ts -> 
  { nd : nonDepProd (subst0 (inds kn [] (ind_bodies mind))
                     (it_mkProd_or_LetIn cstr_args0 (tRel (#|ind_bodies mind| - S ind + #|cstr_args0|)))@[[]]) &
  (fst (nonDep_decompose _ nd) = map (fun b : nat => tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) lind) /\
  (snd (nonDep_decompose _ nd) = tInd {| inductive_mind := kn; inductive_ind := ind |} []) }.
Proof.
    intros Hind Hlets Happ. 
    set (X := (tRel (#|ind_bodies mind| - S ind + #|cstr_args0|))).
    assert (Hmind: #|ind_bodies mind| > 0).
    { destruct (ind_bodies mind); [|cbn; lia]. rewrite nth_error_nil in Hind. inversion Hind. }
    assert (HX : {nd : nonDepProd (subst (inds kn [] (ind_bodies mind)) #|cstr_args0| X@[[]]) &
      (fst (nonDep_decompose _ nd) = map (fun b : nat => tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) []) /\ 
      (snd (nonDep_decompose _ nd) = tInd {| inductive_mind := kn; inductive_ind := ind |} [])}).
    { cbn.
      assert (#|cstr_args0| <= #|ind_bodies mind| - S ind + #|cstr_args0|) by lia.
      apply leb_correct in H. 
      destruct (_ <=? _); [| lia]. 
      assert (Heq : #|ind_bodies mind| - S ind + #|cstr_args0| - #|cstr_args0| < #|ind_bodies mind|) by lia. 
      pose proof (@nth_error_inds kn [] _ _ Heq). revert H0. 
      destruct (nth_error (inds _ _ _) _); [| inversion 1].
      inversion 1. clear H0 H2. unshelve eexists. econstructor. cbn. split; [sq; eauto|].
      repeat f_equal. destruct (ind_bodies _); [inversion Hmind|]. apply nth_error_Some_length in Hind. cbn in *. lia.  
    }
    clearbody X. intros Ts Hrel. rewrite <- (app_nil_r lind). revert HX Ts Hrel. generalize (@nil nat) as lind_done.
    revert X lind x. 
    induction cstr_args0; intros X lind x lind_done HX Ts Hrel; simpl in *; eauto.
    1: { eapply All2_length in Hrel. eapply length_nil in Hrel. 
         now subst. }
    unfold Ts in Hrel. edestruct (CoqType_to_camlType_ind_ctor_app (Σb := [])) as [? [? ->]] in Hrel.
    apply All2_app_inv_r in Hrel as [lind' [lind'' [? [Hrel Ha]]]]. subst.
    rewrite <- app_assoc. eapply IHcstr_args0; eauto.
    { destruct decl_body;[inversion Hlets| eauto]. }
    { inversion Happ; eauto. }
    destruct a. destruct decl_body.
    + inversion Hlets.
    + destruct HX as [ndX [Xfst Xsnd]]. cbn. 
      unshelve econstructor. econstructor; eauto.
      { cbn in *. clear -x1 Happ. 
        apply andb_and in x1; destruct x1 as [x1 _].
        rewrite <- plus_n_O in x1. rewrite rev_length in x1. apply firstorder_type_closed; eauto.
        inversion Happ; eauto.
      }
      split; eauto.
      rewrite map_app. cbn. set (subst _ _ _). set (fst _). change (t :: y) with ([t]++y). f_equal; eauto. 
      unfold t. cbn in Ha. destruct andb_and. destruct (a _). clear a i i1.
      destruct decl_type; inversion i0.
      * cbn. revert i0 Ha. rewrite rev_length. cbn.  intros. apply andb_and in i0. destruct i0. rewrite <- plus_n_O in H.
        inversion Ha. subst. apply All2_length in X0. apply length_nil in X0. subst. clear Ha. 
        rewrite H. rewrite nth_error_inds. { apply leb_complete in H1. lia. } 
        cbn. repeat f_equal; eauto. destruct H4 as [? [? ?]]. inversion H4. 
        apply leb_complete in H1. lia.   
      * cbn in *. inversion Happ; subst. now cbn in H1. 
      * cbn in H0. destruct ind0. inversion H0.
  Qed. 

  Record pcuic_good_for_extraction {Σ : global_env} := 
    { ctors_max_length : forall mind j k ind ctors, nth_error mind j = Some ind -> nth_error (ind_ctors ind) k = Some ctors -> 
        #|cstr_args ctors| < int_to_nat max_length;
      ind_ctors_wB : forall mind j ind, nth_error mind j = Some ind -> #|ind_ctors ind| <= Z.to_nat Uint63.wB }.
  Arguments pcuic_good_for_extraction : clear implicits.

  Lemma camlValue_to_CoqValue `{Heap} `{WcbvFlags} (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind
    (Hparam : ind_params mind = [])
    (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
    (Hnparam : ind_npars mind = 0)
    (Hmono : ind_universes mind = Monomorphic_ctx)
    (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) :
    let adt := CoqType_to_camlType mind Hparam Hfo in
    let Σ : global_env_ext_map := (build_global_env_map (mk_global_env univ [(kn , InductiveDecl mind)] retro), univ_decl) in
    pcuic_good_for_extraction Σ ->
    PCUICTyping.wf Σ ->
    with_constructor_as_block = true ->
    forall v ind Eind, 
    ind < List.length (snd adt) ->
    lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
    realize_ADT _ _ [] [] adt [] All_nil ind v ->
    exists t, forall h,  
    ∥ Σ ;;; [] |- t : tInd (mkInd kn ind) [] ∥ /\ 
    eval [] empty_locals h (compile_pipeline Σ t) h v.
  Proof. 
    rename H into HP; rename H0 into HHeap; rename H1 into H. 
    intros adt Σ good wfΣ Hflag v ind Eind Hind Hlookup [step Hrel].
    revert kn mind Hparam Hindices Hnparam Hmono Hfo v ind Eind adt Σ good wfΣ Hflag Hind Hlookup Hrel. 
    induction step; intros; [inversion Hrel|].
    apply leb_correct in Hind. simpl in Hrel, Hind. 
    unfold Nat.ltb in Hrel. rewrite Hind in Hrel.
    destruct Hrel as [Hrel | Hrel].
    - apply Existsi_spec in Hrel as [k [Ts [Hk [HkS [Hrel HTs]]]]].
      cbn in HkS.
      destruct (filter_firstn' _ _ _ _ HkS) as [k' [Hk' [Hfilter Hwit]]].
      destruct Hwit as [As [Ha [Ha' Ha'']]].
      eexists (tConstruct (mkInd kn ind) k' []); cbn; split.
      + pose (MCList.nth_error_spec (ind_bodies mind) ind).
        destruct n; cbn; intros.
        2: { apply leb_complete in Hind.
             rewrite CoqType_to_camlType'_length in Hind. lia. }    
        pose (MCList.nth_error_spec (ind_ctors x) k').
        destruct n; intros; eauto.
        ++ 
          unshelve epose proof (Htyp := type_Construct Σ [] (mkInd kn ind) k' [] mind x x0 _ _ _).
          ** econstructor.
          ** unfold declared_constructor, declared_inductive. now cbn.
          ** unfold consistent_instance_ext, consistent_instance; cbn.
             now rewrite Hmono.
          ** 
          assert (is_true (@firstorder_oneind [] mind x)).
          { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth in Hfilter, Ha, Ha'; eauto.
          unfold CoqType_to_camlType_oneind in Hfilter, Ha, Ha'. destruct x. cbn in *. 
          destruct andb_and. destruct (a _).
          apply CoqType_to_camlType_ind_ctors_nth in Ha.
          destruct Ha as [a0 [? [? ?]]].
          rewrite H2 in Ha''.
          unfold type_of_constructor in Htyp.  
          assert (CoqType_to_camlType_ind_ctor 0 #|ind_bodies mind|
          (rev (cstr_args a0 ++ ind_params mind)) x = []).
          { destruct CoqType_to_camlType_ind_ctor; eauto. }
          clear Ha''. apply f_equal with (f := @List.length _) in H3.
          rewrite CoqType_to_camlType_ind_ctors_length in H3.
          cbn in H3. erewrite rev_length, app_length in H3.
          assert (Ha0 : #|cstr_args a0| = 0) by lia. apply length_nil in Ha0.
          rewrite e0 in H1. inversion H1. subst; clear H1.
          unfold PCUICTyping.wf in wfΣ. inversion wfΣ as [_ wfΣ'].
          cbn in wfΣ'. inversion wfΣ'; subst. clear X.
          inversion X0 as [_ ? _ wf_ind]; cbn in *.
          destruct wf_ind as [wf_ind _ _ _].
          inversion wfΣ'; subst. inversion X1; subst. inversion on_global_decl_d. 
          eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
          inversion onInductives. unfold PCUICGlobalMaps.on_constructors in *. cbn in *.
          eapply All2_nth_error_Some  in onConstructors; eauto. destruct onConstructors as [l' [? onConstructor]].
          erewrite @cstr_eq with (i:=ind) in Htyp; eauto.
          unfold cstr_concl in Htyp. 
          erewrite Hparam, Ha0 in Htyp. cbn in Htyp. 
          assert (cstr_indices a0 = []).
          { apply length_nil. erewrite @cstr_indices_length with (Σ:=Σ) (ind:=(mkInd kn ind,k')); eauto. 
            2: { repeat split. cbn. left. reflexivity. all:cbn; eauto. } cbn. eapply nth_error_forall in Hindices; eauto.
                 cbn in Hindices. now rewrite Hindices. }
          rewrite H1 in Htyp; clear H1; cbn in Htyp.
          rewrite Ha0 Hparam in Htyp. cbn in Htyp.   
          rewrite inds_spec in Htyp.  
          assert (#|ind_bodies mind| - S ind + 0 + 0 - 0 = #|ind_bodies mind| - S ind)
          by lia. rewrite H1 in Htyp; clear H1.
          erewrite <- mapi_length in Htyp. 
          rewrite <- nth_error_rev, nth_error_mapi, e in Htyp.
          cbn in Htyp. sq; exact Htyp.  
          now rewrite mapi_length.
        ++ assert (is_true (@firstorder_oneind [] mind x)). 
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth in Hk'; eauto.
          rewrite CoqType_to_camlType_oneind_length in Hk'.
          lia.  
     + rewrite (compile_pipeline_tConstruct_nil Σ). simpl. 
        unfold lookup_constructor_args. rewrite Hlookup.
        rewrite Hrel. clear Hrel v.
        pose (MCList.nth_error_spec (ind_bodies mind) ind).
        apply leb_complete in Hind. rewrite CoqType_to_camlType'_length in Hind.    
        destruct n; [|lia].
        assert (is_true (@firstorder_oneind [] mind x)).
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
        unshelve erewrite CoqType_to_camlType'_nth in Hfilter; eauto.  
        unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup. cbn in Hlookup.
        rewrite ReflectEq.eqb_refl in Hlookup.
        unfold nonblocks_until. 
        unshelve erewrite filter_length_nil with (mind:=mind) (ind:=ind); eauto.
        2: { destruct (nth_error (ind_bodies mind) ind); now inversion Hlookup. }
        rewrite Hfilter. 
        unshelve erewrite CoqType_to_camlType'_nth; eauto.
        unfold int_of_nat. set (Z.of_nat _).
        assert (z = (z mod Uint63.wB)%Z).
        symmetry; eapply Z.mod_small.
        split. lia.
        unfold z; clear z. set (List.length _).
        enough (n < S (Z.to_nat (Z.pred Uint63.wB))). 
        clearbody n. 
        eapply Z.lt_le_trans. 
        eapply inj_lt. eapply H1. clear.
        rewrite Nat2Z.inj_succ. 
        rewrite Z2Nat.id. now vm_compute. now vm_compute.
        unfold n. rewrite <- Nat.le_succ_l.
        apply le_n_S. etransitivity. apply filter_length.
        rewrite firstn_length.
        unshelve erewrite CoqType_to_camlType'_nth_length in Hk'; eauto.
        etransitivity. apply Nat.le_min_l.
        apply good.(ind_ctors_wB) in e. lia.
        unshelve erewrite CoqType_to_camlType'_nth in Hk'; eauto.
        rewrite -> H1 at 2. rewrite <- Int63.of_Z_spec. 
        econstructor.
    - apply leb_complete in Hind. 
      apply Existsi_spec in Hrel as [k [Ts [Hk [HkS [Hrel HTs]]]]].
      cbn in HkS.
      destruct (filter_firstn' _ _ _ _ HkS) as [k' [Hk' [Hfilter Hwit]]].
      destruct Hrel as [v' [eq Hv']].
      destruct Ts as [|T Ts]. (* not possible filtered *) 
      + apply filter_nth_error in HTs. destruct HTs as [_ HTs]. 
        inversion HTs.
      + pose proof (HTs' := HTs). apply filter_nth_error in HTs. destruct HTs as [HTs _].
        subst.
        assert (Forall2 (fun v T => 
        (exists t, forall h,  ∥ (Σ , univ_decl) ;;; [] |- fst t : tInd (mkInd kn (#|ind_bodies mind| - S (snd t))) [] ∥ /\ 
        eval [] empty_locals h (compile_pipeline Σ (fst t)) h v
        /\ (0 <= snd t) /\ (snd t < #|ind_bodies mind|) /\ T = Rel (#|ind_bodies mind| - S (snd t)))) v' (T::Ts)).
        { 
          assert (Forall (fun T => exists l l', In (l ++ [T] ++ l') (nth ind (CoqType_to_camlType' mind Hparam Hfo) [])) (T::Ts)).
          { clear -HTs. set (l := T::Ts) in *. clearbody l.
            assert (exists l', In (l' ++ l) (nth ind (CoqType_to_camlType' mind Hparam Hfo) [])).  
            { exists []; eauto.  }
            clear T Ts HTs; revert H. induction l; econstructor.
            - destruct H as [l' HIn]. exists l'; exists l; eauto.
            - eapply IHl. destruct H as [l' HIn]. exists (l' ++ [a]). 
              now rewrite <- app_assoc. } 
          eapply Forall2_Forall_mix; [| apply H0]; clear H0 Hwit HkS Hk HTs HTs'. 
          unfold realize_value, to_realize_value in Hv'.
          induction Hv'; econstructor. 
          - clear IHHv'. intros [l0 [l0' HTs]].
            unshelve eapply CoqType_to_camlType'_Rel with (k:=#|l0|) in HTs; try reflexivity.
            3: { rewrite nth_error_app2; eauto. rewrite Nat.sub_diag. reflexivity. }
            destruct HTs as [i [? [? Hx ]]]; subst. 
            cbn in H0. unfold realize_term in H0.
            destruct H0 as [t [h [h' [Hheap ?]]]].
            specialize (H0 h h' _ Hheap). rewrite to_list_nth in H0.
            + rewrite CoqType_to_camlType'_length. lia.
            + pose (MCList.nth_error_spec (ind_bodies mind) (i - #|l0|)).
              destruct n. 2: { clear -H1 H2 l1. lia. }
              eapply IHstep in H0; eauto.
              2: { unfold CoqType_to_camlType; cbn. now rewrite CoqType_to_camlType'_length. }
              destruct H0 as [t' H0]. cbn. 
              exists (t',i - #|l0|). cbn. intros. specialize (H0 h0). destruct H0. 
              sq. repeat split; eauto. lia. 
              unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen, lookup_env. cbn.
              rewrite ReflectEq.eqb_refl. erewrite nth_error_nth'; cbn; [eauto|lia].
              Unshelve. eauto.  
          - eapply IHHv'. 
        }
        pose proof (Hv'Ts := Forall2_length H0).
        destruct (All_exists _ _ _ _ _ _ H0) as [lv' Hlv']. clear H0. 
        eapply Forall2_sym in Hlv'. cbn in Hlv'.
        pose proof (Forall2_forall _ _ Hlv'). clear Hlv'. rename H0 into Hlv'. 
        eexists (mkApps (tConstruct (mkInd kn ind) k' []) (map fst lv')).
        intro h. specialize (Hlv' h).  
        eapply Forall_Forall2_and_inv in Hlv'.
        destruct Hlv' as [Hlv' Hvallv'].
        eapply Forall2_and_inv in Hlv'. destruct Hlv' as [Heval Hlv'].
        split.
        2: { clear Hlv'. rewrite (compile_pipeline_tConstruct_cons Σ). 
            rewrite map_length. erewrite Forall2_length; eauto.
            pose proof (Forall2_length Hv').
            rewrite zip_length; try rewrite <- H0; cbn; lia.
            unfold lookup_constructor_args. rewrite Hlookup.
            unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup.
            cbn in Hlookup. rewrite ReflectEq.eqb_refl in Hlookup.
            assert (HEind : nth_error (ind_bodies mind) ind = Some Eind).
            { destruct (nth_error (ind_bodies mind) ind); now inversion Hlookup. }          
          assert (is_true (@firstorder_oneind [] mind Eind)).
          { clear - HEind Hfo; eapply forallb_nth_error with (n := ind) in Hfo.
            rewrite HEind in Hfo. exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth; try eapply e; eauto.
          2: { rewrite CoqType_to_camlType'_length in Hind. lia. }
          unfold blocks_until.
          unshelve erewrite filter_length_not_nil with (mind:=mind) (ind:=ind); eauto.
          unshelve erewrite CoqType_to_camlType'_nth; try eapply e; eauto.
          2: { rewrite CoqType_to_camlType'_length in Hind. lia. }
          econstructor.
          - apply Forall2_acc_cst. 
            rewrite MCList.map_InP_spec.
            rewrite <- (map_id v'). apply Forall2_map. 
            rewrite Forall2_map_left. 
            epose (Forall2_map_right (fun a b =>
            eval [] empty_locals h
              (compile_pipeline Σ a.1) h b) fst _ _). destruct i as [? ?].
            eapply H2 in Heval. 
            rewrite zip_fst in Heval; eauto. 
          - cbn. erewrite <- Forall2_length; eauto.
            clear Heval. eapply In_nth_error in HTs.
            destruct HTs as [k HTs]. pose proof (HEind' := HEind).
            unshelve erewrite CoqType_to_camlType'_nth in HTs; eauto.
            2: { rewrite CoqType_to_camlType'_length in Hind. lia. }                  
            eapply CoqType_to_camlType_oneind_nth in HTs.
            destruct HTs as [l' [HTs Hlength]].
            rewrite Hlength. eapply ctors_max_length; eauto.
        }
        clear Hv' Heval.  
        destruct Hwit as [Ts' [HTs'' [Hfilter _]]].
        pose proof (Hlookup':=Hlookup).
        unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup.
        cbn in Hlookup. rewrite ReflectEq.eqb_refl in Hlookup.
        assert (HEind : nth_error (ind_bodies mind) ind = Some Eind).
        { destruct (nth_error (ind_bodies mind) ind); now inversion Hlookup. }
        assert (is_true (@firstorder_oneind [] mind Eind)).
        { clear - HEind Hfo; eapply forallb_nth_error in Hfo; erewrite HEind in Hfo; exact Hfo. }
        unshelve erewrite CoqType_to_camlType'_nth in Hfilter, HTs,HTs', HTs''; eauto.
        2-5 : rewrite CoqType_to_camlType'_length in Hind; lia.
        unfold CoqType_to_camlType_oneind in Hfilter, HTs, HTs', HTs''. remember Eind as o. destruct o. 
        destruct andb_and. destruct (a _).  
        apply CoqType_to_camlType_ind_ctors_nth in HTs''.
        destruct HTs'' as [a0 [? [? ?]]]. rewrite Nat.sub_0_r in HTs'. rewrite HTs' in Hfilter.
        pose proof (i0' := i0). unshelve eapply nth_error_forallb in i0'; eauto.    
        unshelve epose proof (PCUICInductiveInversion.declared_constructor_valid_ty (Σ, univ_decl) [] mind Eind  
        {| inductive_mind := kn; inductive_ind := ind |} k' a0 [] _ _); eauto.
        destruct X as [sctype Hctype].
        { rewrite <- Heqo. cbn. econstructor; eauto. econstructor; eauto.
          unfold declared_minductive. cbn. now left. }
        { unfold consistent_instance_ext, consistent_instance; cbn. now rewrite Hmono. }
        inversion Hfilter. clear HTs HTs' Hfilter. rewrite H4 in Hlv', Hv'Ts. clear T Ts H4.  
        set (P := (fun a b => 0 <= a /\ a < #|ind_bodies mind| /\ b = Rel (#|ind_bodies mind| - S a))). 
        epose proof (Forall2_map_right (fun a => P (snd a)) snd). unfold P in H3.
        rewrite <- H3 in Hlv'. clear H3.
        epose proof (Forall2_map_left P snd). unfold P in H3.
        rewrite <- H3 in Hlv'. clear H3 P. 
        rewrite zip_snd in Hlv'; eauto. 
        eapply Forall2_All2 in Hlv'. revert Hvallv'; intro. 
        assert (Hcstr_indices : cstr_indices a0 = []).
          { apply length_nil. erewrite @cstr_indices_length with (Σ:=Σ) (ind:=(mkInd kn ind,k')); eauto. 
            2: { repeat split. cbn. left. reflexivity. all:cbn; eauto. } cbn. eapply nth_error_forall in Hindices; eauto.
                 cbn in Hindices. now rewrite Hindices. }
        eapply All_sq in Hvallv'. sq. eapply PCUICGeneration.type_mkApps.
        ++ eapply type_Construct; eauto. 
          ** unfold declared_constructor, declared_inductive. now cbn.
          ** unfold consistent_instance_ext, consistent_instance; cbn.
             now rewrite Hmono. 
        ++ unfold PCUICTyping.wf in wfΣ. inversion wfΣ as [_ wfΣ'].
          cbn in wfΣ'. inversion wfΣ'. clear X. inversion X0. inversion on_global_decl_d.
          eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
          inversion onInductives. unfold PCUICGlobalMaps.on_constructors in *. cbn in *.
          unfold type_of_constructor. cbn.
          eapply All2_nth_error_Some  in onConstructors; eauto.
          destruct onConstructors as [l' [? onConstructor]].          
          pose proof (Hlets := on_lets_in_type _ _ _ _ _ _ _ _ _ onConstructor). cbn in Hlets. 
          revert Hctype. erewrite cstr_eq; eauto. rewrite Hparam. cbn. 
          unfold cstr_concl, cstr_concl_head. 
          rewrite Hparam Hcstr_indices. cbn. rewrite <- plus_n_O. intro.  
          revert Hvallv'; intro.   
          eapply @All_All2_refl with (R := fun a b: term * nat =>
            (Σ, univ_decl);;; []
             |- fst a : tInd {| inductive_mind := kn;
             inductive_ind := #|ind_bodies mind| - S (snd b) |} []) in Hvallv'.
          eapply @All2_map_left with (P := fun a b =>
            (Σ, univ_decl);;; []
             |- a : tInd {| inductive_mind := kn;
                   inductive_ind := #|ind_bodies mind| - S (snd b) |} []) in Hvallv'.
          eapply @All2_map_right with (P := fun a b =>
            (Σ, univ_decl);;; []
                     |- a : tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) in Hvallv'.
          set (lind := map snd lv') in *. set (lterm := map fst lv') in *. clearbody lterm lind. clear lv'.
          revert Hlv'; intro. rewrite H2 in Hlv'. clear H2. revert x Hlv'. rewrite Hparam app_nil_r. intros. 
          epose (Hnd := firstorder_nonDepProd). edestruct Hnd as [Hnd' [Hndfst Hndsnd]]; eauto.
          1: eapply firstorder_con_notApp; eauto.
          rewrite <- Hndsnd. eapply nonDep_typing_spine with (s:=sctype) ; eauto. 
          { revert Hctype; intro. unfold type_of_constructor in Hctype. cbn in Hctype.
            erewrite cstr_eq in Hctype; eauto. rewrite Hparam in Hctype. cbn in Hctype. 
            unfold cstr_concl, cstr_concl_head in Hctype. rewrite Hparam Hcstr_indices app_nil_r in Hctype.
            cbn in Hctype. rewrite <- plus_n_O in Hctype. eauto. }
          rewrite Hndfst. now apply All2_map_right.
  Qed.


  Parameter verified_malfunction_pipeline_theorem : forall `{Heap} `{Pointer} `{WcbvFlags} (efl := extraction_env_flags) (cf := extraction_checker_flags)
  univ retro univ_decl kn mind
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hnparam : ind_npars mind = 0)
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hfo : is_true (forallb (@firstorder_oneind (firstorder_env (Σ0 , univ_decl)) mind) (ind_bodies mind))),
  let adt := CoqType_to_camlType mind Hparam Hfo in
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  forall (HΣ : PCUICTyping.wf_ext Σ),
  with_constructor_as_block = true ->
  forall t ind Eind, 
  ind < List.length (snd adt) ->
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  forall (wt : Σ ;;; [] |- t : tInd (mkInd kn ind) [])
  (expΣ : PCUICEtaExpand.expanded_global_env Σ)
  (expt : PCUICEtaExpand.expanded Σ [] t), 
  forall h v (Heval : ∥PCUICWcbvEval.eval Σ t v∥),  
  let Σb := (Transform.transform verified_named_erasure_pipeline (Σ, v) (ErasureCorrectness.precond2 _ _ _ _ expΣ expt wt Normalisation _ Heval)).1 in
  ∥ eval [] (fun _ => fail "notfound") h (compile_pipeline Σ t) h (compile_value_mf' _ Σ Σb v)∥.
  

  Parameter verified_named_erasure_pipeline_fo : forall `{Heap} `{Pointer} `{WcbvFlags} (efl := extraction_env_flags) (cf := extraction_checker_flags)
  univ retro univ_decl kn mind
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hnparam : ind_npars mind = 0)
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hfo : is_true (forallb (@firstorder_oneind (firstorder_env (Σ0 , univ_decl)) mind) (ind_bodies mind))),
  let adt := CoqType_to_camlType mind Hparam Hfo in
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  forall (HΣ : PCUICTyping.wf_ext Σ),
  with_constructor_as_block = true ->
  forall t ind Eind, 
  ind < List.length (snd adt) ->
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  forall (wt : Σ ;;; [] |- t : tInd (mkInd kn ind) [])
  (expΣ : PCUICEtaExpand.expanded_global_env Σ)
  (expt : PCUICEtaExpand.expanded Σ [] t), 
  forall v Heval,
  let Σb := (Transform.transform verified_named_erasure_pipeline (Σ, v) (ErasureCorrectness.precond2 _ _ _ _ expΣ expt wt Normalisation _ Heval)).1 in
  ErasureCorrectness.firstorder_evalue_block Σb (ErasureCorrectness.compile_value_box Σ v []).
  
  Lemma firstn_firstn_length {A} (l : list A) n l' : n <= #|l| -> firstn n (firstn n l ++ l') = firstn n l.
  Proof.
    induction l in n |- *; simpl; auto.
    destruct n=> /=; auto. inversion 1. 
    destruct n=> /=; auto. intros.
    assert (n<=#|l|) by lia. now rewrite IHl.
  Qed.

  Lemma CoqValue_to_CamlValue {P : Pointer} {H : CompatiblePtr P P} (cf := extraction_checker_flags)
  (efl := EInlineProjections.switch_no_params EWellformed.all_env_flags)  {has_rel : EWellformed.has_tRel} {has_box : EWellformed.has_tBox}  
  {HP : @Heap P} `{@CompatibleHeap P P _ _ _} `{WcbvFlags} `{EWellformed.EEnvFlags}
  univ retro univ_decl kn mind
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hnparam : ind_npars mind = 0)
  (Hind : ind_finite mind == Finite )
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Σ0 := mk_global_env univ [(kn , InductiveDecl mind)] retro)
  (Hfo : is_true (forallb (@firstorder_oneind (firstorder_env (Σ0 , univ_decl)) mind) (ind_bodies mind))) :
  let adt := CoqType_to_camlType mind Hparam Hfo in
  let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl) in
  PCUICTyping.wf_ext Σ ->
  with_constructor_as_block = true ->
  forall t ind Eind, 
  ind < List.length (snd adt) ->
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  forall (wt : Σ ;;; [] |- t : tInd (mkInd kn ind) [])
  (expΣ : PCUICEtaExpand.expanded_global_env Σ)
  (expt : PCUICEtaExpand.expanded Σ [] t), 
    forall h v, R_heap h h ->
    eval [] empty_locals h (compile_pipeline Σ t) h v
    -> realize_ADT _ _ [] [] adt [] All_nil ind v.
  Proof.
    intros ? ? HΣ ? ? ? ? ? Hlookup ? ? ? ? ? ? Heval_compile. pose proof Normalisation. 
    assert (Hax: PCUICClassification.axiom_free Σ).
    { intros ? ? X. now inversion X. }
    unshelve epose proof (PCUICNormalization.wcbv_normalization HΣ _ wt) as [val Heval]; eauto.
    unshelve epose proof (wval := PCUICClassification.subject_reduction_eval wt Heval).
    assert (Hval_fo : firstorder_value Σ [] val).
    { cbn. eapply firstorder_value_spec with (args := []); eauto. 
      - now eapply PCUICWcbvEval.eval_to_value.
      - unfold firstorder_ind; cbn. rewrite ReflectEq.eqb_refl.
        unfold firstorder_mutind. rewrite andb_and. split; eauto. 
        now destruct ind_finite. } 
    unfold adt in *. clear adt.  
    revert ind H4 Hlookup wt Heval v Heval_compile wval.
    unshelve eapply (firstorder_value_inds Σ [] (fun val => _) _ val Hval_fo).
    cbn. intros. clear val Hval_fo.    
    epose proof (Heval' := verified_malfunction_pipeline_theorem univ retro univ_decl kn mind Hparam Hindices Hnparam 
    Hmono Hfo HΣ _ t ind Eind _ _ wt expΣ expt h _ (sq Heval)).
    unshelve epose proof (Hfo' := verified_named_erasure_pipeline_fo univ retro univ_decl kn mind Hparam Hindices Hnparam 
    Hmono Hfo HΣ _ t ind Eind _ _ wt expΣ expt _ (sq Heval)); eauto. 
    Opaque verified_named_erasure_pipeline. 
    simpl in Heval', Hfo'. sq. 
    set (Σp := {| universes := _ |}) in *.
    clear pandi X. 
    unshelve eapply eval_det in Heval'; eauto.
    2: { intros ? ? ? X. inversion X. }
    2: { econstructor. }
    destruct Heval' as [_ Heval'].
    set (tv := mkApps (tConstruct i n ui) args) in *. 
    epose proof (Hdecomp := PCUICAstUtils.decompose_app_mkApps (tConstruct i n ui) args).
    forward Hdecomp; eauto.
    rewrite -/ Σ in Heval', Hfo'.
    pose proof (wval' := wval). 
    eapply PCUICInductiveInversion.Construct_Ind_ind_eq' with (args' := []) in wval; eauto.
    repeat destruct wval as [? wval]. repeat destruct p.
    subst. simpl in *.
    set (i := {| inductive_mind := kn; inductive_ind := ind |}) in *.
    destruct d as [[dx dx0] d]. cbn in dx, dx0, d. 
    destruct dx as [dx | dx]; inversion dx. symmetry in H11. subst. clear dx.  
    clear x4 x5 s1 s2 s spine_dom_wf inst_ctx_subst inst_subslet c c0. destruct s0 as [_ _ ? _].
    rewrite Hnparam skipn_0 in inst_ctx_subst. 
    unfold  PCUICContextSubst.context_subst in inst_ctx_subst. 
    rewrite (compile_value_mf_eq _ _ _ _ _ _ _ _ _ _ [] wt) in Heval'; eauto.  
    { intros. cbn in H10. destruct (i0 == _); inversion H10. now subst. }
    { unshelve econstructor. 1,2: exact []. all: eauto. }
    cbn in Heval'. cbn in Hfo'. 
    inversion Hfo' as [? ? ? Hlookup' HForall_fo Heq]. clear Hfo'.
    unfold compile_named_value in Heval'. unfold tv in Heq, Heval'.  
    erewrite compile_value_box_mkApps in Heq. cbn in Heq.
    erewrite compile_value_box_mkApps in Heval'. cbn in Heval'.
    unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args in *. 
    cbn in Hlookup'.
    set (EGlobalEnv.lookup_env _ _) in *.  
    case_eq o. 2: { intro X0; rewrite X0 in Hlookup'. inversion Hlookup'. }
    intros g Hg; rewrite Hg in Hlookup'. 
    destruct g. { inversion Hlookup'. }
    unfold ErasureCorrectness.pcuic_lookup_inductive_pars, EGlobalEnv.lookup_constructor_pars_args in *. 
    rewrite PCUICExpandLetsCorrectness.trans_lookup in Heval'.
    cbn in *. rewrite ReflectEq.eqb_refl in Heval', Heq. inversion Heq. clear Heq. subst.     
    cbn in Heval'. unfold Compile.lookup_constructor_args, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in Heval'.
    cbn in Heval'. unfold o in Hg. cbn in *.  
    pose proof (Hdecl := Hg).
    unshelve eapply verified_named_erasure_pipeline_lookup_env_in with (args := [])in Hg; eauto.
    cbn in *. destruct Hg as [decl' [Hlookup_decl Hdecl']]. rewrite ReflectEq.eqb_refl in Hlookup_decl. 
    inversion Hlookup_decl. subst. clear Hlookup_decl. rewrite Hdecl in Heval'. 
    rewrite Hnparam skipn_0 in Heval'. rewrite map_map in Heval'.
    cbn in Heval', Hlookup'. unfold realize_ADT.
    rewrite map_mapi nth_error_mapi in Heval'.
    rewrite map_mapi nth_error_mapi in Hlookup'.
    exists 1. cbn.
    rewrite CoqType_to_camlType'_length.
    assert (Hind' : ind <? #|ind_bodies mind|). 
    { rewrite CoqType_to_camlType'_length in H9. now apply Nat.leb_le. }
    rewrite Hind'. case_eq (nth_error (ind_bodies mind) ind).
    2:{ intro Hnone. rewrite Hnone in Hlookup'. inversion Hlookup'. }
    intros indbody Hindbody. rewrite Hindbody in Heval', Hlookup'.
    assert (x0 = indbody). { now clear -dx0 Hindbody. } subst. clear dx0. 
    revert Heval'. cbn. destruct args. 
    - left. cbn in *. inversion Heval'.
      subst. clear Heval'. repeat rewrite nth_error_map in Hlookup'.
      rewrite d in Hlookup'. cbn in Hlookup'. revert d; intro d.   
      assert (forall l, #|filter (fun x : nat => match x with | 0 => true | S _ => false end)
      (map EAst.cstr_nargs
      (map (fun cdecl : constructor_body => {| Extract.E.cstr_name := cstr_name cdecl; Extract.E.cstr_nargs := cstr_arity cdecl |})
      (map (PCUICExpandLets.trans_constructor_body ind mind) l)))| = 
      #|filter (fun x : nat => match x with | 0 => true | S _ => false end) (map cstr_nargs l)|).
      {
        induction l; [eauto|cbn]. destruct a; cbn.   
        assert (cstr_arity0 = #|cstr_args0|) by todo "".
        rewrite <- H10. destruct cstr_arity0; cbn;  eauto; f_equal; eauto.
      }
      repeat rewrite firstn_map. rewrite H10 -firstn_map.
      unshelve erewrite filter_length_nil. 5:eauto. 4:eauto. eauto.
      unshelve erewrite CoqType_to_camlType'_nth.
      4: eauto. 3: { now apply Nat.leb_le. }
      { eapply nth_error_forallb; eauto. }
      unshelve eapply CoqType_to_camlType_oneind_nth' in d as [l' [d ?]]; eauto.  
      2: eapply nth_error_forallb; eauto. 
      pose proof (Hd := PCUICReduction.nth_error_firstn_skipn d).
      rewrite Hd. 
      set (CoqType_to_camlType_oneind _ _ _ _) in *.
      rewrite firstn_firstn_length. { eapply nth_error_Some_length in d. lia. }
      assert (l' = []). { apply length_zero_iff_nil. inversion Hlookup'. rewrite H11. todo "". }  
      set (k := #| _ |). set (f := fun x : list camlType => _). set (ll := _ ++ _).
      epose proof (filter_firstn' _ k f ll) as [? [_ [? [? [? [? ?]]]]]].
      { unfold k, f, ll. rewrite filter_app. cbn. rewrite H12. rewrite app_length. cbn. lia. }
      apply Existsi_spec. repeat eexists; cbn; try lia.
      unfold k, f, ll. rewrite filter_app. cbn. subst. rewrite app_length. cbn. lia.
      rewrite Nat.sub_0_r. eauto. 

    - right. inversion Heval'. subst. clear Heval'.  cbn in *.
      rewrite map_map in H12. set (compile_val := fun x : term => CompileCorrect.compile_value _ _ ) in H12.
      change (Forall2 vrel vals (map compile_val (t0 :: args))) in H12. eapply (Forall2_map_right _ compile_val) in H12. 
      repeat rewrite nth_error_map in Hlookup'.
      rewrite d in Hlookup'. cbn in Hlookup'. revert d; intro d.   
      assert (forall l, #|filter (fun x : nat => match x with | 0 => false | S _ => true end)
      (map EAst.cstr_nargs
      (map (fun cdecl : constructor_body => {| Extract.E.cstr_name := cstr_name cdecl; Extract.E.cstr_nargs := cstr_arity cdecl |})
      (map (PCUICExpandLets.trans_constructor_body ind mind) l)))| = 
      #|filter (fun x : nat => match x with | 0 => false | S _ => true end) (map cstr_nargs l)|).
      {
        induction l; [eauto|cbn]. destruct a; cbn.   
        assert (cstr_arity0 = #|cstr_args0|) by todo "".
        rewrite <- H10. destruct cstr_arity0; cbn;  eauto; f_equal; eauto.
      }
      repeat rewrite firstn_map. rewrite H10 -firstn_map. clear H10. 
      unshelve erewrite filter_length_not_nil. 4,5,7:eauto.

      unshelve erewrite CoqType_to_camlType'_nth.
      4: eauto. 3: { now apply Nat.leb_le. }
      { eapply nth_error_forallb; eauto. }
      unshelve eapply CoqType_to_camlType_oneind_nth' in d as [l' [d ?]]; eauto.  
      2: eapply nth_error_forallb; eauto.
      
      pose proof (Hd := PCUICReduction.nth_error_firstn_skipn d).
      rewrite Hd. 
      set (CoqType_to_camlType_oneind _ _ _ _) in *.
      rewrite firstn_firstn_length. { eapply nth_error_Some_length in d. lia. }
      set (k := #| _ |). set (f := fun x : list camlType => _). set (ll := _ ++ _).
      destruct l'. { 
        inversion Hlookup'. 
        assert (#|cstr_args x1| = cstr_arity x1) by todo "". rewrite H13 in H11. 
        rewrite - H10 in H11. rewrite Hnparam skipn_0 in H11. cbn in H11. inversion H11. } 
      epose proof (filter_firstn' _ k f ll) as [? [_ [? [? [? [? ?]]]]]].
      { unfold k, f, ll. rewrite filter_app. cbn. rewrite app_length. cbn. lia. }
      apply Existsi_spec. repeat eexists; cbn; try lia.
      { unfold k, f, ll. rewrite filter_app. cbn. subst. rewrite app_length. cbn. lia. }
      2: { rewrite Nat.sub_0_r. eauto. }
      unfold ll, f, l in *; clear ll f l. 
      revert H7 H4 H12; intros.
      set (args' := t0 :: args) in *. clearbody args'. clear H15.
      
      induction H7; inversion H12.
      + subst. econstructor; eauto.  

      unfold realize_value, to_realize_value. cbn. 
      eapply Forall2_Forall_mix in H12; eauto.  


      

      
      subst. clear Heval' Heq. repeat rewrite nth_error_map in Hlookup'. 
      repeat rewrite firstn_map. destruct d as [[dx dx0] d]. cbn in dx, dx0, d. 
      destruct dx as [dx | dx]; inversion dx. symmetry in H9. subst. clear dx.  
      assert (x0 = indbody). { now clear -dx0 Hindbody. } subst. clear dx0. 
      rewrite d in Hlookup'. cbn in Hlookup'. revert d; intro d.   
      destruct indbody. cbn. destruct andb_and. destruct (a _). cbn in d.
      apply Existsi_spec. repeat eexists; cbn; try lia.

      
      unfold CoqType_to_camlType_ind_ctors.
      
      rewrite filter_map. repeat rewrite map_length.
      destruct indbody. cbn.
      unfold andb_and. 
      subst.
      
      unfold lookup_env in Heval'.  
      rewrite Hlookup_decl in Heval'. 
 
    
    erewrite verified_malfunction_pipeline_compat in Heval'.
    


    rewrite compile_value_box_mkApps in Heval'. 
    simpl in *.
    unfold ErasureCorrectness.pcuic_lookup_inductive_pars in Heval'.
    rewrite PCUICExpandLetsCorrectness.trans_lookup in Heval'.
    unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup. 
    simpl in Hlookup. 
    
    
    set (lookup_env _ _) in *.  
    case_eq o. 2: { intro X; rewrite X in Hlookup. inversion Hlookup. }
    destruct g; intro X; rewrite X in Hlookup. { inversion Hlookup. }
    destruct nth_error; inversion Hlookup. subst. clear Hlookup.



    rewrite X in Heval'. simpl in Heval'. cbn in Heq. rewrite compile_value_box_mkApps in Heq.
    cbn in Heq.  unfold ErasureCorrectness.pcuic_lookup_inductive_pars in *. unfold o in X. rewrite X in Heq.
    inversion Heq. subst. clear Heq.     
    unfold EGlobalEnv.lookup_constructor_pars_args, Compile.lookup_constructor_args, EGlobalEnv.lookup_constructor in *.
    simpl in *. 
    unfold EGlobalEnv.lookup_inductive in *. cbn in Heval'. 
    set (EGlobalEnv.lookup_env _ _) in *. cbn in o0.   
    rewrite Hnparam in Heval'. rewrite skipn_0 in Heval'.
    destruct o0; [|inversion Hlookup'].


    destruct g. destruct nth_error; inversion Hlookup'; clear Hlookup'.
    rewrite Hnparam in H9. rewrite skipn_0 in H9.
    destruct l.
    simpl in *.
    - inversion Heval'; clear Heval'; subst. clear m c1 H8 H9 X.  
      exists 1. cbn. 
      apply leb_correct in H4. unfold Nat.ltb; rewrite H4; cbn. 
      left. generalize dependent o0. unfold CoqType_to_camlType'. destruct mind. cbn in *.
      destruct ind_bodies0; cbn in *.
      admit.
      destruct andb_and. destruct ind; cbn. econstructor.     
      unfold CoqType_to_camlType'. 
      induction step. 
    econstructor.      cbn in H9.   
    simpl in Hfo_evalue.
    as [compile_val ?].
    
    pose proof (ErasureCorrectness.lambdabox_pres_fo) as [compile_val ?].
    simpl in Heval'. rewrite Hnparam in Heval'. rewrite skipn_0 in Heval'.
    destruct H7. destruct H7.  

    destruct l.
    - simpl in Heval'.    
    simpl in Heval'. 
    inversion Heval'.  destruct g.  
    unfold compile_value_mf, compile_value_mf_aux, ErasureCorrectness.compile_value_box in Heval'.
    simpl in Heval'.    
    PCUICClassification.notCoInductive.   }
     
    unshelve epose proof (Hcan := PCUICCanonicity.pcuic_canonicity _ _ _ _ [] _ HΣ wt). 
    { intros ? ? X. now inversion X. }
    destruct Hcan as [tv' [[wtv' tv_eq] tv_head]].

  Admitted.  *)

From Malfunction Require Import CompileCorrect Pipeline. 

Lemma compile_compose {P:Pointer} {H:Heap} {HP : @CompatiblePtr P P} (efl := extraction_env_flags)
  {HH : @CompatibleHeap _ _ _ H H} 
  (Hvrel_refl : forall v, vrel v v)
  (Hheap_refl : forall h, R_heap h h)
  `{WcbvFlags} (cf:=config.extraction_checker_flags) 
  (Σ:global_env_ext_map) h h' t u' u v w na A B :
  ∥ Σ ;;; [] |- t : tProd na A B ∥ ->
  ~ ∥Extract.isErasable Σ [] t∥ -> 
  eval [] empty_locals h (compile_pipeline Σ u) h v ->
  eval [] empty_locals h u' h' v ->
  eval [] empty_locals h (Mapply (compile_pipeline Σ t, [u'])) h' w ->
  ∥{w' & vrel w w' /\ 
        eval [] empty_locals h (compile_pipeline Σ (tApp t u)) h w'}∥.
Proof.
  intros Htyp Herase Hu Hu' Happ.
  erewrite compile_app; eauto.
  inversion Happ; subst. 
  - epose proof (compile_pure _ t).
    eapply isPure_heap in H1 as [Hfpure heq]; eauto.
    2: intros; cbn; eauto. symmetry in heq; subst. pose proof (Hu_copy := Hu).
    eapply isPure_heap in Hu as [Hvpure _]; try eapply compile_pure; intros; cbn in *; eauto.
    eapply eval_det in Hu' as [? ?]; eauto. 3: econstructor.
    2: intros ? ? ? Hempty; inversion Hempty.
    destruct Hfpure as [? Hepure]. eapply isPure_heap_irr with (h'':=h) in H8; eauto.
    2: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. 
         eapply isPure_value_vrel'; eauto. }
    eapply eval_sim with (iglobals := []) in H8 as [[h'' [w' [? [? ?]]]]]; eauto.
    2: { eapply vrel_add; eauto. intro. eauto. }
    sq. exists w'. split; eauto. econstructor 3; eauto. 
    eapply isPure_heap_irr; eauto. 
    { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. }
  - epose proof (compile_pure _ t).
    eapply isPure_heap in H1 as [Hfpure heq]; eauto.
    2: intros; cbn; eauto. symmetry in heq; subst. pose proof (Hu_copy := Hu).
    eapply isPure_heap in Hu as [Hvpure _]; try eapply compile_pure; intros; cbn in *; eauto.
    eapply eval_det in Hu' as [? ?]; eauto. 3: econstructor.
    2: intros ? ? ? Hempty; inversion Hempty.
    destruct Hfpure as [? Hepure]. 
    assert (isPure e).
    { rewrite nth_nth_error in H6. 
      eapply (nth_error_forall (n := n)) in Hepure; cbn in *; eauto.
      2: destruct nth_error; inversion H6; subst; eauto.
      eauto. }
    eapply isPure_heap_irr with (h'':=h) in H9; eauto.
    2: { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto. 
         eapply isPure_value_vrel'; eauto.
         eapply isPure_add_self; eauto. }
    eapply eval_sim with (iglobals := []) in H9 as [[h'' [w' [? [? ?]]]]]; eauto.
    2: { eapply vrel_add; eauto. intro. eauto. }
    sq. exists w'. split; eauto. econstructor 4; eauto. 
    eapply isPure_heap_irr; eauto.
    { intro; cbn. unfold Ident.Map.add. destruct Ident.eqb; eauto.
      eapply isPure_add_self; eauto.
     }
  - erewrite compile_function in H7; eauto. inversion H7.
Qed.  

From MetaCoq.PCUIC Require Import PCUICWellScopedCumulativity. 

Lemma Prod_ind_irred `{checker_flags} Σ Γ f na kn ind ind' X :
  let PiType := tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind') []) in
  wf_ext Σ ->
  Σ ;;; Γ |- f : PiType ->
  Σ ;;; Γ ⊢ PiType ⇝ X ->
  PiType = X.
Proof.
  intros ? ? Hf Hred. 
  eapply PCUICConversion.invert_red_prod in Hred as [A' [B' [? [? ?]]]]; subst.
  unfold PiType. f_equal. 
  - eapply PCUICReduction.red_rect'; eauto. intros; subst.
    eapply PCUICNormal.red1_mkApps_tInd_inv with (v:=[]) in X1 as [? [? ?]]; subst.
    inversion o.
  - eapply PCUICReduction.red_rect'; eauto. 2: eapply c. intros; subst.
    eapply PCUICNormal.red1_mkApps_tInd_inv with (v:=[]) in X1 as [? [? ?]]; subst.
    inversion o.
Qed. 

Lemma Prod_ind_principal `{checker_flags} Σ Γ f na kn ind ind' :
  let PiType := tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind') []) in
  wf_ext Σ ->
  Σ ;;; Γ |- f : PiType ->
  forall B, Σ ;;; Γ |- f : B -> Σ ;;; Γ ⊢ PiType ≤ B.
Proof. 
  intros ? ? Hf B HB.
  pose proof (HB' := HB); eapply PCUICPrincipality.principal_type in HB as [Pf Hprinc]; eauto.
  pose proof (Hprinc' := Hprinc); specialize (Hprinc _ Hf) as [? ?].
  assert (Σ ;;; Γ ⊢ Pf = PiType).
  { 
    eapply ws_cumul_pb_alt_closed in w as [? [? [[? ?] ?]]].
    eapply Prod_ind_irred in c; eauto.
    subst.
    eapply ws_cumul_pb_alt_closed. exists x; exists PiType. repeat split; eauto.
    inversion c0; subst; clear c0; econstructor; eauto.
    inversion X1; subst; clear X1; econstructor; eauto. 
    unfold PCUICEquality.R_global_instance_gen, PCUICEquality.R_opt_variance in *. cbn in *.
    destruct lookup_inductive_gen; eauto. destruct p. destruct destArity; eauto.
    destruct p. destruct context_assumptions; eauto. cbn in *. destruct ind_variance; eauto.
    induction u; try econstructor; eauto. 
    }
  specialize (Hprinc' _ HB') as [? ?].
  etransitivity; eauto. eapply PCUICContextConversion.ws_cumul_pb_eq_le; symmetry; eauto.
Qed.  

Lemma interoperability_firstorder_function {funext:Funext} {P:Pointer} {H:Heap} {HP : @CompatiblePtr P P}
  {HH : @CompatibleHeap _ _ _ H H} 
  (Hvrel_refl : forall v, vrel v v)
  (Hheap_refl : forall h, R_heap h h) `{WcbvFlags} (efl := extraction_env_flags) (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind 
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hnparam : ind_npars mind = 0)
  (Hfinite : ind_finite mind == Finite)
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) ind ind' Eind Eind' f na l:
  let adt := CoqType_to_camlType mind Hparam Hfo in
  let Σ : global_env_ext_map := (build_global_env_map (mk_global_env univ [(kn , InductiveDecl mind)] retro), univ_decl) in
  let global_adt := add_ADT _ _ [] [] kn adt in 
  pcuic_good_for_extraction Σ ->
  ind_sort Eind = Universe.lType l ->
  ind_sort Eind' = Universe.lType l ->
  PCUICTyping.wf_ext (Σ,univ_decl) ->
  PCUICEtaExpand.expanded_global_env Σ ->
  PCUICEtaExpand.expanded Σ [] f ->
  with_constructor_as_block = true ->
  ind < List.length (snd adt) ->
  ind' < List.length (snd adt) ->
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  lookup_inductive Σ (mkInd kn ind') = Some (mind, Eind') ->
  ∥ Σ ;;; [] |- f : tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind') []) ∥ ->
  realize_term _ _ [] []
        global_adt (Arrow (Adt kn ind []) (Adt kn ind' [])) 
        (compile_pipeline Σ f).
Proof.
  intros ? ? ? Hextract ? Hind_sort wfΣ expΣ expf ? ? ? Hlookup Hlookup'. intros. simpl. rewrite ReflectEq.eqb_refl.
  unfold to_realize_term. cbn. 
  pose proof (wfΣ_ext := wfΣ). destruct wfΣ as [wfΣ ?].
  intros t Ht. unfold to_realize_term in *. intros h h' v Heval.
  pose proof (Hlookup'' := Hlookup).
  pose proof (Hlookup''' := Hlookup').
  unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup, Hlookup'. cbn in Hlookup, Hlookup'.
  rewrite ReflectEq.eqb_refl in Hlookup, Hlookup'.
  assert (HEind : nth_error (ind_bodies mind) ind = Some Eind).
  { destruct (nth_error (ind_bodies mind) ind); now inversion Hlookup. }
  assert (Htype_ind : (Σ, univ_decl);;; []
  |- tInd {| inductive_mind := kn; inductive_ind := ind |}
       [] : (tSort (ind_sort Eind))@[[]]).
  {  unshelve epose proof (type_Ind (Σ,univ_decl) [] (mkInd kn ind) [] mind Eind _ _ _).
  *** econstructor.
  *** unfold declared_constructor, declared_inductive. subst. now cbn.
  *** unfold consistent_instance_ext, consistent_instance; cbn.
     now rewrite Hmono.
  *** unfold ind_type in X. destruct Eind; cbn in *.
      unfold PCUICTyping.wf in wfΣ. inversion wfΣ as [_ wfΣ'].
      cbn in wfΣ'. inversion wfΣ'. clear X0. inversion X1. inversion on_global_decl_d.
      eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
      inversion onInductives. cbn in *.
      eapply nth_error_forall in Hindices; eauto. cbn in Hindices. rewrite Hindices in ind_arity_eq.                       
      cbn in ind_arity_eq. rewrite Hparam in ind_arity_eq. cbn in ind_arity_eq.
      now rewrite ind_arity_eq in X. }
  assert (HEind' : nth_error (ind_bodies mind) ind' = Some Eind').
  { destruct (nth_error (ind_bodies mind) ind'); now inversion Hlookup'. }
  assert (Htype_ind' : (Σ, univ_decl);;; []
  |- tInd {| inductive_mind := kn; inductive_ind := ind' |}
        [] : (tSort (ind_sort Eind'))@[[]]).
  {  unshelve epose proof (type_Ind (Σ,univ_decl) [] (mkInd kn ind') [] mind Eind' _ _ _).
  *** econstructor.
  *** unfold declared_constructor, declared_inductive. subst. now cbn.
  *** unfold consistent_instance_ext, consistent_instance; cbn.
      now rewrite Hmono.
  *** unfold ind_type in X. destruct Eind'; cbn in *.
      unfold PCUICTyping.wf in wfΣ. inversion wfΣ as [_ wfΣ'].
      cbn in wfΣ'. inversion wfΣ'. clear X0. inversion X1. inversion on_global_decl_d.
      eapply Alli_nth_error in onInductives; eauto. cbn in onInductives.
      inversion onInductives. cbn in *.
      eapply nth_error_forall in Hindices; eauto. cbn in Hindices. rewrite Hindices in ind_arity_eq.                       
      cbn in ind_arity_eq. rewrite Hparam in ind_arity_eq. cbn in ind_arity_eq.
      now rewrite ind_arity_eq in X. } 
  assert (Htype_ind'' : (Σ, univ_decl);;;
  [],,
  vass na
    (tInd {| inductive_mind := kn; inductive_ind := ind |}
       [])
  |- tInd {| inductive_mind := kn; inductive_ind := ind' |}
       [] : tSort (subst_instance_univ [] (ind_sort Eind'))).
  { eapply (PCUICWeakeningTyp.weakening  _ _ ([vass na (tInd {| inductive_mind := kn; inductive_ind := ind |} [])])) in Htype_ind'; cbn in Htype_ind'; eauto.
    repeat constructor. cbn. now eexists. }
  assert (Herase: ~ ∥ Extract.isErasable (Σ, univ_decl) [] f ∥).
  { sq. eapply EArities.not_isErasable with (u := subst_instance_univ [] (Universe.lType l)); eauto; intros. 
    - sq. eapply Prod_ind_irred ; eauto.
    - sq. eapply Prod_ind_principal; eauto. 
    - intro; sq; eauto.
    - sq. rewrite <- (sort_of_product_idem (subst_instance_univ [] (Universe.lType l))). eapply type_Prod; eauto.
      now rewrite -H1. now rewrite -Hind_sort. }
  inversion Heval; subst.
  - specialize (Ht _ _ _ H10).
    unshelve eapply camlValue_to_CoqValue in Ht. 14:eauto. all:eauto; cbn.
    destruct Ht as [t_coq Ht]. specialize (Ht h2). destruct Ht as [Ht_typ Ht_eval].
    eapply isPure_heap in H8; try eapply compile_pure; intros; cbn; eauto. cbn in H8.
    destruct H8 as [[? ? ] ?]. eapply isPure_heap in H13 as [? ?]; eauto.
    2: { unfold Ident.Map.add; intro. destruct (Ident.eqb s x); eauto.
      eapply isPure_heap in Ht_eval; try eapply compile_pure; intros; cbn; eauto. now destruct Ht_eval. } 
    subst. eapply compile_compose in H10 as [[? [? ?]]]; eauto.
    2: { eapply isPure_heap_irr,  Ht_eval; try eapply compile_pure; intros; cbn; eauto. }
    assert (v = x0). { unshelve eapply isPure_value_vrel_eq; eauto. }
    subst. sq. unshelve eapply Firstorder.verified_malfunction_pipeline_theorem with (t := tApp f t_coq). all:eauto.
    unshelve epose proof (type_App _ _ _ _ _ _ _ _ _ H5 Ht_typ); try exact (subst_insatance_univ [] (ind_sort Eind)); eauto.
    eapply PCUICEtaExpand.expanded_tApp; eauto. todo "expand".    
  - specialize (Ht _ _ _ H9).
    eapply camlValue_to_CoqValue in Ht; eauto; cbn.
    destruct Ht as [t_coq Ht].
    specialize (Ht h2).  destruct Ht as [Ht_typ Ht_eval].
    eapply isPure_heap in H8; try eapply compile_pure; intros; cbn; eauto.
    cbn in H8. destruct H8 as [[? ? ] ?]. rewrite nth_nth_error in H11. 
    case_eq (nth_error mfix n); intros;  [|rewrite H10 in H11; inversion H11].
    pose proof (H5_copy := H7). eapply (nth_error_forall (n:=n)) in H7; eauto.
    rewrite H10 in H11. subst. 
    eapply isPure_heap in H14 as [? ?]; eauto.
    2: { unfold Ident.Map.add; intro; destruct (Ident.eqb s y); eauto.
         eapply isPure_heap in Ht_eval; try eapply compile_pure; intros; cbn; eauto. 
         now destruct Ht_eval as [? _]. eapply isPure_add_self; eauto. }
    cbn in H7. subst. eapply compile_compose in H9 as [[? [? ?]]]; eauto.
    2: { eapply isPure_heap_irr,  Ht_eval; try eapply compile_pure; intros; cbn; eauto. }
    assert (v = x). { unshelve eapply isPure_value_vrel_eq; eauto. }
    subst. sq. unshelve eapply Firstorder.verified_malfunction_pipeline_theorem; try exact H11; eauto.
    sq. unshelve epose proof (type_App _ _ _ _ _ _ _ _ _ H5 Ht_typ); try exact (subst_instance_univ [] (ind_sort Eind)); eauto. 
    rewrite <- (sort_of_product_idem _). rewrite {2}H1 -Hind_sort.
    eapply type_Prod; eauto.
    eapply PCUICEtaExpand.expanded_tApp; eauto. todo "expand".    
  - rewrite (compile_function _ _ _ _ _ _ _ _ H5 _ H9) in H12; eauto. inversion H12.
Qed.

  