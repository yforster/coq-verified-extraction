Require Import ssreflect Eqdep_dec.
From MetaCoq.Utils Require Import All_Forall MCSquash MCList.
From MetaCoq.Common Require Import config Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICFirstorder.
From MetaCoq.Erasure Require Import EWcbvEval EWcbvEvalNamed.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.

From Malfunction Require Import Malfunction SemanticsSpec utils_array Compile.

Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.


Unset Elimination Schemes. 

Inductive camlType : Set :=
    Arrow : camlType -> camlType -> camlType
  | Rel : nat -> camlType
  | Adt : kername -> 
            (* number of the ADT in the mutual definition *) int -> 
            (* list of parameters *) list camlType -> 
            camlType.

Definition camlType_rect :
forall P : camlType -> Type,
       (forall c : camlType,
        P c -> forall c0 : camlType, P c0 -> P (Arrow c c0)) ->
       (forall n : nat, P (Rel n)) ->
       (forall (k : kername) (i : int) (l : list camlType), All P l -> P (Adt k i l)) ->
       forall c : camlType, P c. 
Proof. 
  intros P X X0 X1. fix f 1. intros c; destruct c.
  - eapply X; eauto.   
  - eapply X0; eauto. 
  - eapply X1; eauto. induction l; econstructor; eauto. 
Defined.
       
Set Elimination Schemes. 

Notation "A → B" := (Arrow A B) (at level 50). 

Definition isArrow T := match T with Arrow _ _ => true | _ => false end.

Definition ADT : Set := 
  (* number of parameters *)
  nat * list (
    list (list camlType) (* list of constructors for each ADT *)).

Inductive Existsi {A : Type} (P : nat -> A -> Prop) (n : nat) 
  : list A -> Prop :=
	  Existsi_cons_hd : forall x l, P n x -> Existsi P n (x :: l)
  | Existsi_cons_tl : forall (x : A) (l : list A),
                     Existsi P (S n) l -> Existsi P n (x :: l).

Lemma Existsi_spec A (P : nat -> A -> Prop) n (l:list A) : Existsi P n l -> 
  exists k x, n <= k /\ k < n + List.length l /\ P k x /\ nth_error l (k-n) = Some x.
Proof.
  induction 1.
  - exists n; exists x. cbn; repeat split; eauto. lia.
    now rewrite Nat.sub_diag.   
  - destruct IHExistsi as [k [a [Hk [Hk' [HP Ha]]]]].
    exists k; exists a. repeat split; eauto; cbn; try lia.
    assert (k - n = S (k - S n)) by lia.
    now rewrite H0. 
Defined. 

Section Realizability. 

  Variable _Heap:Heap.

  Definition realize_adt_type := 
      forall (params: list camlType), All (fun _ => value -> Prop) params -> 
              ((* number of the ADT in the mutual definition *) nat -> value -> Prop).

  Variable globals : list (Ident.t * value).
  
  Definition global_adt_decl := list (kername * realize_adt_type).

  Section Values. 

    Variable local_adt : list (value -> Prop).
    Variable global_adt : global_adt_decl.
  
    Definition realize_val (A:camlType) : value -> Prop.
    Proof.
      refine (camlType_rect _ _ _ _ A); clear A.
      - intros A PA B PB.
        refine (fun f => 
              exists locals' x t, f = Func (locals',x,t) /\ 
                forall v v' h h', 
                    PA v -> 
                    eval _ globals (Ident.Map.add x v locals') h t h' v' ->
                    PB v').
      - intros n. refine (List.nth n local_adt (fun _ => False)).
      - intros kn n params PAll.
        case (find (fun '(kn',_) => eq_kername kn kn') global_adt).
        + intros [_ Hrel]. exact (Hrel params PAll (int_to_nat n)).
        + intros; exact False. 
    Defined.
  End Values. 

  Fixpoint realize_ADT_gen_fix (global_adt : global_adt_decl) 
    (adt : list (list (list camlType))) (step : nat) : realize_adt_type.
  Proof.
    destruct step; [compute; intros; exact False|].
    intros params paramRel ind. 
    destruct (Nat.ltb ind (List.length adt)); [|intros; exact False].
    pose proof (constr_list := List.nth ind adt []). 
    refine (fun v => _\/_).
    - pose (constr_noarg := filter 
      (fun x => match x with [] => true 
            | _ => false end) constr_list).
      refine (Existsi (fun index Ts => v = value_Int (Int , Z.of_nat index)) 0 constr_noarg).
    - pose (constr_arg := filter 
      (fun x => match x with [] => false 
          | _ => true end) constr_list).
      refine (Existsi (fun index Ts => 
          exists vs, v = Block (int_of_nat index, vs) /\ _) 0 constr_arg). 
      refine (Forall2 (realize_val _ global_adt) Ts vs).
      refine (_ ++ _).
      + (* parameters *)
        clear -paramRel. induction paramRel; [exact []| ].
        refine (p :: IHparamRel).
      + (* recursive calls *)
        exact (to_list (realize_ADT_gen_fix global_adt adt step params paramRel) (List.length adt)).
  Defined.   

  Definition realize_ADT_gen (global_adt : global_adt_decl) 
    : ADT -> nat -> realize_adt_type :=
    fun '(n , adt) step params =>
      if (Nat.eqb n (List.length params)) 
      then realize_ADT_gen_fix global_adt adt step params
      else fun _ _ _ => False.

  Definition realize_ADT (global_adt : global_adt_decl) : ADT -> realize_adt_type :=
    fun adt params paramRel ind v => exists n, realize_ADT_gen global_adt adt n params paramRel ind v.

  Definition add_ADT (global_adt : global_adt_decl) (kn : kername) (adt : ADT) :  global_adt_decl := 
    (kn, realize_ADT global_adt adt) :: global_adt.

End Realizability.

Section firstorder.

  Context {Σb : list (kername * bool)}.

  Definition CoqType_to_camlType_oneind_type n k decl_type :
    is_true (@firstorder_type Σb k n decl_type) -> camlType.
  Proof.
    unfold firstorder_type. destruct (fst _).
    all: try solve [inversion 1].
    (* case of tRel with a valid index *)
    - intro; exact (Rel n0).
    (* case of tInd where Σb is saying that inductive_mind is first order *)
    - intro; destruct ind. exact (Adt inductive_mind (int_of_nat inductive_ind) []).
  Defined.  

  Fixpoint CoqType_to_camlType_ind_ctor n m cstr :
    is_true
    (alli
       (fun (k : nat) '{| decl_type := t |} =>
        @firstorder_type Σb m k t) n cstr) -> list camlType. 
  Proof. 
    destruct cstr; cbn; intros. 
    (* no more arguments *)
    * exact [].
    * apply MCProd.andb_and in H. destruct H. destruct c.
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
    - apply MCProd.andb_and in H. destruct H. 
      refine (_ :: CoqType_to_camlType_ind_ctors _ _ Hparam H0). clear H0.
      destruct c. unfold firstorder_con in H. cbn in H.
      eapply CoqType_to_camlType_ind_ctor; eauto.
  Defined. 

  Definition CoqType_to_camlType_oneind mind ind : 
    ind_params mind = [] -> 
    is_true (@firstorder_oneind Σb mind ind) -> list (list camlType).
  Proof.
    destruct ind. intros Hparam H. apply MCProd.andb_and in H.
    destruct H as [H _]. cbn in *. clear -H Hparam.
    eapply CoqType_to_camlType_ind_ctors; eauto. 
  Defined.

  Lemma bool_irr b (H H' : is_true b) : H = H'.
    destruct b; [| inversion H].
    assert (H = eq_refl). 
    eapply (K_dec _ (fun H => H = eq_refl)); eauto.
    etransitivity; eauto. 
    eapply (K_dec _ (fun H => eq_refl = H)); eauto.
    Unshelve. all: cbn; eauto. 
    all: intros b b'; pose (Coq.Bool.Bool.bool_dec b b'); intuition. 
  Defined.

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
    - cbn in *; destruct MCProd.andb_and. destruct (a Hfo). destruct (in_nil Hlarg).
    - cbn in Hlarg. destruct MCProd.andb_and. destruct (a0 Hfo). 
      destruct MCProd.andb_and. destruct (a1 i0). destruct a.
      unfold In in Hlarg. destruct Hlarg.
      2: { eapply IHind_ctors0; eauto. cbn. destruct MCProd.andb_and.
            destruct (a _). rewrite (bool_irr _ i6 i4). eauto.
            Unshelve.
            cbn. apply MCProd.andb_and. split; cbn; eauto. }
      cbn in Hparam, i3. rewrite Hparam in i3, H. rewrite app_nil_r in i3, H.
      clear - i3 HT H. set (rev cstr_args0) in *. rewrite <- H in HT. revert T HT. clear H. 
      set (Datatypes.length ind_bodies0) in *. revert i3. generalize n 0. clear.
      induction l; cbn; intros; [inversion HT|].
      destruct MCProd.andb_and. destruct (a0 i3). destruct a. 
      unfold In in HT. destruct HT.
      + rewrite <- H; eapply CoqType_to_camlType_oneind_type_fo; eauto.
      + eapply IHl. eauto.
  Defined.    

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
      2-3: unfold firstorder_oneind, firstorder_con; apply MCProd.andb_and in H0; destruct H0; eauto.
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
    Datatypes.length
      (CoqType_to_camlType_fix
        ind_bodies0 ind_finite0
        ind_params0 ind_npars0
        ind_universes0 ind_variance0
        Hparam ind_bodies1 Hfo) =
    Datatypes.length ind_bodies0); eauto.
    induction ind_bodies0; cbn; eauto.
    intros. f_equal. destruct MCProd.andb_and.
    destruct (a0 Hfo). eauto. 
  Qed.      

  
  Lemma CoqType_to_camlType_oneind_length mind Hparam x Hfo:
  List.length
      (CoqType_to_camlType_oneind
            mind x Hparam Hfo) =
  List.length (ind_ctors x).
  Proof.
    destruct x; cbn. destruct MCProd.andb_and.
    destruct (a Hfo). clear.
    induction ind_ctors0; cbn; eauto.
    destruct MCProd.andb_and. destruct (a0 i0).
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
    - destruct MCProd.andb_and. destruct (a0 Hfo).  
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
  
  Definition empty_heap : CanonicalHeap.(heapGen) (@SemanticsSpec.value CanonicalHeap) :=
    (int_of_nat 0 , fun _ => []).

  Lemma lookup_inductive_env Σ kn Emind Eind ind :
    EGlobalEnv.lookup_inductive Σ (mkInd kn ind) = Some (Emind,Eind) ->
    EGlobalEnv.lookup_env Σ kn = Some (EAst.InductiveDecl Emind).
  Proof.
    induction Σ; cbn; intros.
    - inversion H.
    - destruct (ReflectEq.eqb kn (fst a)); cbn in *.
      + f_equal. destruct (snd a); cbn in *; [inversion H|].
        destruct (nth_error (EAst.ind_bodies m) ind); now inversion H.  
      + apply IHΣ; eauto.
  Qed.


  Lemma filter_length_nil ind k mind Eind Hparam Hfo :
    let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
    nth_error (EAst.ind_bodies Emind) ind = Some Eind ->
  List.length
  (filter (fun x0 : nat =>  match x0 with
      | 0 => true
      | S _ => false
      end)
     (firstn k (map EAst.cstr_nargs (EAst.ind_ctors Eind)))) = 
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
    Admitted.                       

    Lemma filter_length_not_nil ind k mind Eind Hparam Hfo :
    let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
    nth_error (EAst.ind_bodies Emind) ind = Some Eind ->
  List.length
  (filter (fun x0 : nat =>  match x0 with
      | 0 => false
      | S _ => true 
      end)
     (firstn k (map EAst.cstr_nargs (EAst.ind_ctors Eind)))) = 
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
    Admitted.                       

  Fixpoint All_exists T A P l 
    (H: Forall (fun t : T => exists a : A, P t a) l) 
    : exists l' : list A, Forall2 P l l'.
  Proof. 
    destruct H.
    - exists []. econstructor.
    - refine (let '(ex_intro l' X) := 
              All_exists T A P _ H0 in _).
      destruct H as [p H].
      exists (p::l'). econstructor; eauto. 
  Qed. 

  Lemma Forall2_acc_cst (X A B : Type) (R : X -> A -> X -> B -> Prop) x l l' :
    Forall2 (fun a b => R x a x b) l l' -> Forall2_acc R x l x l'.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Lemma Forall2_sym :
  forall A B (P : A -> B -> Prop) l l',
    Forall2 P l l' ->
    Forall2 (fun x y => P y x) l' l.
  Proof.
  intros A B P l l' h.
  induction h.
  - constructor.
  - constructor. all: auto.
  Qed.
  
  Lemma CoqType_to_camlType_ind_ctors_nth 
    mind ind_ctors Hparam a k i :
    nth_error (CoqType_to_camlType_ind_ctors mind ind_ctors Hparam i) k
    = Some a ->
    exists a', nth_error ind_ctors k = Some a' /\
    exists i', 
    a = CoqType_to_camlType_ind_ctor 0 (Datatypes.length
    (ind_bodies mind)) (rev (cstr_args a' ++ ind_params mind)) i'.
  Proof. 
    revert a k i.
    induction ind_ctors; cbn; intros.
    - destruct k; inversion H.
    - destruct MCProd.andb_and. destruct (a1 _).
      destruct k; destruct a.
      + inversion H. eexists; split; [reflexivity|].
        cbn. cbn. unfold firstorder_con in i. cbn in i.
        apply MCProd.andb_and in i. destruct i as [i ?]. 
        exists i. f_equal. apply bool_irr.
      + eapply IHind_ctors; eauto.
  Qed. 

  Lemma CoqType_to_camlType_ind_ctors_length 
  l n m i:
  List.length (CoqType_to_camlType_ind_ctor n m l i) = List.length l.
  revert n m i. induction l; cbn; eauto; intros. 
  destruct MCProd.andb_and. destruct (a0 _). destruct a.
  cbn. now f_equal.
  Qed. 

  Lemma Forall_Forall2_and_inv {A B : Type} 
    {R : A -> B -> Prop} {P : A -> Prop} l l':
  Forall2 (fun (x : A) (y : B) => P x /\ R x y ) l l' ->
  Forall2 R l l' /\ Forall P l.
  Proof. 
    induction 1; repeat econstructor; now eauto.
  Qed.

  Axiom cstr_arity_length : forall x, cstr_arity x = List.length (cstr_args x).
  Axiom ctors_max_length : forall mind j k ind ctors,
    nth_error mind j = Some ind ->
    nth_error (ind_ctors ind) k = Some ctors -> 
    #|cstr_args ctors| < int_to_nat max_length.
  Axiom ind_ctors_wB : forall mind j ind,
    nth_error mind j = Some ind ->
    #|ind_ctors ind| <= Z.to_nat Uint63.wB.

  Definition camlValue_to_CoqValue_nil `{WcbvFlags} kn mind Eind 
    (Hparam : ind_params mind = [])
    (Hnparam : ind_npars mind = 0)
    (Hfo : is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind))) ind v :
    let adt := CoqType_to_camlType mind Hparam Hfo in
    let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
    let Σ := [(kn , EAst.InductiveDecl Emind)] in
    with_constructor_as_block = true ->
    ind < List.length (snd adt) ->
    EGlobalEnv.lookup_inductive Σ (mkInd kn ind) = Some (Emind, Eind) ->
    realize_ADT CanonicalHeap [] [] adt [] All_nil ind v ->
    exists t, ∥ EWcbvEval.value Σ t ∥ /\ 
    eval CanonicalHeap [] (fun _ => not_evaluated) empty_heap (compile Σ t) empty_heap v.
  Proof.
    intros adt Emind Σ Hflag Hind Hlookup [step Hrel].
    revert v kn mind Hparam Hnparam Hfo ind adt Emind Eind Σ Hflag Hind Hlookup Hrel. 
    induction step; intros;  [inversion Hrel|].
    apply leb_correct in Hind. simpl in Hrel, Hind. 
    unfold Nat.ltb in Hrel. rewrite Hind in Hrel.
    destruct Hrel as [Hrel | Hrel].
    - apply Existsi_spec in Hrel as [k [Ts [Hk [HkS [Hrel HTs]]]]].
      cbn in HkS.
      destruct (filter_firstn' _ _ _ _ HkS) as [k' [Hk' [Hfilter Hwit]]].
      eexists (EAst.tConstruct (mkInd kn ind) k' []); cbn; split.
      + sq. 
        pose (MCList.nth_error_spec (ind_bodies mind) ind).
        destruct n; cbn; intros.
        2: { apply leb_complete in Hind.
             rewrite CoqType_to_camlType'_length in Hind. lia. }    
        pose (MCList.nth_error_spec (ind_ctors x) k').
        destruct n; intros; eauto.
        ++ econstructor 2; eauto. cbn. rewrite ReflectEq.eqb_refl.
        unfold Emind. cbn. rewrite nth_error_map. 
        rewrite e. cbn. rewrite nth_error_map. rewrite e0. cbn.
        reflexivity.
        cbn; rewrite Hnparam; cbn.
        destruct Hwit as [a' [? [_ ?]]].
        destruct a'; [|inversion H1].
        assert (is_true (@firstorder_oneind Σb mind x)).
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
        unshelve erewrite CoqType_to_camlType'_nth in Hfilter; eauto.
        unshelve erewrite CoqType_to_camlType'_nth_length in Hk'; eauto.
        unshelve erewrite CoqType_to_camlType'_nth in H0; eauto.
        unfold CoqType_to_camlType_oneind in H0.
        destruct x. destruct MCProd.andb_and. destruct (a _).
        apply CoqType_to_camlType_ind_ctors_nth in H0.
        destruct H0 as [a0 [? [? ?]]].
        cbn in *.
        rewrite e0 in H0. inversion H0. destruct H5. clear H0.
        cbn in *.   
        apply f_equal with (f := @List.length _) in H3.
        rewrite CoqType_to_camlType_ind_ctors_length in H3.
        rewrite rev_length in H3. cbn in H3. rewrite app_length in H3.
        rewrite cstr_arity_length. lia. 
        ++ assert (is_true (@firstorder_oneind Σb mind x)). 
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth in Hk'; eauto.
          rewrite CoqType_to_camlType_oneind_length in Hk'.
          lia.   
      + rewrite compile_unfold_eq. simpl. 
        unfold lookup_constructor_args. rewrite Hlookup.
        rewrite Hrel. clear Hrel v.
        pose (MCList.nth_error_spec (ind_bodies mind) ind).
        apply leb_complete in Hind. rewrite CoqType_to_camlType'_length in Hind.    
        destruct n; [|lia].
        assert (is_true (@firstorder_oneind Σb mind x)).
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
        unshelve erewrite CoqType_to_camlType'_nth in Hfilter; eauto.
        cbn in Hlookup. rewrite ReflectEq.eqb_refl in Hlookup.
        unshelve erewrite filter_length_nil with (mind:=mind) (ind:=ind); eauto.
        2: { fold Emind. destruct (nth_error (EAst.ind_bodies Emind) ind); now inversion Hlookup. }
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
        apply ind_ctors_wB in e. lia.
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
      + pose proof (HTs':=HTs).
        apply filter_nth_error in HTs. destruct HTs as [HTs _].
        subst. inversion Hv'; subst.
        cbn in H2.  
        assert (Forall (fun v => (exists t : EAst.term,
      ∥ EWcbvEval.value Σ t ∥ /\
      eval CanonicalHeap []
        (fun _ : Ident.t => not_evaluated)
        empty_heap (compile Σ t) empty_heap v)) l').
        { clear HTs' Hv' H2.
          assert (exists l, incl Ts l /\ In l (nth ind (CoqType_to_camlType' mind Hparam Hfo) [])).
          { exists (T::Ts). split; eauto. eapply incl_tl; apply incl_refl. }
          clear HTs. rename H0 into HTs. 
          induction H4; [eauto|].
          econstructor; eauto.
          { destruct x.
          - destruct HTs as [? [? HTs]]. 
            eapply CoqType_to_camlType'_fo_alt in HTs.
            exfalso; apply HTs.
            apply H1. econstructor 1. reflexivity.
          - case_eq (n <? Datatypes.length
          (CoqType_to_camlType' mind Hparam Hfo)); intro Heq. 
          2: { apply Nat.leb_gt in Heq. cbn in H0. erewrite nth_overflow in H0.
            inversion H0. rewrite to_list_length. lia. }
          apply leb_complete in Heq. cbn in H0. 
          rewrite to_list_nth in H0; [lia|].
          pose (MCList.nth_error_spec (ind_bodies mind) ind).
          rewrite CoqType_to_camlType'_length in Hind.    
          destruct n0; [|lia].
          pose (MCList.nth_error_spec (ind_bodies mind) n).
          pose proof (Heq' := Heq). 
          rewrite CoqType_to_camlType'_length in Heq.    
          destruct n0; [|lia]. cbn.
          eapply IHstep with (ind := n); eauto. 
          eapply Heq'. cbn. rewrite ReflectEq.eqb_refl.
          cbn. rewrite nth_error_map e0. cbn. reflexivity.
          eauto.
          - inversion H0. 
          }
          eapply IHForall2. destruct HTs as [? [? HTs]].
          eexists; eauto. split; eauto.
          intros a Ha. apply H1. econstructor 2; eauto.     
        }
        destruct (All_exists _ _ _ _ H0) as [lv' Hlv'].           
        eapply Forall2_sym in Hlv'. 
        eapply Forall_Forall2_and_inv in Hlv'.
        destruct Hlv' as [Hlv' Hvallv'].
        apply Forall_All in Hvallv'.
        apply All_sq in Hvallv'. destruct Hvallv'.
        destruct T.
        (* not first-order *)
        * eapply CoqType_to_camlType'_fo_alt in HTs.
          exfalso; apply HTs. econstructor 1; eauto. 
        * case_eq (n <? Datatypes.length
          (CoqType_to_camlType' mind Hparam Hfo)); intro Heq. 
          2: { apply Nat.leb_gt in Heq. cbn in H2. erewrite nth_overflow in H2.
            inversion H2. rewrite to_list_length. lia. }
          apply leb_complete in Heq. cbn in H2. 
          rewrite to_list_nth in H2; [lia|].
          pose (MCList.nth_error_spec (ind_bodies mind) ind).
          rewrite CoqType_to_camlType'_length in Hind.    
          destruct n0; [|lia].
          pose (MCList.nth_error_spec (ind_bodies mind) n).
          pose proof (Heq' := Heq). 
          rewrite CoqType_to_camlType'_length in Heq.    
          destruct n0; [|lia]. cbn. 
          eapply IHstep with (kn:=kn) in H2; eauto; cbn.  
          destruct H2 as [vy [? Hvy]]. 
          eexists (EAst.tConstruct (mkInd kn ind) k' (vy :: lv')); cbn; split.
          2: { rewrite compile_unfold_eq. simpl. 
          unfold lookup_constructor_args. rewrite Hlookup.
          assert (is_true (@firstorder_oneind Σb mind x)).
          { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          assert (is_true (@firstorder_oneind Σb mind x0)).
          { clear -e0 Hfo. eapply forallb_nth_error in Hfo; erewrite e0 in Hfo. exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth; try eapply e; eauto.
          cbn in Hlookup. rewrite ReflectEq.eqb_refl in Hlookup.
          unshelve erewrite filter_length_not_nil with (mind:=mind) (ind:=ind); eauto.
          2: { fold Emind. destruct (nth_error (EAst.ind_bodies Emind) ind); now inversion Hlookup. }
          unshelve erewrite CoqType_to_camlType'_nth; try eapply e; eauto.
          econstructor.
          - econstructor.
            + exact Hvy.
            + apply Forall2_acc_cst. 
              rewrite MCList.map_InP_spec.
              rewrite <- (map_id l'). apply Forall2_map. 
              exact Hlv'.
          - cbn. apply Forall2_length in H4. rewrite <- H4.
          assert (is_true (@firstorder_oneind Σb mind x)).
          { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth with (x:=x) in HTs ; eauto.  
          unfold CoqType_to_camlType_oneind in HTs.
          destruct x, MCProd.andb_and, (a _).
          apply In_nth_error in HTs.
          destruct HTs as [j HTs].
          apply CoqType_to_camlType_ind_ctors_nth in HTs.
          destruct HTs as [? [? [? HTs]]].
          apply f_equal with (f := @List.length _) in HTs. 
          rewrite CoqType_to_camlType_ind_ctors_length in HTs.
          cbn in HTs. rewrite Hparam in HTs.
          rewrite rev_length app_length in HTs. cbn in HTs.    
          rewrite HTs. rewrite <- plus_n_O.
          unshelve eapply ctors_max_length; try eapply e; eauto.
          }
          2: { cbn. rewrite ReflectEq.eqb_refl.
          unfold ErasureFunction.erase_mutual_inductive_body.
          rewrite nth_error_map e0. reflexivity. }
          pose (MCList.nth_error_spec (ind_ctors x) k').
          destruct n0; intros; eauto.
          ++ sq. econstructor 2; eauto. cbn.
          rewrite ReflectEq.eqb_refl.
          unfold Emind. cbn. rewrite nth_error_map. 
          rewrite e. cbn. rewrite nth_error_map. rewrite e1. cbn.
          reflexivity.
          cbn; rewrite Hnparam; cbn.
          destruct Hwit as [a' [? [? ?]]].
          assert (is_true (@firstorder_oneind Σb mind x)).
          { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          apply Forall2_length in Hlv'. rewrite Hlv'.
          apply Forall2_length in Hv'. cbn in Hv'.
          inversion Hv'.
          rewrite Nat.sub_0_r in HTs'. rewrite H3 in HTs'.    
          unshelve erewrite CoqType_to_camlType'_nth with (x:=x) in H2; eauto.
          unfold CoqType_to_camlType_oneind in H2.
          destruct x. destruct MCProd.andb_and. destruct (a _).
          apply CoqType_to_camlType_ind_ctors_nth in H2.
          destruct H2 as [a0 [? [? ?]]].
          cbn in *.
          rewrite e1 in H2. inversion H2. destruct H10. clear H2.
          cbn in *.
          rewrite cstr_arity_length.
          apply f_equal with (f := @List.length _) in H7.
          rewrite CoqType_to_camlType_ind_ctors_length in H7.
          rewrite rev_length in H7. cbn in H3. rewrite app_length in H7.
          rewrite Hparam in H7. cbn in H7. rewrite <- plus_n_O in H7.
          rewrite <- H7. now inversion HTs'.
          ++ assert (is_true (@firstorder_oneind Σb mind x)). 
        { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth with (x:=x) in Hk'; eauto.
          rewrite CoqType_to_camlType_oneind_length in Hk'.
          lia. 
        * inversion H2.  
  Qed.
  
  From Malfunction Require Import CompileCorrect.

  Definition CoqValue_to_CamlValue `{WcbvFlags} 
  (cf:=config.extraction_checker_flags) {guard : abstract_guard_impl}
  (Σ:reference_impl_ext) kn mind Eind 
  {normal_in : forall Σ_ : global_env_ext,
  wf_ext Σ_ -> Σ_ ∼_ext Σ -> PCUICSN.NormalizationIn Σ_}
(retro : Retroknowledge.t)
(Hparam : ind_params mind = [])
(Hnparam : ind_npars mind = 0)
(Hfo : is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind))) ind univ v u t vErase' :
let adt := CoqType_to_camlType mind Hparam Hfo in
let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
let Σ' := [(kn , EAst.InductiveDecl Emind)] in
let global_adt := add_ADT CanonicalHeap [] [] kn adt in 
Σ.(reference_impl_env_ext) = (mk_global_env univ [(kn , InductiveDecl mind)] retro ,Monomorphic_ctx) ->
with_constructor_as_block = true ->
ind < List.length (snd adt) ->
EGlobalEnv.lookup_inductive Σ' (mkInd kn ind) = Some (Emind, Eind) ->
forall (wt : Σ ;;; [] |- t : tInd (mkInd kn ind) u)
(wv : Σ ;;; [] |- v : tInd (mkInd kn ind) u),  
let tErase := ErasureFunction.erase (normalization_in := normal_in) canonical_abstract_env_impl Σ [] t 
(fun Σ' e => match (eq_sym e) in (_ = ΣΣ) return welltyped ΣΣ [] t with eq_refl => iswelltyped wt end) in 
let vErase := ErasureFunction.erase (normalization_in := normal_in) canonical_abstract_env_impl Σ [] v 
(fun Σ' e => match (eq_sym e) in (_ = ΣΣ) return welltyped ΣΣ [] v with eq_refl => iswelltyped wv end) in 
PCUICWcbvEval.eval Σ t v ->
EWcbvEval.eval Σ' tErase vErase ->
represents_value vErase' vErase ->
eval [] (fun _ => not_evaluated) empty_heap
    (compile Σ' tErase)
    empty_heap (compile_value Σ' vErase') ->
realize_val CanonicalHeap [] []
            global_adt (Adt kn (int_of_nat ind) []) (compile_value Σ' vErase').
Proof.
  intros. cbn. rewrite ReflectEq.eqb_refl.
  rewrite int_to_of_nat. admit.
  pose proof (X':=X).
  eapply @PCUICClassification.eval_classification with (args := []) in X; eauto.
  destruct v; try solve [inversion X]; cbn in X.   
  admit.
  (*cbn in vErase.
  admit. 
  induction vErase'.      
  3: { destruct args; unfold compile_value. unfold lookup_constructor_args.
       cbn.  ErasureFunction.erase_correct_firstorder } 
    EWcbvEval.eval
  EWcbvEvalNamed.eval Σ Γ s t
  SemanticsSpec.eval Σ' Γ' h (compile Σ s) h (compile_value Σ t).
*)
Abort.
  Definition CoqFunction_to_CamlFunction `{WcbvFlags} 
    (cf:=config.extraction_checker_flags) {guard : abstract_guard_impl}
    (Σ:reference_impl_ext) kn mind Eind 
    {normal_in : forall Σ_ : global_env_ext,
    wf_ext Σ_ -> Σ_ ∼_ext Σ -> PCUICSN.NormalizationIn Σ_}
  (retro : Retroknowledge.t)
  (Hparam : ind_params mind = [])
  (Hnparam : ind_npars mind = 0)
  (Hfo : is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind))) ind univ v u f na:
  let adt := CoqType_to_camlType mind Hparam Hfo in
  let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
  let Σ' := [(kn , EAst.InductiveDecl Emind)] in
  let global_adt := add_ADT CanonicalHeap [] [] kn adt in 
  Σ.(reference_impl_env_ext) = (mk_global_env univ [(kn , InductiveDecl mind)] retro ,Monomorphic_ctx) ->
  with_constructor_as_block = true ->
  ind < List.length (snd adt) ->
  EGlobalEnv.lookup_inductive Σ' (mkInd kn ind) = Some (Emind, Eind) ->
  forall (wt : Σ ;;; [] |- f : tProd na (tInd (mkInd kn ind) u) (tInd (mkInd kn ind) u)),  
  eval [] (fun _ => not_evaluated) empty_heap
      ((compile Σ' (ErasureFunction.erase (normalization_in := normal_in) canonical_abstract_env_impl Σ [] f 
          (fun Σ' e => match (eq_sym e) in (_ = ΣΣ) return welltyped ΣΣ [] f with eq_refl => iswelltyped wt end))))
      empty_heap v ->
  realize_val CanonicalHeap [] []
              global_adt (Arrow (Adt kn (int_of_nat ind) []) (Adt kn (int_of_nat ind) [])) v.
Proof.
  intros. cbn. rewrite ReflectEq.eqb_refl. cbn.

  do 3 eexists. split; intros. 
  2: {
    rewrite int_to_of_nat; [admit|].
    eapply camlValue_to_CoqValue_nil in H5; eauto; cbn.
    2: { rewrite int_to_of_nat. admit. eauto. }
    2: { rewrite ReflectEq.eqb_refl. rewrite int_to_of_nat. admit.
        cbn. rewrite nth_error_map. admit. }
    destruct H5 as [? [? ?]].
         
    }   

    } 


  Existing Instance config.extraction_checker_flags.



  Definition camlValue_to_CoqValue_gen `{WcbvFlags}  
    Σ kn mind Eind 
    (Hparam : ind_params mind = [])
    (Hnparam : ind_npars mind = 0)
    (Hfo : is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind))) ind v :
    let adt := CoqType_to_camlType mind Hparam Hfo in
    let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
    with_constructor_as_block = true ->
    ind < List.length (snd adt) ->
    EGlobalEnv.lookup_inductive Σ (mkInd kn ind) = Some (Emind, Eind) ->
    realize_ADT CanonicalHeap [] [] adt [] All_nil ind v ->
    exists t, ∥ EWcbvEval.value Σ t ∥ /\ 
    eval CanonicalHeap [] (fun _ => not_evaluated) empty_heap (compile Σ t) empty_heap v.
  Proof.
    induction Σ; cbn; intros.
    - cbn in H3. inversion H2.
    - destruct a. cbn in *.     
      destruct ReflectEq.eqb.
      2: { eapply IHΣ. ; eauto.  }   

  Definition camlValue_to_CoqValue `{WcbvFlags} Σ global_adt kn mind (Hparam : ind_params mind = [])
      (Hfo : is_true (forallb (@firstorder_oneind Σb mind) (ind_bodies mind))) ind v :
      let adt := CoqType_to_camlType mind Hparam Hfo in
      let Emind := ErasureFunction.erase_mutual_inductive_body mind in 
      let Σ' := (kn , EAst.InductiveDecl Emind) :: Σ in
      with_constructor_as_block = false ->
      ind < List.length (snd adt) ->
      realize_ADT CanonicalHeap [] global_adt adt [] All_nil ind v ->
      exists t, ∥ EWcbvEval.value Σ' t ∥ /\ 
      eval CanonicalHeap [] (fun _ => not_evaluated) empty_heap (compile Σ' t) empty_heap v.
    Proof.
      revert v kn mind Hparam Hfo ind. induction global_adt.
      [intros; eapply camlValue_to_CoqValue_nil; eauto|].
      { cbn.  }
      intros v kn mind Eind Hparam Hfo ind adt Emind Hflag Hind [step Hrel] Hlookup.
      revert v kn mind Eind Hparam Hfo ind adt Emind Hflag Hind Hrel Hlookup. 
      induction step; intros; [inversion Hrel|].
      unfold realize_ADT_gen in Hrel. 
      apply leb_correct in Hind. simpl in Hrel, Hind. 
      unfold Nat.ltb in Hrel. rewrite Hind in Hrel.
      destruct Hrel as [Hrel | Hrel].
      - apply Existsi_spec in Hrel as [k [Hk [HkS Hrel]]]. cbn in HkS.
        destruct (filter_firstn _ _ _ _ HkS) as [k' [Hk' Hfilter]].
        eexists (EAst.tConstruct (mkInd kn ind) k' []); cbn; split.
        + repeat econstructor. cbn. rewrite Hflag. apply MCProd.andb_and; split; eauto.
          apply lookup_inductive_env in Hlookup. rewrite Hlookup.
          pose (MCList.nth_error_spec (EAst.ind_bodies Emind) ind).
          destruct n.
          pose (MCList.nth_error_spec (EAst.ind_ctors x) k').
          destruct n; eauto.  admit. admit. 
        + rewrite compile_unfold_eq. simpl. 
          unfold lookup_constructor_args. rewrite Hlookup.
          subst. unfold EAst.cstr_nargs. admit.
      - apply Existsi_spec_gen in Hrel as [k [Ts [Hk [HkS [Hrel HTs]]]]]. cbn in HkS.
        destruct (filter_firstn _ _ _ _ HkS) as [k' [Hk' Hfilter]].
        destruct Hrel as [v' [eq Hv']].

  
      pose (map ).
      eexists (EAst.tConstruct (mkInd kn ind) k' v'); cbn; split.
      + repeat econstructor. cbn. rewrite Hflag. apply MCProd.andb_and; split; eauto.
        apply lookup_inductive_env in Hlookup. rewrite Hlookup.
        pose (MCList.nth_error_spec (EAst.ind_bodies Emind) ind).
        destruct n.
        pose (MCList.nth_error_spec (EAst.ind_ctors x) k').
        destruct n; eauto.  admit. admit. 
      + rewrite compile_unfold_eq. simpl. 
        unfold lookup_constructor_args. rewrite Hlookup.
        subst. unfold EAst.cstr_nargs. admit.
    
    
  
    destruct 
    destruct mind.   ind_bodies0; [inversion Hind|].
    simpl in Hrel. unfold Nat.ltb in Hrel. rewrite Hind in Hrel.
    - set (filter _ _) in Hrel. remember l.
      apply Existsi_spec in Hrel as [k [Hk [Hk' Hrel]]]. cbn in Hk'.   
      eexists (EAst.tConstruct (mkInd kn ind) k []); cbn; split.
      + repeat econstructor. cbn. admit.
      + subst. rewrite compile_unfold_eq. simpl. 
        unfold lookup_constructor_args. rewrite Hlookup. econstructor.
      + admit.
    -      
          apply eval_num_int. econstructor.    
          unfold EGlobalEnv.lookup_env in Hlookup. 

    2: { unfold firstorder_oneind in Hfo. apply MCProd.andb_and in Hfo. } 
      unfold CoqType_to_camlType in adt. 

End firstorder.

