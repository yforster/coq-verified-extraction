Require Import ssreflect ssrbool Eqdep_dec.
From Equations Require Import Equations. 
From MetaCoq.Utils Require Import All_Forall MCSquash MCList.
From MetaCoq.Common Require Import Transform config Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICFirstorder PCUICCasesHelper BDStrengthening.
From MetaCoq.Erasure Require Import EWcbvEval EWcbvEvalNamed.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.

From Malfunction Require Import Malfunction SemanticsSpec utils_array Compile.

Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.
From MetaCoq.Utils Require Import bytestring.

Print nat_rect.

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

  Open Scope bs. 

  Definition empty_locals : Ident.Map.t := fun _ => fail "not_defined".

  Close Scope bs. 

  Section Values. 

    Variable local_adt : list (value -> Prop).
    Variable global_adt : global_adt_decl.

    Definition to_realize_term (realize_val : value -> Prop) 
      : t -> Prop := fun t => forall h h' v, 
      eval _ globals empty_locals h t h' v -> realize_val v.

    Definition to_realize_value (realize_term : t -> Prop) 
      : value -> Prop := fun v => exists t h h', 
        eval _ globals empty_locals h t h' v /\ realize_term t.

    Definition realize_term (A:camlType) : t -> Prop.
    Proof.
      refine (camlType_rect _ _ _ _ A); clear A.
      - intros A PA B PB.
        exact (fun f => forall t, PA t -> PB (Mapply(f,[t]))).
      - intros n. 
        exact (to_realize_term (List.nth n local_adt (fun _ => False))).
      - intros kn n params PAll.
        case (find (fun '(kn',_) => eq_kername kn kn') global_adt).
        + intros [_ Hrel]. 
          refine (to_realize_term (Hrel params _ (int_to_nat n))).
          induction PAll; econstructor; eauto. eapply to_realize_value; eassumption.
        + intros; exact False. 
    Defined.

    Definition realize_value (A:camlType) : value -> Prop :=
      to_realize_value (realize_term A).

  End Values. 
  MetaCoq Quote Recursively Definition tnat := nat.

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
      refine (Forall2 (realize_value _ global_adt) Ts vs).
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
    is_true (@firstorder_type Σb n k decl_type) -> camlType.
  Proof.
    unfold firstorder_type. destruct (fst _).
    all: try solve [inversion 1].
    (* case of tRel with a valid index *)
    - intro; exact (Rel (n - S (n0-k))).  (* n0 - k *)  
    (* case of tInd where Σb is saying that inductive_mind is first order *)
    - intro; destruct ind. exact (Adt inductive_mind (int_of_nat inductive_ind) []).
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
    - cbn in H. apply MCProd.andb_and in H. destruct H. 
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
    #|CoqType_to_camlType_fix
        ind_bodies0 ind_finite0
        ind_params0 ind_npars0
        ind_universes0 ind_variance0
        Hparam ind_bodies1 Hfo| =
    #|ind_bodies0|); eauto.
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
                  
  Fixpoint zip {A B} (l:list A) (l':list B) : list (A * B) :=
  match l , l' with 
  | [] , [] => []
  | a::l , b::l' => ((a,b) :: zip l l')
  | _ , _ => [] 
  end. 
    
  Lemma zip_length {A B} (l:list A) (l':list B) : 
    #|l| = #|l'| ->  #|zip l l'| = #|l|.
  Proof. 
    revert l'; induction l; destruct l'; cbn; eauto.
    intro Heq; inversion Heq. rewrite IHl; eauto.  
  Qed. 

  Lemma zip_fst {A B} (l:list A) (l':list B) : 
    #|l| = #|l'| -> map fst (zip l l') = l.
  revert l'; induction l; destruct l'; cbn; eauto.
  - inversion 1.
  - intro Heq; inversion Heq. rewrite IHl; eauto.
  Qed.         

  Lemma zip_snd {A B} (l:list A) (l':list B) : 
  #|l| = #|l'| -> map snd (zip l l') = l'.
  revert l'; induction l; destruct l'; cbn; eauto.
  - inversion 1.  
  - intro Heq; inversion Heq. rewrite IHl; eauto.
  Qed.  

  Fixpoint All_exists T U A P l l'
    (H: Forall2 (fun (t : T) (u : U) => exists a : A, P t u a) l l')  
    : exists l'' : list A, Forall2 (fun tu a => P (fst tu) (snd tu) a) (zip l l') l''.
  Proof. 
    destruct H.
    - exists []. econstructor.
    - destruct H as [p H].
      refine (let '(ex_intro l' X) := 
              All_exists T U A P _ _ H0 in _).
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
    a = CoqType_to_camlType_ind_ctor 0 #|ind_bodies mind| (rev (cstr_args a' ++ ind_params mind)) i'.
  Proof. 
    revert a k i.
    induction ind_ctors; cbn; intros.
    - destruct k; inversion H.
    - destruct MCProd.andb_and. destruct (a1 _).
      destruct k; destruct a.
      + inversion H. eexists; split; [reflexivity|].
        cbn. unfold firstorder_con in i. cbn in i.
        apply MCProd.andb_and in i. destruct i as [i ?]. 
        exists i. repeat f_equal. apply bool_irr.
      + eapply IHind_ctors; eauto.
  Qed. 

  Lemma CoqType_to_camlType_ind_ctors_length 
  l n m i:
  List.length (CoqType_to_camlType_ind_ctor n m l i) = List.length l.
  revert n m i. induction l; cbn; eauto; intros. 
  destruct MCProd.andb_and. destruct (a0 _). destruct a.
  cbn. now f_equal.
  Qed. 

  Lemma CoqType_to_camlType_ind_ctor_app
  l l' n m i : { i' & { i'' &  CoqType_to_camlType_ind_ctor n m (l++l') i = CoqType_to_camlType_ind_ctor n m l i' ++ CoqType_to_camlType_ind_ctor (#|l| + n) m l' i''}}.
  pose proof (ii := i). rewrite alli_app in ii. eapply MCProd.andb_and in ii. destruct ii as [i' i''].
  exists i', i''. revert n i i' i''. induction l; cbn in *; intros.  
  - f_equal. eapply bool_irr.
  - destruct MCProd.andb_and. destruct (a0 _). destruct a.      
    destruct MCProd.andb_and. destruct (a _). rewrite <- app_comm_cons; repeat f_equal.
    * apply bool_irr.
    * assert (S (#|l| + n) = #|l| + S n) by lia. revert i''. rewrite H. apply IHl.
  Qed.      
    
  Lemma CoqType_to_camlType_oneind_nth mind Hparam x Hfo k l :
  nth_error (CoqType_to_camlType_oneind mind x Hparam Hfo) k = Some l
  -> exists l', nth_error (ind_ctors x) k = Some l' /\ #|l| = #|cstr_args l'|.
  Proof.
    destruct x; cbn. destruct MCProd.andb_and.
    destruct (a Hfo). clear.
    revert k l. induction ind_ctors0; cbn; eauto.
    - intros k l H. rewrite nth_error_nil in H. inversion H.
    - destruct MCProd.andb_and. destruct (a0 i0).
      destruct a. intros k l H. destruct k; cbn. 
      + eexists; split; [reflexivity |]. cbn in *.
        inversion H. rewrite CoqType_to_camlType_ind_ctors_length.
        rewrite Hparam. rewrite app_nil_r. apply rev_length.
      + cbn in *. now eapply IHind_ctors0. 
  Qed. 

  Lemma Forall_Forall2_and_inv {A B : Type} 
    {R : A -> B -> Prop} {P : A -> Prop} l l':
  Forall2 (fun (x : A) (y : B) => P x /\ R x y ) l l' ->
  Forall2 R l l' /\ Forall P l.
  Proof. 
    induction 1; repeat econstructor; now eauto.
  Qed.

  Lemma Forall2_forall {A B X: Type} 
    {R : A -> B -> X -> Prop} l l':
  Forall2 (fun a b => forall x, R a b x) l l' ->
  forall x, Forall2 (fun a b => R a b x) l l'.
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Axiom ctors_max_length : forall mind j k ind ctors,
    nth_error mind j = Some ind ->
    nth_error (ind_ctors ind) k = Some ctors -> 
    #|cstr_args ctors| < int_to_nat max_length.
  Axiom ind_ctors_wB : forall mind j ind,
    nth_error mind j = Some ind ->
    #|ind_ctors ind| <= Z.to_nat Uint63.wB.
  Axiom ind_wB : forall mind retro kn univ (cf:=config.extraction_checker_flags),
    let Σ := mk_global_env univ [(kn , InductiveDecl mind)] retro in
    PCUICTyping.wf Σ ->
    #|ind_bodies mind| <= Z.to_nat Uint63.wB.

  Axiom compile_pipeline : global_declarations -> term -> t.

  Definition cstr_nargs : constructor_body -> nat := fun c => #| cstr_args c|.

  Definition lookup_constructor_args Σ ind : option (list nat) 
    := match lookup_inductive Σ ind with
    | Some (_, idecl) => Some (map cstr_nargs (ind_ctors idecl))
   | None => None
    end.

  Axiom compile_pipeline_tConstruct_nil : forall Σ i n inst, 
    compile_pipeline Σ.(declarations) (tConstruct i n inst) = 
    match lookup_constructor_args Σ i with
    | Some num_args =>
      Mnum (numconst_Int (int_of_nat (nonblocks_until n num_args)))
    | None => Mstring "error: inductive not found"
    end.

  Axiom compile_pipeline_tConstruct_cons : forall Σ i n inst l, 
    #|l| > 0 ->
    compile_pipeline Σ.(declarations) (mkApps (tConstruct i n inst) l) =
    match lookup_constructor_args Σ i with
    | Some num_args =>
      Mblock
        (int_of_nat (blocks_until n num_args),
         map_InP l (fun (x : term) (_ : In x l) => compile_pipeline Σ.(declarations) x))
    | None => Mstring "error: inductive not found"
    end.


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
    - destruct Eind; cbn. destruct MCProd.andb_and. destruct (a _).
      rewrite (filter_ext _ (fun x =>
      match #|x| with
      | 0 => true
      | S _ => false
      end)).
      { clear. intro l; induction l; eauto. }
      revert k i0. clear Hind i i1 a. induction ind_ctors0; cbn; intros. 
      + intros. now repeat rewrite firstn_nil.
      + destruct k; eauto; cbn. destruct MCProd.andb_and. destruct (a0 _). cbn.
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
    - destruct Eind; cbn. destruct MCProd.andb_and. destruct (a _).
      rewrite (filter_ext _ (fun x =>
      match #|x| with
      | 0 => false
      | S _ => true
      end)).
      { clear. intro l; induction l; eauto. }
      revert k i0. clear Hind i i1 a. induction ind_ctors0; cbn; intros. 
      + intros. now repeat rewrite firstn_nil.
      + destruct k; eauto; cbn. destruct MCProd.andb_and. destruct (a0 _). cbn.
        destruct a. cbn. rewrite CoqType_to_camlType_ind_ctors_length.
        revert i1. cbn. rewrite Hparam app_nil_r. cbn.
        rewrite rev_length. intro.  
        destruct cstr_args0; cbn. 
        * eapply IHind_ctors0.
        * intros; f_equal. eapply IHind_ctors0; eauto.
    - now eapply nth_error_Some_length. 
  Qed. 

  Lemma Forall2_map_left {A B C} (P : A -> B -> Prop) (f : C -> A) (l : list C) (l' : list B) :
    Forall2 P (map f l) l' <-> Forall2 (fun x y => P (f x) y) l l'.
Proof.
  split; intros.
  + eapply Forall2_map_inv. now rewrite map_id.
  + rewrite -(map_id l'). now eapply Forall2_map.
Qed.

End firstorder.

Lemma CoqType_to_camlType_oneind_type_Rel n k decl_type Hfo :
let T := CoqType_to_camlType_oneind_type (Σb := []) n k decl_type Hfo in
exists i,  (k <= i) /\ (i < n + k) /\ T = Rel (n - S (i-k)).
Proof.
unfold CoqType_to_camlType_oneind_type.
unfold firstorder_type in Hfo.
set (fst (PCUICAstUtils.decompose_app decl_type)) in *.
destruct t; inversion Hfo; cbn; eauto.
- apply MCProd.andb_and in H0. destruct H0. apply leb_complete in H, H0.
  exists n0; repeat split; eauto.
- destruct ind. inversion Hfo.
Qed.   

Lemma CoqType_to_camlType_oneind_Rel mind ind Hparam Hfo larg T k : 
In larg (CoqType_to_camlType_oneind (Σb := []) mind ind Hparam Hfo) ->
nth_error larg k = Some T -> exists i, (k <= i) /\ (i < #|ind_bodies mind| + k) /\ T = Rel (#|ind_bodies mind| - S (i-k)).
Proof. 
destruct mind, ind. revert k Hfo. induction ind_ctors0; intros k Hfo Hlarg HT.
- cbn in *; destruct MCProd.andb_and. destruct (a Hfo). destruct (in_nil Hlarg).
- cbn; cbn in Hlarg. destruct MCProd.andb_and. cbn in Hfo. destruct (a0 Hfo). 
  destruct MCProd.andb_and. destruct (a1 i0). destruct a.
  unfold In in Hlarg. destruct Hlarg.
  2: { eapply IHind_ctors0; eauto. cbn. destruct MCProd.andb_and.
        destruct (a _). rewrite (bool_irr _ i6 i4). eauto.
        Unshelve.
        cbn. apply MCProd.andb_and. split; cbn; eauto. }
  cbn in Hparam, i3. rewrite Hparam in i3, H. rewrite app_nil_r in i3, H.
  clear - i3 HT H. set (rev cstr_args0) in *. rewrite <- H in HT.
  pose proof (nth_error_Some_length HT).
  revert T HT. clear H H0. cbn; set (#|ind_bodies0|) in *. 
  setoid_rewrite <- (Nat.sub_0_r k) at 1. assert (k >= 0) by lia. revert H.  
  revert k i3. generalize 0 at 1 2 3 4.
  induction l; cbn; intros. 1: { rewrite nth_error_nil in HT. inversion HT. }
  destruct MCProd.andb_and. destruct (a0 i3). destruct a.
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
  - destruct MCProd.andb_and. destruct (a0 Hfo). destruct H.
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

Inductive Forall2i {A B : Type} (R : nat -> A -> B -> Prop) (n : nat)
  : list A -> list B -> Prop :=
| Forall2i_nil : Forall2i R n [] []
| Forall2i_cons :
    forall x y l r,
      R n x y ->
      Forall2i R (S n) l r ->
      Forall2i R n (x :: l) (y :: r).
Arguments Forall2i_nil {_ _ _ _}.
Arguments Forall2i_cons {_ _ _ _ _ _ _ _}.

Derive Signature NoConfusionHom for All2i.

Lemma Forall2_Forall_mix {A B} {P : B -> Prop} {Q : A -> B -> Prop}
   {l : list A} {l' : list B} :
  Forall2 (fun x y => (P y -> Q x y)) l l' -> Forall P l' -> Forall2 Q l l'.
Proof.
  induction 1; simpl; intros; constructor; inversion H1; eauto.
Qed.

  Lemma Forall2_and_inv {A B : Type} (R R' : A -> B -> Prop) (l : list A) (l' : list B) :
    Forall2 (fun (x : A) (y : B) => R x y /\ R' x y) l l'
    -> Forall2 R l l' /\ Forall2 R' l l'.
  Proof.
    induction 1; split; eauto; econstructor; destruct H; now destruct IHForall2.
  Qed.

  Inductive nonDepProd : term -> Type :=
    | nonDepProd_tInd : forall i u, nonDepProd (tInd i u)
    | nonDepProd_Prod : forall na A B, closed A -> nonDepProd B -> nonDepProd (tProd na A B).

  Axiom todo : forall A, A.

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
  
  Lemma strengthening_type `{cf: checker_flags} {Σ : global_env_ext} {wfΣ : PCUICTyping.wf Σ} Γ Γ' Γ'' t s :
    Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |- lift #|Γ'| #|Γ''| t : tSort s -> 
    { s' & Σ ;;; Γ ,,, Γ'' |- t : tSort s'}.
  Admitted. 

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
    edestruct s0 as [s' Hs]. cbn.  rewrite PCUICLiftSubst.lift_closed; eauto.
    econstructor; try reflexivity; eauto.
    + eexists; eauto.
    + rewrite /subst1 PCUICClosed.subst_closedn; eauto.
  Qed.      

  Lemma firstorder_type_closed kn l k T :
    firstorder_type (Σb := []) #|ind_bodies l| k T -> closed (subst (inds kn [] (ind_bodies l)) k T@[[]]).
  Proof. 
    destruct T; try solve [inversion 1]; cbn in *; eauto.  
    - intro H; apply MCProd.andb_and in H. destruct H. rewrite H.
      eapply leb_complete in H, H0. rewrite nth_error_inds; [lia|eauto].
    - apply todo. (* application *)  
  Qed. 

  Lemma firstorder_nonDepProd mind kn Eind cstr_args0 x lind ind :
  nth_error (ind_bodies mind) ind = Some Eind ->
  is_assumption_context cstr_args0 ->
  let Ts := CoqType_to_camlType_ind_ctor (Σb := []) 0 #|ind_bodies mind| (rev cstr_args0) x in 
  All2 (fun a b => 0 <= a /\ a < #|ind_bodies mind| /\ b = Rel (#|ind_bodies mind| - S a)) lind Ts -> 
  { nd : nonDepProd (subst0 (inds kn [] (ind_bodies mind))
                     (it_mkProd_or_LetIn cstr_args0 (tRel (#|ind_bodies mind| - S ind + #|cstr_args0|)))@[[]]) &
  (fst (nonDep_decompose _ nd) = map (fun b : nat => tInd {| inductive_mind := kn; inductive_ind := #|ind_bodies mind| - S b |} []) lind) /\
  (snd (nonDep_decompose _ nd) = tInd {| inductive_mind := kn; inductive_ind := ind |} []) }.
Proof.
    intros Hind Hlets. 
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
    destruct a. destruct decl_body.
    + inversion Hlets.
    + destruct HX as [ndX [Xfst Xsnd]]. cbn. 
      unshelve econstructor. econstructor; eauto.
      { clear - x1. cbn in *. apply MCProd.andb_and in x1; destruct x1 as [x1 _].
        rewrite <- plus_n_O in x1. rewrite rev_length in x1. now apply firstorder_type_closed. 
      }
      split; eauto.
      rewrite map_app. cbn. set (subst _ _ _). set (fst _). change (t :: y) with ([t]++y). f_equal; eauto. 
      unfold t. cbn in Ha. destruct MCProd.andb_and. destruct (a _). clear a i i1.
      destruct decl_type; inversion i0.
      * cbn. revert i0 Ha. rewrite rev_length. cbn.  intros. apply MCProd.andb_and in i0. destruct i0. rewrite <- plus_n_O in H.
        inversion Ha. subst. apply All2_length in X0. apply length_nil in X0. subst. clear Ha. 
        rewrite H. rewrite nth_error_inds. { apply leb_complete in H1. lia. } 
        cbn. repeat f_equal; eauto. destruct H4 as [? [? ?]]. inversion H4. 
        apply leb_complete in H1. lia.   
      * cbn in *. (* application case, not possible *) apply todo.
      * cbn in H0. destruct ind0. inversion H0.
  Qed. 


  Lemma camlValue_to_CoqValue_nil `{Heap} `{WcbvFlags} (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind
    (Hparam : ind_params mind = [])
    (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
    (Hnparam : ind_npars mind = 0)
    (Hmono : ind_universes mind = Monomorphic_ctx)
    (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) :
    let adt := CoqType_to_camlType mind Hparam Hfo in
    let Σ := mk_global_env univ [(kn , InductiveDecl mind)] retro in
    PCUICTyping.wf Σ ->
    with_constructor_as_block = true ->
    forall v ind Eind, 
    ind < List.length (snd adt) ->
    lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
    realize_ADT _ [] [] adt [] All_nil ind v ->
    exists t, forall h,  
    ∥ (Σ , univ_decl) ;;; [] |- t : tInd (mkInd kn ind) [] ∥ /\ 
    eval _ [] (empty_locals _) h (compile_pipeline Σ.(declarations) t) h v.
  Proof. 
    rename H into HHeap; rename H0 into H. 
    intros adt Σ wfΣ Hflag v ind Eind Hind Hlookup [step Hrel].
    revert kn mind Hparam Hindices Hnparam Hmono Hfo v ind Eind adt Σ wfΣ Hflag Hind Hlookup Hrel. 
    induction step; intros;  [inversion Hrel|].
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
          unshelve epose proof (Htyp := type_Construct (Σ, univ_decl) [] (mkInd kn ind) k' [] mind x x0 _ _ _).
          ** econstructor.
          ** unfold declared_constructor, declared_inductive. now cbn.
          ** unfold consistent_instance_ext, consistent_instance; cbn.
             now rewrite Hmono.
          ** 
          assert (is_true (@firstorder_oneind [] mind x)).
          { clear -e Hfo; eapply forallb_nth_error in Hfo; erewrite e in Hfo; exact Hfo. }
          unshelve erewrite CoqType_to_camlType'_nth in Hfilter, Ha, Ha'; eauto.
          unfold CoqType_to_camlType_oneind in Hfilter, Ha, Ha'. destruct x. cbn in *. 
          destruct MCProd.andb_and. destruct (a _).
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
      + pose proof (HTs' := HTs). apply filter_nth_error in HTs. destruct HTs as [HTs _].
        subst.
        assert (Forall2 (fun v T => 
        (exists t, forall h,  ∥ (Σ , univ_decl) ;;; [] |- fst t : tInd (mkInd kn (#|ind_bodies mind| - S (snd t))) [] ∥ /\ 
        eval _ [] (empty_locals _) h (compile_pipeline Σ.(declarations) (fst t)) h v
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
        apply Forall_All in Hvallv'.
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
            erewrite <- (Forall2_map_right (fun a b =>
            eval HHeap [] (empty_locals HHeap) h
              (compile_pipeline [(kn, InductiveDecl mind)]
                 (fst a)) h b) fst) in Heval.
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
        destruct MCProd.andb_and. destruct (a _).  
        apply CoqType_to_camlType_ind_ctors_nth in HTs''.
        destruct HTs'' as [a0 [? [? ?]]]. rewrite Nat.sub_0_r in HTs'. rewrite HTs' in Hfilter. 
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
          rewrite <- Hndsnd. eapply nonDep_typing_spine with (s:=sctype) ; eauto. 
          { revert Hctype; intro. unfold type_of_constructor in Hctype. cbn in Hctype.
            erewrite cstr_eq in Hctype; eauto. rewrite Hparam in Hctype. cbn in Hctype. 
            unfold cstr_concl, cstr_concl_head in Hctype. rewrite Hparam Hcstr_indices app_nil_r in Hctype.
            cbn in Hctype. rewrite <- plus_n_O in Hctype; eauto. }
          rewrite Hndfst. now apply All2_map_right.
  Qed.
  
  Definition CoqValue_to_CamlValue `{Heap} `{WcbvFlags} (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind
    (Hparam : ind_params mind = [])
    (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
    (Hnparam : ind_npars mind = 0)
    (Hmono : ind_universes mind = Monomorphic_ctx)
    (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) :
    let adt := CoqType_to_camlType mind Hparam Hfo in
    let Σ := mk_global_env univ [(kn , InductiveDecl mind)] retro in
    PCUICTyping.wf Σ ->
    with_constructor_as_block = true ->
    forall t ind Eind, 
    ind < List.length (snd adt) ->
    lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
    ∥ (Σ , univ_decl) ;;; [] |- t : tInd (mkInd kn ind) [] ∥ ->
    forall h v, 
      eval _ [] (empty_locals _) h (compile_pipeline Σ.(declarations) t) h v
      -> realize_ADT _ [] [] adt [] All_nil ind v.
  Proof.
  Admitted.  

  From Malfunction Require Import CompileCorrect Pipeline.

  Section fix_global.

  Variable Σ : list Ident.t.

  Fixpoint isPure (t : t) :=
    match t with
    | Mvar x => true
    | Mlambda (ids, x) => isPure x
    | Mapply (x, args) => isPure x && forallb isPure args
    | Mlet (binds, x) => forallb isPure_binding binds && isPure x
    | Mnum x => true
    | Mstring x => false (* strings are interpreted using vectors *)
    | Mglobal id => true
    | Mswitch (x, sels) => isPure x && forallb (fun '(_, x) => isPure x) sels
    | Mnumop1 (op, num, x) => isPure x
    | Mnumop2 (op, num, x1, x2) => isPure x1 && isPure x2
    | Mconvert (from, to, x) => isPure x
    | Mblock (tag, xs) => forallb isPure xs
    | Mfield (i, x) => isPure x
    | _ => false
    end
  with isPure_binding (b : binding) :=
         match b with
         | Unnamed x => isPure x
         | Named (id, x) => isPure x
         | Recursive recs => forallb (fun '(id,x) => isPure x) recs
         end.

  Definition isPure_rec_value `{Heap} (v : rec_value) :=
    match v with 
    | RFunc (_ , t) => is_true (isPure t)
    | Bad_recursive_value => True
    | _ => False
    end. 

  Fixpoint isPure_value `{Heap} (v : value) {struct v} :=
    match v with
    | Block (_,vs) => Forall (fun p => p) (map isPure_value vs)
    | Func (locals,_,t) => (forall s, isPure_value (locals s)) /\ is_true (isPure t)    
    | RClos (locals,self,mfix,t) => (forall s, isPure_value (locals s)) /\ Forall isPure_rec_value mfix
    | value_Int _ => True
    | Float _ => True
    | fail _ => True
    | _ => False
    end.

End fix_global.

Lemma isPure_add_self `{Heap} locals mfix self s :
  (forall s : Ident.t, isPure_value (locals s)) ->
  Forall isPure_rec_value mfix ->
  isPure_value (add_self self mfix locals s).
Proof.
  intros Hlocals Hmfix. unfold add_self, add_recs, List.mapi.
  generalize 0 as i. generalize self at 1. 
  induction self; cbn; eauto.
  unfold Ident.Map.add. destruct (Ident.eqb s a); cbn; eauto.
Qed.

Lemma isPure_heap `{Heap} `{WcbvFlags} locals h h' t v :
  is_true (isPure t) ->
  (forall s, isPure_value (locals s)) -> 
  eval [] locals h t h' v -> isPure_value v /\ h = h'.
Proof.
  intros Hpure Hlocals. induction 1; try solve [inversion Hpure]; cbn in Hpure;
  repeat rewrite MCProd.andb_and in Hpure; try solve [cbn; repeat split; eauto]; eauto. 
  - cbn in *. destruct Hpure as [? [? ?]].
    try (destruct IHeval1; eauto);
     try (destruct IHeval2; eauto); try (destruct IHeval3; eauto); try now eauto.
    destruct H4. intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); eauto.
  - destruct Hpure as [? [? ?]].
    try (destruct IHeval1; eauto);
     try (destruct IHeval2; eauto); try (destruct IHeval3; eauto); try now eauto.
    destruct H5. pose proof (proj1 (Forall_nth _ _) H9 n Bad_recursive_value). rewrite H1 in H10.
    eapply H10. case_eq (Nat.ltb n #|mfix|); try rewrite Nat.ltb_lt; eauto.
    rewrite Nat.ltb_ge. intro neq.  rewrite nth_overflow in H1; eauto. inversion H1.  
    destruct H5. intros s. unfold Ident.Map.add. destruct (Ident.eqb s y); eauto.
    eapply isPure_add_self; eauto. 
  - cbn in *. destruct Hpure as [? [? ?]]; try (destruct IHeval1; eauto); now eauto.
  - destruct Hpure as [? [? [? ?]]]. repeat rewrite MCProd.andb_and in IHeval.
    destruct IHeval ; eauto.
  - cbn in *. destruct Hpure as [[? ?] ?]; try (destruct IHeval1; eauto); try (destruct IHeval2; eauto); now eauto.  
  - cbn in *. destruct Hpure as [[? ?] ?]; try (destruct IHeval1; eauto); try (destruct IHeval2; eauto); try now eauto.
    intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); eauto.
  - cbn in *. destruct Hpure as [[? ?] ?]; try (destruct IHeval; eauto); try now eauto.
    intros s. rewrite H1. eapply isPure_add_self; eauto. unfold rfunc, RFunc_build.
    eapply forallb_Forall in H3. clear -H3. induction recs; eauto; cbn. destruct a; cbn in *. inversion H3; subst.
    econstructor; eauto. destruct t0; cbn; eauto. destruct p. cbn in H2. destruct l; cbn ; eauto.
    destruct l; cbn ; eauto.
  - cbn in *. destruct Hpure as [? ?]; try (destruct IHeval1; eauto); try (destruct IHeval2; eauto); try now eauto.
    induction cases; cbn in *. inversion H1. repeat rewrite MCProd.andb_and in H3. destruct H3.   
    destruct a. destruct (existsb _ _); [inversion H1; subst; eauto|]. now eapply IHcases.
  - cbn in *. clear H1 H2. induction H3; [now eauto|]. repeat rewrite MCProd.andb_and in Hpure.
    destruct Hpure. destruct IHForall2_acc; eauto. destruct H1; eauto. cbn; split; now eauto.
  - cbn in *. destruct IHeval; eauto. split; eauto. eapply Forall_nth; eauto. now eapply Forall_map_inv in H4.
  - cbn in *. now eauto.
  - cbn in *. inversion H1.
  - cbn in *. destruct IHeval; eauto.
  - cbn. destruct Hpure. destruct IHeval1; eauto. destruct IHeval2; eauto. now destruct op.
  - cbn; now eauto.   
  - cbn; destruct Hpure. destruct IHeval1; eauto. destruct IHeval2; now eauto.
  - cbn; destruct Hpure. destruct IHeval1; eauto. destruct IHeval2; now eauto.
  - cbn; destruct IHeval; eauto. 
  - cbn. destruct IHeval; eauto.
  - cbn. destruct IHeval; eauto.
Qed.            

Lemma isPure_heap_irr `{Heap} `{WcbvFlags} h h' locals t v :
  is_true (isPure t) ->
  (forall s, isPure_value (locals s)) -> 
  eval [] locals h t h' v -> forall h'', eval [] locals h'' t h'' v.
Proof.
  intros Hpure Hlocals. induction 1; try solve [inversion Hpure]; cbn in Hpure;
  repeat rewrite MCProd.andb_and in Hpure; try solve [cbn; destruct Hpure; econstructor; eauto]; 
  try solve [cbn; econstructor; eauto].
  - intro. destruct Hpure as [? [? ?]]. econstructor 3; eauto.
    eapply isPure_heap in H1_, H1_0; eauto. destruct H1_ as [[Hlocals' He] _].  
    eapply IHeval3; eauto. intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); now eauto.
  - intro. destruct Hpure as [? [? ?]]. econstructor 4; eauto.
    eapply isPure_heap in H1_, H1_0; eauto. destruct H1_ as [[Hlocals' He] _].
    pose proof (proj1 (Forall_nth _ _) He n Bad_recursive_value).
    rewrite H1 in H5. cbn in H5. eapply IHeval3.
    case_eq (Nat.ltb n #|mfix|); try rewrite Nat.ltb_lt; eauto.
    rewrite Nat.ltb_ge. intro neq. rewrite nth_overflow in H1; eauto. inversion H1.  
    destruct H1_0. intros s. unfold Ident.Map.add. destruct (Ident.eqb s y); eauto.
    eapply isPure_add_self; eauto. 
  - intro. destruct Hpure as [? [? ?]]. econstructor 6; eauto.
    eapply IHeval; eauto. cbn. now repeat rewrite MCProd.andb_and.
  - intro. destruct Hpure as [[? ?] ?]. econstructor; eauto. eapply IHeval2; eauto. 
    cbn. now repeat rewrite MCProd.andb_and.
  - intro. destruct Hpure as [[? ?] ?]. econstructor; eauto. eapply IHeval2; eauto. 
    cbn. now repeat rewrite MCProd.andb_and. 
    intros s. unfold Ident.Map.add. destruct (Ident.eqb s x); eauto. eapply isPure_heap in H1_; now eauto. 
  - intro. destruct Hpure as [[? ?] ?]. econstructor; eauto. rewrite H1 in IHeval. eapply IHeval; eauto; cbn.
    now repeat rewrite MCProd.andb_and. intro s. eapply isPure_add_self; eauto.
    unfold rfunc, RFunc_build.
    eapply forallb_Forall in H3. clear -H3. induction recs; eauto; cbn. destruct a; cbn in *. inversion H3; subst.
    econstructor; eauto. destruct t0; cbn; eauto. destruct p. cbn in H2. destruct l; cbn ; eauto.
    destruct l; cbn ; eauto. 
  - destruct Hpure. econstructor; eauto. eapply IHeval2; eauto.   
    induction cases; cbn in *. inversion H1. repeat rewrite MCProd.andb_and in H3. destruct H3.   
    destruct a. destruct (existsb _ _); [inversion H1; subst; eauto|]. now eapply IHcases.
  - econstructor; eauto. clear H1 H2. induction H3; [econstructor; eauto|].
    cbn in Hpure. rewrite MCProd.andb_and in Hpure. destruct Hpure. econstructor; eauto.
Qed. 

Axiom compile_pure : forall `{Heap} `{WcbvFlags} Σ t, is_true (isPure (compile_pipeline Σ t)).

Axiom compile_compose : forall `{Heap} `{WcbvFlags} (cf:=config.extraction_checker_flags) 
  (Σ:global_env) univ_decl h h' t u' u v w na A B,
  ∥ (Σ , univ_decl) ;;; [] |- t : tProd na A B ∥ ->
  ~ ∥Extract.isErasable (Σ , univ_decl) [] t∥ -> 
  eval [] (empty_locals _) h (compile_pipeline Σ.(declarations) u) h v ->
  eval [] (empty_locals _) h u' h' v ->
  eval [] (empty_locals _) h (Mapply (compile_pipeline Σ.(declarations) t, [u'])) h' w ->
  eval [] (empty_locals _) h (compile_pipeline Σ.(declarations) (tApp t u)) h w.

Axiom compile_function : forall `{Heap} `{WcbvFlags} (cf:=config.extraction_checker_flags)
  Σ univ_decl h h' f v na A B,
  ∥ (Σ , univ_decl) ;;; [] |- f : tProd na A B ∥ ->
  ~ ∥Extract.isErasable (Σ , univ_decl) [] f∥ ->
  eval [] (empty_locals _) h (compile_pipeline Σ.(declarations) f) h' v ->
  isFunction v = true.

Lemma CoqFunction_to_CamlFunction `{Heap} `{WcbvFlags} (cf:=config.extraction_checker_flags)
    univ retro univ_decl kn mind 
  (Hparam : ind_params mind = [])
  (Hindices : Forall (fun ind => ind_indices ind = []) (ind_bodies mind))
  (Hnparam : ind_npars mind = 0)
  (Hmono : ind_universes mind = Monomorphic_ctx)
  (Hfo : is_true (forallb (@firstorder_oneind [] mind) (ind_bodies mind))) ind Eind f na:
  let adt := CoqType_to_camlType mind Hparam Hfo in
  let Σ := mk_global_env univ [(kn , InductiveDecl mind)] retro in
  let global_adt := add_ADT _ [] [] kn adt in 
  PCUICTyping.wf Σ ->
  with_constructor_as_block = true ->
  ind < List.length (snd adt) ->
  lookup_inductive Σ (mkInd kn ind) = Some (mind, Eind) ->
  ∥ (Σ , univ_decl) ;;; [] |- f : tProd na (tInd (mkInd kn ind) []) (tInd (mkInd kn ind) []) ∥ ->
  realize_term _ [] []
        global_adt (Arrow (Adt kn (int_of_nat ind) []) (Adt kn (int_of_nat ind) [])) 
        (compile_pipeline Σ.(declarations)  f).
Proof.
  intros ? ? ? wfΣ ? ? Hlookup. intros. cbn. rewrite ReflectEq.eqb_refl. cbn.
  intros t Ht. unfold to_realize_term in *. intros h h' v Heval.
  assert (Hindmax : (Z.of_nat ind < Int63.wB)%Z).
  { epose proof (ind_wB mind _ _ _ _); eauto.
    cbn in H2. rewrite CoqType_to_camlType'_length in H2. lia. }
  rewrite int_to_of_nat in Ht; eauto. rewrite int_to_of_nat; eauto.
  pose proof (Hlookup' := Hlookup).
  unfold lookup_inductive, lookup_inductive_gen, lookup_minductive_gen in Hlookup. cbn in Hlookup.
  rewrite ReflectEq.eqb_refl in Hlookup.
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
  assert (Htype_ind' : (Σ, univ_decl);;;
  [],,
  vass na
    (tInd {| inductive_mind := kn; inductive_ind := ind |}
       [])
  |- tInd {| inductive_mind := kn; inductive_ind := ind |}
       [] : tSort (subst_instance_univ [] (ind_sort Eind))).
  {     unshelve epose proof (type_Ind (Σ,univ_decl) 
  ([],,vass na (tInd {| inductive_mind := kn; inductive_ind := ind |} [])) (mkInd kn ind) [] mind Eind _ _ _).
  *** econstructor. econstructor. cbn. unfold infer_sort.
      eexists; eauto.   
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
      now rewrite ind_arity_eq in X.  }      
  inversion Heval; subst.
  - specialize (Ht _ _ _ H8).
    unshelve eapply camlValue_to_CoqValue_nil in Ht; eauto; cbn.
    destruct Ht as [t_coq Ht]. specialize (Ht h2). destruct Ht as [Ht_typ Ht_eval].
    assert (h2 = h').
    { eapply isPure_heap in H6; try eapply compile_pure; intros; cbn; eauto. cbn in H6. destruct H6 as [[? ? ] ?]. 
      eapply isPure_heap; try apply H11; intros; cbn; eauto.
      unfold Ident.Map.add. destruct (Ident.eqb s x); eauto.
      eapply isPure_heap in Ht_eval; try eapply compile_pure; intros; cbn; eauto. now destruct Ht_typ. }
    subst. eapply isPure_heap in H6; try eapply compile_pure; intros; cbn; eauto.
    destruct H6 as [? ?]; subst.  
    eapply compile_compose in H8; eauto.
    2: { } 
    2: { eapply isPure_heap_irr,  Ht_eval; try eapply compile_pure; intros; cbn; eauto. }
    unshelve eapply CoqValue_to_CamlValue; try exact H8; try rewrite int_to_of_nat; eauto.
    destruct H3, Ht_typ. sq. 
    unshelve epose proof (type_App _ _ _ _ _ _ _ _ _ X X0); try exact (subst_instance_univ [] (ind_sort Eind)); eauto.
    rewrite <- (sort_of_product_idem _).
    eapply type_Prod; eauto.
  - specialize (Ht _ _ _ H7).
    eapply camlValue_to_CoqValue_nil in Ht; eauto; cbn.
    destruct Ht as [t_coq Ht].
    specialize (Ht h2).  destruct Ht as [Ht_typ Ht_eval].
    assert (h2 = h').
    { eapply isPure_heap in H6; try eapply compile_pure; intros; cbn; eauto.
      cbn in H6. destruct H6 as [[? ? ] ?].
      pose proof (proj1 (Forall_nth _ _) H5 n Bad_recursive_value).
      rewrite H9 in H8. cbn in H8.
      eapply isPure_heap in Ht_eval; try eapply compile_pure; intros; cbn; eauto. 
      destruct Ht_eval as [? _].
      case_eq (Nat.ltb n #|mfix|); try rewrite Nat.ltb_lt; eauto.
      intro; eapply isPure_heap; try apply H12; intros; cbn; eauto.
      unfold Ident.Map.add. destruct (Ident.eqb s y); eauto.
      cbn. eapply isPure_add_self; eauto.
      rewrite Nat.ltb_ge. intro neq. rewrite nth_overflow in H9; eauto. inversion H9. }
    subst. eapply isPure_heap in H6; try eapply compile_pure; intros; cbn; eauto. 
    destruct H6 as [? ?]; subst.  
    eapply compile_compose in H7; eauto. 
    2: { eapply isPure_heap_irr,  Ht_eval; try eapply compile_pure; intros; cbn; eauto. }
    unshelve eapply CoqValue_to_CamlValue; try exact H7; try rewrite int_to_of_nat; eauto.
    destruct H3, Ht_typ. sq.
    unshelve epose proof (type_App _ _ _ _ _ _ _ _ _ t0 X); try exact (subst_instance_univ [] (ind_sort Eind)); eauto. 
    rewrite <- (sort_of_product_idem _).
    eapply type_Prod; eauto.
  - rewrite (compile_function _ _ _ _ _ _ _ _ _ H3 H7) in H10. inversion H10.
Qed.
