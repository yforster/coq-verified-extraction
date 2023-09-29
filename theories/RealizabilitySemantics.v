Require Import ssreflect ssrbool Eqdep_dec.
From Equations Require Import Equations. 
From MetaCoq.Utils Require Import All_Forall MCSquash MCList.
From MetaCoq.Common Require Import Transform config Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICFirstorder PCUICCasesHelper BDStrengthening PCUICCumulativity.
From MetaCoq.Erasure Require Import EWcbvEval EWcbvEvalNamed.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.

From Malfunction Require Import Malfunction SemanticsSpec utils_array Compile.

Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.
From MetaCoq.Utils Require Import bytestring.

Unset Elimination Schemes. 

Inductive camlType : Set :=
    Arrow : camlType -> camlType -> camlType
  | Rel : nat -> camlType
  | Adt : kername -> 
            (* number of the ADT in the mutual definition *) nat -> 
            (* list of parameters *) list camlType -> 
            camlType.

Definition camlType_rect :
forall P : camlType -> Type,
       (forall c : camlType,
        P c -> forall c0 : camlType, P c0 -> P (Arrow c c0)) ->
       (forall n : nat, P (Rel n)) ->
       (forall (k : kername) i (l : list camlType), All P l -> P (Adt k i l)) ->
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
          refine (to_realize_term (Hrel params _ n)).
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

  Definition cstr_nargs : constructor_body -> nat := fun c => #| cstr_args c|.

  Lemma Forall2_map_left {A B C} (P : A -> B -> Prop) (f : C -> A) (l : list C) (l' : list B) :
    Forall2 P (map f l) l' <-> Forall2 (fun x y => P (f x) y) l l'.
  Proof.
    split; intros.
    + eapply Forall2_map_inv. now rewrite map_id.
    + rewrite -(map_id l'). now eapply Forall2_map.
  Qed.

  Definition lookup_constructor_args Σ ind : option (list nat) 
    := match lookup_inductive Σ ind with
    | Some (_, idecl) => Some (map cstr_nargs (ind_ctors idecl))
   | None => None
    end.

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

  Section Pure.

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

End Pure.

From Malfunction Require Import CompileCorrect Pipeline.

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