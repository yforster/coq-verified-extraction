Require Import ssreflect.
From Malfunction Require Import Malfunction SemanticsSpec.
From MetaCoq.PCUIC Require Import PCUICAst PCUICFirstorder.

Require Import ZArith Array.PArray List String Floats Lia Bool.
Import ListNotations.


Inductive camlType : Set :=
    Arrow : camlType -> camlType -> camlType
  | Rel : nat -> camlType 
  | Adt : kername -> 
            (* number of ADT in the mutual definition *) nat -> 
            (* list of parameters *) list camlType -> 
            camlType.

Notation "A → B" := (Arrow A B) (at level 50). 

Definition ADT : Set := 
  (* number of parameters *)
  nat * list (
  nat (* constructors w/o arguments *) *
  list (list camlType) (* constrcutors w/ arguments *)).

Section Realizability. 

  Definition realize_term `{Heap} (A:camlType) : t -> Prop.
  Admitted. 

  Fixpoint realize_val `{Heap} (A:camlType) locals : value -> Prop.
    refine (
      match A with 
       | Arrow A' B'=> fun f => _
       | Rel n => _
       | Adt kn n params => _
      end); clear A.
    - refine (exists locals x t, f = Func (locals,x,t) /\ 
                forall v id, realize_val _ A' v -> 
                             realize_term (Mapply (Mlambda ([x],t),[Mvar id]))).

End Realizability.

Section firstorder.

  Context {Σb : list (kername * bool)}.

  Definition CoqType_to_camlType_oneind_type n k decl_type :
    is_true (@firstorder_type Σb k n decl_type) -> camlType.
  Proof.
    unfold firstorder_type. intro H.
    destruct (fst _); inversion H.
    (* case of tRel with a valid index *)
    - exact (Rel n0).
    (* case of tInd where Σb is saying that inductive_mind is first order *)
    - destruct ind. exact (Adt inductive_mind inductive_ind []).
  Defined.  

  Definition CoqType_to_camlType_oneind mind ind : 
    ind_params mind = [] -> 
    is_true (@firstorder_oneind Σb mind ind) -> nat * list (list camlType).
  Proof.
    destruct ind. intros Hparam H. apply MCProd.andb_and in H.
    destruct H as [H _]. cbn in *. clear -H Hparam.
    induction ind_ctors0.
    (* no more constructor *)
    - exact (O , []).
    (* a :: ind_ctors0 constructors *)
    - apply MCProd.andb_and in H. destruct H. destruct (IHind_ctors0 H0) as [n l].
      (* [n l] codes for ind_ctors *)
      destruct a. revert H. cbn. rewrite Hparam. generalize (rev (cstr_args0 ++ [])).
      clear - n l.
      intros cstr; generalize 0. destruct cstr; intros.
      (* cstr is a constrcutor with no argument, we increment the number n *)
      + exact (S n,l).
      (* c :: cstr , we extend the list of list *)
      + refine (n,_::l). clear n l.
        revert n0 H. generalize (c::cstr). clear. 
        intros cstr; induction cstr; cbn; intros. 
        (* we convert the type of the first type of the constructor *)
        * exact [].
        * apply MCProd.andb_and in H. destruct H. destruct a.
        (* we convert the type of the first type of the constructor *)
          apply CoqType_to_camlType_oneind_type in H.
          refine (H :: _). clear H.
        (* we recursively convert *)
          exact (IHcstr _ H0).
    Defined.

  (* The following function morally do (map CoqType_to_camlType_oneind) while passing 
  th proof that everything is first order *)

  Definition CoqType_to_camlType mind : 
    ind_params mind = [] -> 
    is_true (@firstorder_mutind Σb mind) -> ADT.
  Proof.
    (* no parameters *)
    intros Hparam H. refine (0,_).
    destruct mind. unfold firstorder_mutind; cbn. 
    apply MCProd.andb_and in H. destruct H as [_ H].
    revert H. generalize ind_bodies0 at 1. induction ind_bodies0; cbn in *; intros.
    - exact [].
    - apply MCProd.andb_and in H. destruct H. cbn in *. 
      specialize (IHind_bodies0 Hparam _ H0). clear H0. refine (_ :: IHind_bodies0). 
      apply (CoqType_to_camlType_oneind) in H; eauto.
  Defined.

End firstorder.

