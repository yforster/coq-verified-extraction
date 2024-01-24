From Coq Require Import List String Arith Lia.
Import ListNotations.
From Equations Require Import Equations.

From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Utils Require Import MCList bytestring.
From MetaCoq.Erasure Require Import EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv.

From Malfunction Require Import utils_array Malfunction.
Open Scope bs.

Section MapiInP.
  Context {A B : Type}.

  Equations mapi_InP (l : list A) (n : nat) (f : nat -> forall x : A, In x l -> B) : list B :=
  mapi_InP nil n _ := nil;
  mapi_InP (cons x xs) n f := cons (f n x _) (mapi_InP xs (S n) (fun n x inx => f n x _)).
End MapiInP.

Lemma mapi_InP_spec' {A B : Type} (f : nat -> A -> B) (l : list A) n :
  mapi_InP l n (fun n (x : A) _ => f n x) = mapi_rec f l n.
Proof.
  remember (fun n (x : A) _ => f n x) as g.
  funelim (mapi_InP l n g); simpl. reflexivity.
  simp mapi_InP.
  f_equal. 
  now rewrite (H f0).
Qed.

Lemma mapi_InP_spec {A B : Type} (f : nat -> A -> B) (l : list A) :
  mapi_InP l 0 (fun n (x : A) _ => f n x) = mapi f l.
Proof.
  eapply mapi_InP_spec'.
Qed.

Definition Mapply_ '(e, l) :=
    match l with [] => e | _ => Mapply (e, l) end.

Definition Mlambda_ '(e, l) :=
    match e with [] => l | _ => Mlambda (e, l) end.

Definition blocks_until i (num_args : list nat) :=
  #| filter (fun x => match x with 0 => false | _ => true end) (firstn i num_args)|.

Definition nonblocks_until i num_args :=
    #| filter (fun x => match x with 0 => true | _ => false end) (firstn i num_args)|.

Definition Mcase : list nat * t * list (list Ident.t * t) -> t :=
 fun '(num_args, discr, brs) =>
   Mswitch (discr, mapi (fun i '(nms, b) => 
      (match nth_error num_args i with
      | Some 0 =>  [Malfunction.Intrange (int_of_nat (nonblocks_until i num_args), int_of_nat (nonblocks_until i num_args))]
      | _hasargs => [Malfunction.Tag (int_of_nat (blocks_until i num_args))]
      end,
      Mapply_ (Mlambda_ (nms, b), mapi (fun i _ => Mfield (int_of_nat i, discr)) (nms)))) brs).

From MetaCoq Require Import EAst.

Section Compile.
  Context (Σ : global_declarations).

  Definition lookup_record_projs (e : global_declarations) (ind : Kernames.inductive) : option (list Kernames.ident) :=
    match lookup_inductive e ind with
    | Some (mdecl, idecl) => Some (map proj_name idecl.(ind_projs))
    | None => None
    end.

  Definition lookup_constructor_args (e : global_declarations) (ind : Kernames.inductive) : option (list nat) :=
    match lookup_inductive e ind with
    | Some (mdecl, idecl) => Some (map cstr_nargs idecl.(ind_ctors))
    | None => None
    end.

  Definition Mapply_u t a :=
    match t with Mapply (fn, args) => Mapply (fn, List.app args [a]) | _ => Mapply (t, [a]) end.

  Obligation Tactic := idtac.

  Definition to_primitive (v : EPrimitive.prim_val EAst.term) : Malfunction.t :=
    match projT2 v with
    | EPrimitive.primIntModel i => Mnum (numconst_Int i)
    | EPrimitive.primFloatModel f => Mnum (numconst_Float64 f)
    (* error: primitive arrays not supported *)
    | EPrimitive.primArrayModel a => Mnum (numconst_Int (int_of_nat 0))
    end.

  Definition force_lambda (t : Malfunction.t) :=
    match t with
    | Mlambda _ => t
    | _ => Mlambda (["__expanded"], Mapply_u t (Mvar "__expanded"))
    end.

  Equations? compile (t: term) : Malfunction.t
    by wf t (fun x y : EAst.term => size x < size y) :=
      | tVar na => Mvar na
      | tLambda nm bod => Mlambda ([(BasicAst.string_of_name nm)], compile bod)
      | tLetIn nm dfn bod => Mlet ([Named ((BasicAst.string_of_name nm), compile dfn)], compile bod)
      | tApp fn arg =>
          Mapply_u (compile fn) (compile arg)
      | tConst nm => Mglobal (Kernames.string_of_kername nm)
      | tConstruct i m [] =>
        match lookup_constructor_args Σ i with
        | Some num_args => Mnum (numconst_Int (int_of_nat (nonblocks_until m num_args)))
        | None => Mstring "error: inductive not found"
        end
      | tConstruct i m args =>
        match lookup_constructor_args Σ i with
        | Some num_args => Mblock (int_of_nat (blocks_until m num_args), map_InP args (fun x H => compile x))
        | None => Mstring "error: inductive not found"
        end
      | tCase i mch [] => Mlambda (["empty_match"], Mvar "empty_match")
      | tCase i mch brs =>
        match lookup_constructor_args Σ (fst i) with
        | Some num_args =>
            Mcase (num_args, compile mch, map_InP brs (fun br H => (rev_map (fun nm => (BasicAst.string_of_name nm)) (fst br), compile (snd br))))     
       | None => Mstring "error: inductive not found"
        end
      | tFix mfix idx =>
          let bodies := map_InP mfix (fun d H => ((BasicAst.string_of_name (d.(dname))), force_lambda (compile d.(dbody)))) in
          Mlet ([Recursive bodies], Mvar (fst (nth (idx) bodies ("", Mstring ""))))
      | tProj (Kernames.mkProjection ind _ nargs) bod with lookup_record_projs Σ ind :=
        { | Some args =>
              let len := List.length args in
              Mfield (int_of_nat (len - 1 - nargs), compile bod)
          | None => Mstring "inductive not found" }
      | tPrim p => to_primitive p
      | tRel n => Mstring "error: tRel has been translated away"
      | tBox => Mstring "error: tBox has been translated away"
      | tCoFix mfix idx => Mstring "error: tCofix not supported"
      | tEvar _ _ => Mstring "error: tEvar not supported"
      .
    Proof.
      all: try (cbn; lia).
      - subst args. eapply (In_size id size) in H.
        unfold id in H. change size with (fun x => size x) at 2. cbn [size]. exact H.
      - eapply (In_size snd size) in H. cbn in *.
        lia.
      - eapply (In_size dbody size) in H. cbn in *. lia.
    Qed.
 
End Compile.

Definition compile_constant_decl Σ cb := 
  option_map (compile Σ) cb.(cst_body).

Fixpoint compile_env Σ : list (string * option t) := 
  match Σ with
  | [] => []
  | (x,d) :: Σ => match d with
                  ConstantDecl cb => (Kernames.string_of_kername x, compile_constant_decl Σ cb) :: compile_env Σ
                | _ => compile_env Σ
              end
  end.

Definition compile_program (p : EProgram.eprogram) : Malfunction.program :=
  (compile_env (fst p), compile (fst p) (snd p)).
