From MetaCoq Require Import PCUICAstUtils.
From MetaCoq.Erasure Require Import EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv.
From Malfunction Require Import Malfunction.
From Equations Require Import Equations.
From Coq Require Import List String Arith Lia.
Import ListNotations.
From MetaCoq Require Import MCList.

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

Local Coercion conv :=
  fun x => bytestring.String.to_string (Kernames.string_of_kername x).

From MetaCoq Require Import EAst.

Section Compile.
  Context (Σ : global_declarations).

  Definition int_of_nat n := Uint63.of_Z (Coq.ZArith.BinInt.Z.of_nat n).

  Definition Mapply_ '(e, l) :=
      match l with [] => e | _ => Mapply (e, l) end.

  Definition Mlambda_ '(e, l) :=
      match e with [] => l | _ => Mlambda (e, l) end.

  Open Scope string.

  Definition Mbox :=
    Mlet ([Recursive [("reccall", Mlambda (["_"%string], Mvar "reccall") )]], Mvar "reccall").

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

  Equations? compile (t: term) : Malfunction.t
    by wf t (fun x y : EAst.term => size x < size y) :=
      | tRel n => Mstring "tRel"
      | tBox => Mbox
      | tLambda nm bod => Mlambda ([bytestring.String.to_string (BasicAst.string_of_name nm)], compile bod)
      | tLetIn nm dfn bod => Mlet ([Named (bytestring.String.to_string (BasicAst.string_of_name nm), compile dfn)], compile bod)
      | tApp fn arg =>
          Mapply_u (compile fn) (compile arg)
      | tConst nm => Mglobal nm
      | tConstruct i m [] =>
        match lookup_constructor_args Σ i with
        | Some num_args => let num_args_until_m := firstn m num_args in
                          let index := #| filter (fun x => match x with 0 => true | _ => false end) num_args_until_m| in
                          Mnum (numconst_Int (int_of_nat index))
        | None => Mstring "inductive not found"
        end
      | tConstruct i m args =>
        match lookup_constructor_args Σ i with
        | Some num_args => let num_args_until_m := firstn m num_args in
                          let index := #| filter (fun x => match x with 0 => false | _ => true end) num_args_until_m| in
                          Mblock (int_of_nat index, map_InP args (fun x H => compile x))
        | None => Mstring "inductive not found"
        end
      | tCase i mch brs =>
          match lookup_constructor_args Σ (fst i) with
          | Some num_args =>
              Mswitch (compile mch, mapi_InP brs 0 (fun i br H => (match fst br with
                                                                | [] => let num_args_until_i := firstn i num_args in
                                                                       let index := #| filter (fun x => match x with 0 => true | _ => false end) num_args_until_i| in
                                                                       [Malfunction.Tag (int_of_nat index)]
                                                                | args => let num_args_until_i := firstn i num_args in
                                                                         let index := #| filter (fun x => match x with 0 => false | _ => true end) num_args_until_i| in
                                                                         [Malfunction.Intrange (int_of_nat index, int_of_nat index)]
                                                                end, Mapply_ (Mlambda_ (rev_map (fun nm => bytestring.String.to_string (BasicAst.string_of_name nm)) (fst br), compile (snd br)),
                                                                                                          mapi (fun i _ => Mfield (int_of_nat i, compile mch)) (rev (fst br))))))
          | None => Mstring "inductive not found"
          end
      | tFix mfix idx =>
          let bodies := map_InP mfix (fun d H => (bytestring.String.to_string (BasicAst.string_of_name (d.(dname))), compile d.(dbody))) in
          Mlet ([Recursive bodies], Mvar (fst (nth (idx) bodies ("", Mstring ""))))
      | tProj (Kernames.mkProjection ind _ nargs) bod with lookup_record_projs Σ ind :=
        { | Some args =>
              let len := List.length args in
              Mfield (int_of_nat (len - 1 - nargs), compile bod)
          | None => Mstring "Proj" }
      | tCoFix mfix idx => Mstring "TCofix"
      | tVar na => Mvar (bytestring.String.to_string na)
      | tEvar _ _ => Mstring "Evar"
      | tPrim _ => Mstring "Prim".
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
  
Definition compile_decl Σ d :=
  match d with
  | ConstantDecl cb => compile_constant_decl Σ cb
  | InductiveDecl idecl => None
  end.

Definition compile_env Σ := flat_map
(fun '(x, d) =>
 match compile_decl Σ d with
 | Some t => [(Compile.conv x, t)]
 | None => []
 end) Σ.

Fixpoint compile_env' Σ : list (string * t) := 
  match Σ with
  | [] => []
  | (x,d) :: Σ => match compile_decl Σ d with Some t => (conv x, t) :: compile_env' Σ 
                                         | _ => compile_env' Σ
              end
  end.

Definition compile_program (p : EProgram.eprogram) : Malfunction.program :=
  (compile_env (fst p), compile (fst p) (snd p)).
