From MetaCoq Require Import PCUICAstUtils.
From MetaCoq.Erasure Require Import EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv.
From Malfunction Require Import Ast.
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

Section Compile.
  Context (Σ : global_declarations).

  Definition int_of_nat n := Uint63.of_Z (Coq.ZArith.BinInt.Z.of_nat n).

  Import TermSpineView.

  Definition Mapply_ '(e, l) :=
      match l with [] => e | _ => Mapply (e, l) end.

  Definition Mlambda_ '(e, l) :=
      match e with [] => l | _ => Mlambda (e, l) end.

  Definition Mbox :=
    Mlet ([Recursive [("reccall"%string, Mlambda (["_"%string], Mvar 1) )]], Mvar 0).

  Definition lookup_record_projs (e : global_declarations) (ind : Kernames.inductive) : option (list Kernames.ident) :=
    match lookup_inductive e ind with
    | Some (mdecl, idecl) => Some (map proj_name idecl.(ind_projs))
    | None => None
    end.

  Equations? compile (t: term) : Malfunction.Ast.t
  by wf t (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel n => Mvar n
    | tBox => Mbox
    | tLambda nm bod => Mlambda ([bytestring.String.to_string (BasicAst.string_of_name nm)], compile bod)
    | tLetIn nm dfn bod => Mlet ([Named (bytestring.String.to_string (BasicAst.string_of_name nm), compile dfn)], compile bod)
    | tApp fn args napp nnil =>
        Mapply_ (compile fn, map_InP args (fun x H => compile x))
    | tConst nm => Mglobal (bytestring.String.to_string (Kernames.string_of_kername nm))
    | tConstruct i m args => Mblock (int_of_nat m, map_InP args (fun x H => compile x))
    | tCase i mch brs =>
        Mswitch (compile mch, mapi_InP brs 0 (fun i '(nms, b) H => ([Malfunction.Tag (int_of_nat i)], Mapply_ (Mlambda_ (rev_map (fun nm => bytestring.String.to_string (BasicAst.string_of_name nm)) nms, compile b),
                                                                                                        mapi (fun i _ => Mfield (int_of_nat i, compile mch)) (rev nms)))))
    | tFix mfix idx =>
        let bodies := map_InP mfix (fun d H => (bytestring.String.to_string (BasicAst.string_of_name (d.(dname))), compile d.(dbody))) in
        Mlet ([Recursive bodies], Mvar idx)
    | tProj (Kernames.mkProjection ind _ nargs) bod with lookup_record_projs Σ ind :=
      { | Some args =>
            let len := List.length args in
            Mfield (int_of_nat (len - 1 - nargs), compile bod)
        | None => Mstring "Proj" }
    | tCoFix mfix idx => Mstring "TCofix"
    | tVar _ => Mstring "tVar"
    | tEvar _ _ => Mstring "Evar"
    }.
  Proof.
    all: try (cbn; lia).
    - eapply size_mkApps_f; eauto.
    - eapply le_lt_trans. 2: eapply size_mkApps_l; eauto. eapply (In_size id size) in H.
      unfold id in H. change size with (fun x => size x) at 2. lia.
    - eapply (In_size id size) in H.
      unfold id in H. change size with (fun x => size x) at 2. lia.
    - eapply (In_size snd size) in H. cbn in H.
      lia.
    - eapply (In_size dbody size) in H. cbn in H. lia.
  Qed.
  
End Compile.

From MetaCoq Require Import ETransform Transform bytestring.
Import Transform.

Require Malfunction.SemanticsSpec Malfunction.Semantics.

Program Definition block_erasure_pipeline {guard : PCUICWfEnvImpl.abstract_guard_impl} (efl := EWellformed.all_env_flags) :=
  erasure_pipeline ▷ constructors_as_blocks_transformation (hastrel := eq_refl) (hastbox := eq_refl).
Next Obligation.
  intros. cbn. MCUtils.todo "ok"%bs.
Qed.

Program Definition malfunction_pipeline {guard : PCUICWfEnvImpl.abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program Malfunction.t
             Ast.term Malfunction.t
             TemplateProgram.eval_template_program
             (fun _ _ => True) :=
  block_erasure_pipeline ▷ 
  _.
Next Obligation.
  intros. unshelve econstructor.
  - exact (fun _ => True).
  - cbn. intros [Σ t] _. refine (Semantics.named _ (compile Σ t)). exact [].
  - exact (fun _ => True).
  - exact (fun _ _ _ _ => True).
  - exact "malfunction"%bs.
  - cbn. eauto.
  - cbn. econstructor. exact (Malfunction.Mvar ""%string). eauto.
Defined.
Next Obligation.
  cbn. intros. eauto.
Qed.

From Ceres Require Import Ceres.
From Malfunction Require Import Serialize.

Definition compile_malfunction {cf : config.checker_flags} (p : Ast.Env.program)
  : String.string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs to_string  p'.

From MetaCoq.Template Require Import All Loader.

Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).

MetaCoq Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv delta [ack35 ack] in ack35) in exact t).
Local Open Scope string_scope.

(* MetaCoq Quote Recursively Definition p := ltac:(let plus := eval cbv in plus in *)
(*                                                 let mult := eval cbv in mult in *)
(*                                                   let eqb := eval cbv in Nat.eqb in *)
(*                                                     exact (let six := 6 in eqb (plus (mult six six) six) (mult six (plus six 1)))). *)
Compute (compile_malfunction cbv_ack35).
