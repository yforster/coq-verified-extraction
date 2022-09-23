Require Import List String.
Import ListNotations.
Local Open Scope string_scope.

From Malfunction Require Import Compile SemanticsSpec Mcase.
From MetaCoq Require Import ReflectEq EWcbvEvalNamed bytestring.

From Equations Require Import Equations.

Definition lookup {A} (E : list (Kernames.ident * A)) (x : string) :=
  match find (fun '(s, _) => String.eqb x s) E with
  | Some (_, v) => Some v
  | None => None
  end.

Fixpoint compile_value (Σ : EAst.global_declarations) (s : EWcbvEvalNamed.value) : SemanticsSpec.value :=
  match s with
  | vBox =>
      Func ("_"%string, (fun _ => fail "empty"),  Malfunction.Mlet ([Malfunction.Recursive [("reccall", Malfunction.Mlambda (["_"], Malfunction.Mvar "reccall") )]], Malfunction.Mvar "reccall"))
  | vClos na b env => Func (bytestring.String.to_string na, (fun x =>
                                                              match lookup (map (fun '(x,v) => (x, compile_value Σ v)) env) (String.of_string x) with Some v => v | None => fail "notfound" end), compile Σ b)
  | vConstruct ind c args => Block (int_of_nat c, map (compile_value Σ) args)
  | vRecClos b idx env => fail "ok"
  end.

Require Import FunctionalExtensionality.

Lemma compile_correct Σ s t Γ Γ' :
  (forall na v, lookup Γ na = Some v -> Malfunction.Ident.Map.find (bytestring.String.to_string na) Γ' = compile_value Σ v) ->
   EWcbvEvalNamed.eval Σ Γ s t ->
   SemanticsSpec.eval (compile_env Σ) Γ' (compile Σ s) (compile_value Σ t).
Proof.
  intros HΓ Heval.
  revert Γ' HΓ.
  induction Heval; intros Γ_ HΓ; simp compile; try rewrite <- !compile_equation_1.
  - (* variables *)
    rewrite <- (HΓ _ _ e). econstructor.
  - (* box app *)
    cbn. admit.
  - (* beta *)
    admit.
  - (* lambda *)
    cbn.
    erewrite (functional_extensionality (fun x : Malfunction.Ident.t => match lookup (map (fun '(x0, v) => (x0, compile_value Σ v)) Γ) (String.of_string x) with
                                       | Some v => v
                                       | None => fail "notfound"
                                       end)).
    econstructor.
    intros x. unfold Malfunction.Ident.Map.find in *. 
    admit.
  - cbn. econstructor.
    + now eapply IHHeval1.
    + econstructor. eapply IHHeval2.
      intros. unfold add, lookup in H. cbn in H.
      change (String.eqb na0 na) with (na0 == na) in *.
      destruct (eqb_spec na0 na).
      * inversion H; subst. unfold Malfunction.Ident.Map.add, Malfunction.Ident.Map.find, Malfunction.Ident.eqb.
        now rewrite String.eqb_refl.
      * unfold Malfunction.Ident.Map.add, Malfunction.Ident.Map.find, Malfunction.Ident.eqb.
        destruct (String.eqb_spec (String.to_string na0) (String.to_string na)).
        -- admit.
        -- eauto.
  - (* case *)
    replace ((Malfunction.Mswitch
       (compile Σ discr,
        mapi_InP brs 0
          (fun (i : nat) (pat : list BasicAst.name * EAst.term) =>
           let
           '(nms0, b) as x := pat return (In x brs -> list Malfunction.case * Malfunction.t) in
            fun _ : In (nms0, b) brs =>
            ([Malfunction.Tag (Compile.int_of_nat i)],
             Compile.Mapply_
               (Compile.Mlambda_ (MCList.rev_map (fun nm : BasicAst.name => String.to_string (BasicAst.string_of_name nm)) nms0, compile Σ b),
                MCList.mapi (fun (i0 : nat) (_ : BasicAst.name) => Malfunction.Mfield (Compile.int_of_nat i0, compile Σ discr)) (MCList.rev nms0)))))))
              with (Mcase (compile Σ discr, map (fun '(brs, b) => (map (fun x => String.to_string (BasicAst.string_of_name x)) brs, compile Σ b)) brs)).
    + eapply eval_case. all: admit.
    + unfold Mcase. repeat f_equal.
      rewrite !MCList.mapi_map.
      (* rewrite <- !mapi_InP_spec. *)
      (* clear. generalize 0. induction brs; cbn; intros; simp mapi_InP. *)
      (* * reflexivity. *)
      (* * f_equal. destruct a. f_equal. *)
      (*   rewrite !MCList.mapi_map. *)
      (*   admit. *)
      (*   eapply IHbrs. *)
      (* *  *)
      admit.
  - (* recursion *)
    admit.
  - (* fix *)
    cbn. admit.
  - (* global *)
    econstructor. 2: eauto. admit.
  - (* constructor application *)
    cbn. econstructor.
    rewrite MCList.map_InP_spec, !map_app. cbn.
    eapply Forall2_app.
    + admit.
    + repeat econstructor. now eapply IHHeval2.
  - cbn. repeat econstructor.
Admitted.
