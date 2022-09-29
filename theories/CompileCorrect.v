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
  | vRecClos mfix idx env => let y'_t' :=
                             match
                               nth_error mfix (Datatypes.length mfix - idx - 1) with Some (dname, EAst.tLambda y' t') => (String.to_string (BasicAst.string_of_name y'), t')
                               | _ => ("", EAst.tVar "invalid recursive closure"%bs)
                               end in
                                Func
                                (fst y'_t', 
                                fun x => match lookup (map (fun '(x,v) => (x, compile_value Σ v)) env) (String.of_string x) with Some v => v | _ => fail "notfound" end,
                                Malfunction.Mlet
                                 ([Malfunction.Recursive
                                     (map
                                        (fun x =>
                                         (String.to_string ( (fst x)),
                                          compile Σ (snd x))) mfix)], compile Σ (snd y'_t')))
                                
  end.

Require Import FunctionalExtensionality.

Lemma to_string_of_string s : 
  String.to_string (String.of_string s) = s.
Proof.
  induction s; cbn.
  - reflexivity.
  - now rewrite Ascii.ascii_of_byte_of_ascii, IHs.
Qed.

Lemma of_string_to_string s : 
  String.of_string (String.to_string s) = s.
Proof.
  induction s; cbn.
  - reflexivity.
  - now rewrite Ascii.byte_of_ascii_of_byte, IHs.
Qed.

Lemma lookup_map {A B} (f : A -> B) Γ x :
  lookup (map (fun '(x0, v) => (x0, f v)) Γ) x = option_map f (lookup Γ x).
Proof.
  unfold lookup.
  induction Γ as [ | []].
  - reflexivity.
  - cbn in *. change (String.eqb x i) with (eqb x i). destruct (eqb_spec x i).
    + subst. reflexivity.
    + eapply IHΓ.
Qed.

Lemma rev_spec {A} (l : list A) : MCList.rev l = rev l.
Proof. 
  unfold MCList.rev.
  rewrite <- (app_nil_r (rev l)).
  generalize (@nil A).
  induction l; cbn; intros; try congruence.
  rewrite IHl. now rewrite <- app_assoc.
Qed.

Lemma lookup_add a v Γ na :
  lookup (add a v Γ) na = if na == a then Some v else lookup Γ na.
Proof.
  unfold add, lookup. cbn. change (String.eqb na a) with (na == a).
  destruct (eqb_spec na a); congruence.
Qed.

Require Import Lia.

Lemma lookup_multiple nms args Γ na :
  List.length nms = List.length args ->
  lookup (add_multiple nms args Γ) na = match find (fun x => na == fst x) (map2 pair nms args) with 
                                        | Some (_, y) => Some y
                                        | None => lookup Γ na
                                        end.
Proof.
  intros Hlen. induction nms in args, Hlen |- *.
  - destruct args; cbn in *; congruence.
  - destruct args; cbn in *; try congruence.
    rewrite lookup_add, IHnms. 2: cbn in *; lia.
    destruct (eqb_spec na a).
    + eauto.
    + reflexivity.
Qed.

Lemma Mapply_eval globals locals (x : Malfunction.Ident.t)
    (locals' : Malfunction.Ident.Map.t)
    (e e2 : Malfunction.t) (v2 : SemanticsSpec.value)
    (e1 : Malfunction.t) (v : SemanticsSpec.value) args :
    SemanticsSpec.eval globals locals (Mapply_ (e1, args)) (Func (x, locals', e)) ->
    SemanticsSpec.eval globals locals e2 v2 ->
    SemanticsSpec.eval globals (Malfunction.Ident.Map.add x v2 locals') e v ->
    SemanticsSpec.eval globals locals (Malfunction.Mapply (e1, args ++ [e2]))%list v.
Proof.
  replace e1 with (Mnapply e1 []) by reflexivity.
  generalize (@nil Malfunction.t) at 1 2.
  induction args in e1 |- *; intros l Hleft Hright Happ; cbn.
  - econstructor; cbn in *; eauto.
  - cbn. econstructor.
    replace (Malfunction.Mapply (Mnapply e1 l, [a])) with
    (Mnapply e1 (l ++ [a])) by now rewrite Mnapply_app. cbn.
    eapply IHargs; eauto.
    cbn in Hleft.
    eapply eval_app_nested_inv with (args := a :: args) in Hleft.
    eapply eval_app_nested_. now rewrite <- app_assoc.
Qed.

Lemma Mapply_u_spec f a :
   ~ (exists n, f = Malfunction.Mapply (n, [])) ->
   (exists fn args, f = Mapply_ (fn, args) /\ Mapply_u f a = Mapply_ (fn, args ++ [a]))%list \/
   (~ (exists fn args, f = Malfunction.Mapply (fn, args)) /\ Mapply_u f a = Mapply_ (f, [a])).
Proof.
  destruct f; cbn; firstorder try congruence.
  left. destruct p. exists t, l; cbn. destruct l; cbn; eauto.
  edestruct H; eauto.
Qed.  

Lemma lookup_env_In d Σ : 
  EGlobalEnv.lookup_env Σ (fst d) = Some (snd d) -> In d Σ.
Proof.
  induction Σ; cbn in *.
  - congruence.
  - destruct (eqb_spec (fst d) (fst a)). intros [=]. destruct a, d; cbn in *; intuition auto.
    left; subst; auto.
    intros hl; specialize (IHΣ hl); intuition auto.
Qed.

Fixpoint add_recs'' (locals : Malfunction.Ident.Map.t) allrecs recs  :=
  match recs with
  | [] => locals
  | (x, (y, e)) :: recs =>  
    let locals' := add_recs'' locals allrecs recs in
    Malfunction.Ident.Map.add x (Func (y, locals, Malfunction.Mlet ([Malfunction.Recursive allrecs], e))) locals'
  end.

Lemma add_recs''_spec locals allrecs recs x y t :
  NoDup (map fst recs) ->
  In (x, (y, t)) recs ->
  Malfunction.Ident.Map.find x (add_recs'' locals allrecs recs) =
  (Func (y, locals, Malfunction.Mlet ([Malfunction.Recursive allrecs], t))).
Proof.
  intros Hdup Hin. induction recs.
  - cbn in *. tauto.
  - cbn in *. inversion Hdup as [ | a_ b Hdup1 Hdup2 e ]; subst.
    destruct Hin.
    + subst. unfold Malfunction.Ident.Map.add, Malfunction.Ident.eqb. now rewrite String.eqb_refl.
    + destruct a as [? [] ]. unfold Malfunction.Ident.Map.add, Malfunction.Ident.eqb.
      destruct (String.eqb_spec x t0).
      * subst. cbn in *. destruct Hdup1. eapply in_map_iff. eexists (_ ,(_, _)); cbn. eauto.
      * eapply IHrecs; eauto.
Qed.

Lemma Mapply_spec fn args : 
  args <> nil ->
  Mapply_ (fn, args) = Malfunction.Mapply (fn, args).
Proof.
  destruct args; cbn; congruence.
Qed.

(* TODO: annotate wellformedness in both fix rules *)
(* annotate pars = 0 *)
(* use n-ary constructor rule *)

Lemma compile_correct Σ s t Γ Γ' :
  (forall na, Malfunction.Ident.Map.find (bytestring.String.to_string na) Γ' =
                match lookup Γ na with Some v => compile_value Σ v | _ => fail "notfound" end) ->
   EWcbvEvalNamed.eval Σ Γ s t ->
   SemanticsSpec.eval (compile_env Σ) Γ' (compile Σ s) (compile_value Σ t).
Proof.
  intros HΓ Heval.
  revert Γ' HΓ.
  induction Heval; intros Γ_ HΓ; simp compile; try rewrite <- !compile_equation_1.
  - (* variables *)
    specialize (HΓ na).
    unfold EWcbvEvalNamed.lookup, lookup in *.
    rewrite e in HΓ. rewrite <- HΓ.
    econstructor. 
  - (* box app *)
    cbn. todo "fix statement to talk about box: then we can't just compile, but need to existentially quantify over the environment in the closure".
  - (* beta *)
    destruct (Mapply_u_spec (compile Σ f) (compile Σ a)) as [(fn & arg & E & ->) | (E & ->) ].
    + destruct f; simp compile; intros [? [=]]. 
      * destruct (compile Σ f1); cbn in H0; try congruence. destruct p, l; cbn in *; congruence.
      * revert H0. destruct p. simp compile. unfold compile_unfold_clause_10. 
        destruct lookup_record_projs; congruence.
    + rewrite Mapply_spec. 2: destruct arg; cbn; congruence.
      eapply Mapply_eval.
      * rewrite <- E. cbn in IHHeval1. eauto.
      * eauto.
      * erewrite (functional_extensionality ((Malfunction.Ident.Map.add (String.to_string na) 
             (compile_value Σ a')
             (fun x : Malfunction.Ident.t =>
              match
                lookup (map (fun '(x0, v) => (x0, compile_value Σ v)) Γ')
                  (String.of_string x)
              with
              | Some v => v
              | None => fail "notfound"
              end))) (fun na0 => match lookup (add na a' Γ') (String.of_string na0) with
              | Some v => compile_value Σ v
              | None => fail "notfound"
              end)). eapply IHHeval3.
        -- intros na0. unfold Malfunction.Ident.Map.find. now rewrite (of_string_to_string).
        -- intros x.  unfold Malfunction.Ident.Map.find. rewrite lookup_add.
           unfold Malfunction.Ident.Map.add. unfold Malfunction.Ident.eqb.
           destruct (String.eqb_spec x (String.to_string na)).
           ++ subst. rewrite of_string_to_string. now rewrite eqb_refl.
           ++ destruct (eqb_spec (String.of_string x) na).
              ** subst. rewrite to_string_of_string in n. congruence.
              ** rewrite lookup_map. now destruct lookup.
    + econstructor. cbn in *. eauto. eauto.
      erewrite (functional_extensionality ((Malfunction.Ident.Map.add (String.to_string na) 
             (compile_value Σ a')
             (fun x : Malfunction.Ident.t =>
              match
                lookup (map (fun '(x0, v) => (x0, compile_value Σ v)) Γ')
                  (String.of_string x)
              with
              | Some v => v
              | None => fail "notfound"
              end))) (fun na0 => match lookup (add na a' Γ') (String.of_string na0) with
              | Some v => compile_value Σ v
              | None => fail "notfound"
              end)). eapply IHHeval3.
        -- intros na0. unfold Malfunction.Ident.Map.find. now rewrite (of_string_to_string).
        -- intros x.  unfold Malfunction.Ident.Map.find. rewrite lookup_add.
           unfold Malfunction.Ident.Map.add. unfold Malfunction.Ident.eqb.
           destruct (String.eqb_spec x (String.to_string na)).
           ++ subst. rewrite of_string_to_string. now rewrite eqb_refl.
           ++ destruct (eqb_spec (String.of_string x) na).
              ** subst. rewrite to_string_of_string in n. congruence.
              ** rewrite lookup_map. now destruct lookup.
  - (* lambda *)
    cbn.
    erewrite (functional_extensionality (fun x : Malfunction.Ident.t => match lookup (map (fun '(x0, v) => (x0, compile_value Σ v)) Γ) (String.of_string x) with
                                       | Some v => v
                                       | None => fail "notfound"
                                       end)).
    econstructor.
    intros x. unfold Malfunction.Ident.Map.find in *.
    specialize (HΓ (String.of_string x)).
    rewrite to_string_of_string in HΓ.
    rewrite HΓ, lookup_map.
    destruct (lookup _ (String.of_string x)); eauto.
  - (* let *) 
    cbn. econstructor.
    + now eapply IHHeval1.
    + econstructor. eapply IHHeval2.
      intros. unfold add, lookup in *. cbn in *.
      change (String.eqb na0 na) with (na0 == na) in *.
      destruct (eqb_spec na0 na).
      * subst. unfold Malfunction.Ident.Map.add, Malfunction.Ident.Map.find, Malfunction.Ident.eqb.
        now rewrite String.eqb_refl.
      * unfold Malfunction.Ident.Map.add, Malfunction.Ident.Map.find, Malfunction.Ident.eqb.
        destruct (String.eqb_spec (String.to_string na0) (String.to_string na)).
        -- eapply (f_equal String.of_string) in e. rewrite !of_string_to_string in e.
           congruence.
        -- rewrite <- HΓ. reflexivity.
  - (* case *)
    replace ((Malfunction.Mswitch
    (compile Σ discr,
     mapi_InP brs 0
       (fun (i : nat) (br0 : list BasicAst.name * EAst.term)
          (_ : In br0 brs) =>
        ([Malfunction.Tag (Compile.int_of_nat i)],
         Compile.Mapply_
           (Compile.Mlambda_
              (MCList.rev_map
                 (fun nm : BasicAst.name =>
                  String.to_string (BasicAst.string_of_name nm)) 
                 (fst br0), compile Σ (snd br0)),
            MCList.mapi
              (fun (i0 : nat) (_ : BasicAst.name) =>
               Malfunction.Mfield (Compile.int_of_nat i0, compile Σ discr))
              (MCList.rev (fst br0))))))))
              with (Mcase (compile Σ discr, map (fun '(brs, b) => (MCList.rev_map (fun x => String.to_string (BasicAst.string_of_name x)) brs, compile Σ b)) brs)).
    + destruct br as [br1 br2].
      eapply eval_case. 
      * cbn in *. eapply IHHeval1. eauto.
      * rewrite nth_error_map, e0. cbn. reflexivity.
      * cbn in *. clear - f n. rewrite MCList.rev_map_spec. eapply NoDup_rev. induction f.
        -- econstructor.
        -- cbn. inversion n; subst. econstructor. 2: eauto.
           intros (? & ? & ?) % in_map_iff.
           eapply (f_equal String.of_string) in H. rewrite !of_string_to_string in H.
           assert (forall n1 n, BasicAst.string_of_name n1 = BasicAst.string_of_name n -> n1 = n) by todo "string_of_name injective".
           eapply H1 in H as ->.
           eapply H2. clear - f H0.
           induction f; cbn in *. tauto. destruct H0 as [-> | ?]. inversion H; subst. eauto. subst. eauto.           
      * rewrite !map_length. cbn in *. rewrite MCList.rev_map_spec. rewrite rev_length, map_length. lia. 
      * cbn in *. eapply IHHeval2. intros na.
        rewrite lookup_multiple. 2: 
        clear - HΓ f e2.        
        induction br1 using rev_ind in nms, f, e2, br1, args |- *.
        -- inversion f. subst. cbn. now eapply HΓ.
        -- eapply Forall2_app_inv_l in f as (? & ? & ? & ? & ->). inversion H0. subst. inversion H5.
           subst. rewrite rev_app_distr.
           destruct args; rewrite app_length in e2; cbn in *; try lia.
           rewrite MCList.rev_map_spec. rewrite map_app.
           rewrite rev_app_distr. cbn.
           unfold Malfunction.Ident.Map.add, Malfunction.Ident.eqb.
           destruct (eqb_spec na y).
           ++ subst. now rewrite String.eqb_refl.
           ++ destruct (String.eqb_spec (String.to_string na) (String.to_string y)).
              ** eapply (f_equal (String.of_string)) in e0. rewrite !of_string_to_string in e0. congruence.
              ** rewrite <- IHbr1. 2: lia. 2: eauto.
                 rewrite MCList.rev_map_spec. reflexivity.
        -- eapply All_Forall.Forall2_length in f. rewrite rev_length. lia.
    + unfold Mcase. repeat f_equal.
      rewrite !MCList.mapi_map.
      rewrite !mapi_InP_spec.
      eapply MCList.mapi_ext. clear. intros n [nms br].
      f_equal. change Mapply_ with Compile.Mapply_.
      f_equal. change Mlambda_ with Compile.Mlambda_.
      f_equal. cbn [fst snd].
      rewrite MCList.rev_map_spec. cbn.
      rewrite !MCList.mapi_rev. 
      rewrite MCList.mapi_map.
      rewrite rev_spec.
      rewrite !MCList.mapi_rev. f_equal.
      eapply MCList.mapi_ext. intros.
      repeat f_equal. 
      all: now rewrite map_length.
  - (* recursion *)
    todo "recursion".
  - (* fix *)
    cbn.
    destruct ((MCList.nth_error_Some' mfix (Datatypes.length mfix - idx - 1))) as [_ Hnth].
    forward Hnth.
    assert (Datatypes.length mfix > 0) by todo "wf_mfix". 1: lia. 
    assert ({ l | Forall2 (fun d '(x, y, b) => d.(EAst.dname) = x /\ d.(EAst.dbody) = EAst.tLambda y b) mfix l /\
                  NoDup (map (fun x => fst (fst x)) l) }) as [l [Hl Hnodup]] by todo "consequence of wf_fixpoint".
    assert (map
      (fun x : EAst.def EAst.term =>
       (String.to_string (BasicAst.string_of_name (EAst.dname x)),
        compile Σ (EAst.dbody x))) mfix =(map
        (fun '(y0, t) =>
         let
         '(x, y) := y0 in
          (String.to_string (BasicAst.string_of_name x), compile Σ (EAst.tLambda y t))) l)) as Eqn.
      { clear -Hl. induction Hl; cbn.
        - reflexivity.
        - destruct y as [[] ]. destruct H as [<- ->].
          simp compile.
          repeat f_equal. eapply IHHl.
      }   
    unshelve econstructor.
    + refine (add_recs'' Γ_ (map (fun '(x, y, t) => (bytestring.String.to_string (BasicAst.string_of_name x), compile Σ (EAst.tLambda y t)) ) l) 
                            (map (fun '(x, y, t) => (bytestring.String.to_string (BasicAst.string_of_name x), (bytestring.String.to_string (BasicAst.string_of_name y), compile Σ t) )) l)).
    + rewrite MCList.map_InP_spec in *.
      unfold add_recs.
      rewrite <- Eqn.
      generalize (map
      (fun x : EAst.def EAst.term =>
       (String.to_string (BasicAst.string_of_name (EAst.dname x)),
        compile Σ (EAst.dbody x))) mfix) at 1 3 as allrecs.
      clear - Hl. intros.
      induction Hl in Γ_.
      * cbn. reflexivity.
      * cbn. 
        destruct y as [[y1 y3] y2]. cbn in *.
        destruct H as [<- ->]. cbn.
        simp compile.
        now rewrite IHHl.
    + econstructor. evar (v : SemanticsSpec.value).
      match goal with [ |- SemanticsSpec.eval _ _ _ ?fv ] =>
      replace fv with v end.
      subst v. econstructor.
      subst v. rewrite MCList.map_InP_spec.
      erewrite nth_error_nth.
      2: rewrite nth_error_map.
      2: now rewrite (projT2 Hnth). cbn.
      destruct Hnth as [[] Hx]; cbn.
      eapply All_Forall.Forall2_nth_error_Some in Hl as [ [[x' y'] t'] [H1 [<- H3]]]; eauto. cbn in *.
      subst. eapply nth_error_In in H1.
      erewrite add_recs''_spec.
      3:{ eapply in_map_iff. eexists (_, _, _). split. 2: eauto. f_equal. }
      2:{ clear - Hnodup. induction l; cbn.
          - econstructor.
          - inversion Hnodup; subst. econstructor. 2: eauto.
            destruct a as [[] ]. cbn in *.
            rewrite in_map_iff. intros ([? []] & ? & ?). cbn in *. subst.
            eapply in_map_iff in H0 as ([[]] & [=] & ?). subst.
            eapply (f_equal String.of_string) in H0. rewrite !of_string_to_string in H0.
            eapply H1. eapply in_map_iff. eexists (_, _, _). cbn.
            split. 2: eauto.
            assert (forall n1 n, BasicAst.string_of_name n1 = BasicAst.string_of_name n -> n1 = n) by todo "string_of_name injective".
            eauto.
      }
      rewrite <- Eqn.
      rewrite MCList.map2_length.
      rewrite PeanoNat.Nat.min_r.
      2: eapply All_Forall.Forall2_length in f; lia.
      eapply All_Forall.Forall2_nth_error_Some in f as f'. destruct f' as (? & ? & ?); eauto.
      erewrite TemplateToPCUICCorrectness.nth_error_map2; eauto.
      cbn. repeat f_equal.
      * eapply functional_extensionality. intros x0.
        rewrite <- (to_string_of_string x0).
        unfold Malfunction.Ident.Map.find in *.
        rewrite HΓ.
        rewrite lookup_map.
        rewrite of_string_to_string. now destruct lookup.
      * clear -f. induction f; cbn; repeat f_equal; eauto.
        now rewrite <- H.
      * eauto.
  - (* global *)
    unshelve econstructor.
    1: exact (compile Σ body).
    2:{ eapply IHHeval. reflexivity. }
    eapply in_flat_map.
    unfold EGlobalEnv.declared_constant in *.    
    eexists (_, _). split.
    + eapply lookup_env_In. cbn. eauto.
    + cbn. unfold compile_constant_decl. rewrite e. cbn. eauto.
  - (* constructor application *)
    cbn. econstructor.
    rewrite MCList.map_InP_spec, !map_app. cbn.
    eapply Forall2_app.
    + todo "switch to eval rule with Forall2".
    + repeat econstructor. now eapply IHHeval2.
  - cbn. repeat econstructor.
Qed.
Print Assumptions compile_correct.