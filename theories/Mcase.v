From Malfunction Require Import Malfunction SemanticsSpec.
From MetaCoq Require Import MCList.
Require Import List Lia.
Export ListNotations.
From MetaCoq Require Import bytestring BasicAst.

Definition Mapply_ '(e, l) :=
    match l with [] => e | _ => Mapply (e, l) end.

Definition Mlambda_ '(e, l) :=
    match e with [] => l | _ => Mlambda (e, l) end.

Definition Mcase : t * list (list Ident.t * t) -> t :=
 fun '(discr, brs) =>
   Mswitch (discr, mapi (fun i '(nms, b) => ([Malfunction.Tag (int_of_nat i)], Mapply_ (Mlambda_ (nms, b),
   mapi (fun i _ => Mfield (int_of_nat i, discr)) (nms)))) brs).

Definition add_multiple (nms : list Ident.t) (args : list value) locals :=
    fold_right (fun '(nm, arg) locals => Ident.Map.add nm arg locals) locals (map2 pair nms args). 

Definition Func_ nms locals b v :=
  match nms with
  | n :: nms => Func (n, locals, Mlambda_ (nms, b))
  | nil => v
  end.

Fixpoint Mnapply (l : t) (args : list t) :=
  match args with
    [] => l
  | a :: args => Mnapply (Mapply_ (l, [a])) args
  end.

Lemma Mnapply_app l args1 args2 :
  Mnapply l (args1 ++ args2) = Mnapply (Mnapply l args1) args2.
Proof.
  induction args1 in l, args2 |- *; cbn.
  - reflexivity.
  - now rewrite IHargs1.
Qed. 

Lemma eval_app_nested_ globals locals args l args' v :
  eval globals locals (Mnapply l (args' ++ args)) v ->
  eval globals locals (Mapply_ (Mnapply l args', args)) v.
Proof.
  induction args in args' |- *.
  - cbn. now rewrite app_nil_r.
  - cbn. intros H. specialize (IHargs (args' ++ [a])). destruct args.
    + now rewrite Mnapply_app in H.
    + econstructor. cbn in *.
      rewrite !Mnapply_app in IHargs.
      eapply IHargs. rewrite Mnapply_app in H. cbn in H.
      cbn. eauto.
Qed.

Require Import FunctionalExtensionality.

Lemma add_to_add_multiple nm y nms' values' locals :
  NoDup (nm :: nms') ->
  #|nms'| = #|values'| ->
  Ident.Map.add nm y (add_multiple nms' values' locals) =
  add_multiple (nms' ++ [nm]) (values' ++ [y]) locals.
Proof.
  intros H Hlen. induction nms' in values', H, Hlen, nm, y |- *.
  - destruct values'; cbn in Hlen; try lia. reflexivity.
  - destruct values'; cbn in Hlen; try lia.
    cbn.
    fold (add_multiple (nms') (values') locals).
    fold (add_multiple (nms' ++ [nm]) (values' ++ [y]) locals).
    rewrite <- IHnms'.
    3: lia. 2:{ inversion H; subst. econstructor; firstorder. inversion H3; eauto. }
    inversion H; subst. inversion H3; subst.
    assert (nm <> a) by (intros ->; firstorder).
    eapply functional_extensionality. intros x.
    unfold Ident.Map.add, Ident.eqb. 
    destruct (Strings.String.eqb_spec x nm), (Strings.String.eqb_spec x a); subst; congruence.
Qed.

Lemma NoDup_app {X} (l1 l2 : list X) :
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; inversion 1; subst; split; try econstructor; firstorder.
  rewrite in_app_iff in *; firstorder subst.
Qed.

Lemma eval_app_ globals locals args values values' nms' nms b v l :
  #|args| = #|nms| -> 
  #|nms'| = #|values'| ->
  NoDup (nms' ++ nms) ->
  Forall2 (eval globals locals) args values ->
  eval globals (add_multiple (nms' ++ nms) (values' ++ values) locals) b v ->
  eval globals locals l (Func_ nms (add_multiple nms' values' locals) b v) ->
  eval globals locals (Mapply_ (l, args)) v.
Proof.
  intros Hlen Hlenv Hdup H Heval Hl.
  eapply (eval_app_nested_ globals locals args l []). cbn.
  induction args in H, b, nms, nms', Hlen, Heval, v, values, values', Hl, l, Hdup, Hlenv |- *.
  - cbn. destruct nms; cbn in *; try lia. eauto.
  - destruct nms as [ | nm nms]; cbn in Hlen. 1: lia.
    inversion H. subst. rename H2 into Hx.
    destruct args.
    + destruct nms; cbn in Hlen; try lia. inversion H4; subst. clear H4.
      cbn. econstructor; eauto.
      rewrite add_to_add_multiple; eauto.
      eapply NoDup_incl_NoDup; eauto. rewrite app_length; cbn; lia. intros ? ?; rewrite in_app_iff in *; firstorder.
    + destruct nms as [ | nm' nms]. cbn in *; lia.
      cbn. eapply IHargs with (nms' := nms' ++ [nm]) (values' := values' ++ [y]).
      5:{ rewrite <- !app_assoc. cbn. eapply Heval. }
      1: cbn; eauto. 1:{ rewrite !app_length; cbn; lia. } 1:{ rewrite <- !app_assoc. cbn. eauto. } eauto.
      econstructor; [ eauto.. | ].
      cbn. destruct nms; rewrite add_to_add_multiple.
      * econstructor.
      * assert (nms' ++ [nm; nm'] = (nms' ++ [nm]) ++ [nm']) as Eq by now rewrite <- !app_assoc.
        rewrite Eq in Hdup. eapply NoDup_app in Hdup as [Hdup _].
        eapply NoDup_incl_NoDup; eauto. rewrite !app_length; cbn; lia. intros ? ?; rewrite !in_app_iff in *; firstorder subst.
      * lia.
      * econstructor. cbn. lia.
      * assert (nms' ++ nm :: nm' :: t0 :: nms = (nms' ++ [nm]) ++ (nm' :: t0 :: nms)) as Eq by now rewrite <- !app_assoc.
        rewrite Eq in Hdup. eapply NoDup_app in Hdup as [Hdup _].
        eapply NoDup_incl_NoDup; eauto. rewrite !app_length; cbn; lia. intros ? ?; rewrite !in_app_iff in *; firstorder subst.
      * lia.
Qed.

Lemma eval_apply_lambda globals locals args nms b values v : 
  #|args| = #|nms| -> 
  NoDup nms ->
  Forall2 (eval globals locals) args values ->
  eval globals (add_multiple nms values locals) b v ->
  eval globals locals (Mapply_ (Mlambda_ (nms, b), args)) v.
Proof.
  intros.
  eapply eval_app_ with (nms' := []) (values' := []); eauto.
  destruct nms.
  - cbn. eauto.
  - cbn. destruct nms.
    + econstructor; firstorder.
    + econstructor. cbn. lia.
Qed.

Axiom todo : forall {A}, A.
Ltac todo s := apply todo.

Lemma eval_case globals locals discr i args brs nms br v :
  eval globals locals discr (Block (int_of_nat i, args)) ->
  nth_error brs i = Some (nms, br) -> 
  NoDup nms ->
  #|args| = #|nms| ->
  eval globals (add_multiple nms args locals) br v ->
  eval globals locals (Mcase (discr, brs)) v.
Proof.
  intros Hdiscr Hnth Hdup Hlen Hbr.
  eapply eval_switch with (e := Mapply_ (Mlambda_ (nms, br), mapi (fun i _ => Mfield (int_of_nat i, discr)) (nms))).
  - eauto.
  - clear - Hnth. unfold mapi at 1. change i with (0 + i). 
    generalize 0 as n. intros n. induction brs as [ | [nms' br'] brs IH] in i, Hnth , nms, br, n |- *.
    + destruct i; inversion Hnth.
    + destruct i; cbn in Hnth.
      * inversion Hnth as [ ]. subst; clear Hnth. cbn.
        replace (n + 0) with n by lia.
        now rewrite Bool.orb_false_r, Int63.eqb_refl.
      * cbn [mapi mapi_rec]. unfold find_match.
        destruct existsb eqn:E.
        -- cbn in E. rewrite Bool.orb_false_r in E.
           eapply Int63.eqb_correct in E.
           eapply (f_equal int_to_nat) in E.
           rewrite !int_to_of_nat in E.
           lia. all: todo "int size"%bs.           
        -- fold find_match. erewrite <- (IH i _ _ _ (S n)). do 4 f_equal. lia.
  - eapply eval_apply_lambda. 2: eassumption. 3: eassumption. 1: now rewrite mapi_length.
    unfold mapi. change 0 with (#|@nil value|).
    revert Hdiscr. change args with ([] ++ args) at 1. generalize (@nil value) as args'. 
    intros args' Hdiscr.
    induction args in nms, Hlen, Hdup, Hdiscr, args' |- *.
    + destruct nms; inversion Hlen. cbn. econstructor.
    + destruct nms; inversion Hlen. cbn. econstructor.
      2: specialize IHargs with (args' := args' ++ [a]).
      2: rewrite app_length in IHargs. 2: cbn in IHargs.
      2: replace (S #|args'|) with (#|args'| + 1) by lia.
      2: eapply IHargs.
      * evar (v' : value).
        enough (a = v') as E. subst v'. rewrite E. econstructor.
        eapply Hdiscr. 1-2: todo "int size"%bs.
        subst v'. rewrite int_to_of_nat. 2: todo "int size"%bs.
        rewrite app_nth2, PeanoNat.Nat.sub_diag; [ reflexivity | lia].
      * now inversion Hdup.
      * assumption.
      * rewrite <- app_assoc. eapply Hdiscr. 
      Unshelve. eauto.
Qed.
Print Assumptions eval_case.