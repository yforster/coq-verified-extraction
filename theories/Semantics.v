Require Import ssreflect.
From Malfunction Require Import Malfunction Interpreter.

Require Import ZArith Array.PArray List String Floats Lia.
Import ListNotations.

Set Default Goal Selector "!".

Inductive value :=
| Block of int * list value
| Vec of vector_type * list value
| Func of Ident.t * @Ident.Map.t value * t
| value_Int of inttype * Z
| Float of float
| Thunk of value
| fail of string
.

Fixpoint vtrans (s : value) : Interpreter.value :=
  match s with
  | Block (tag, vals) => Interpreter.Block (tag, Array_of_list (Interpreter.fail "") (map vtrans vals))
  | Vec (ty, vals) => Interpreter.Vec (ty, Array_of_list (Interpreter.fail "") (map vtrans vals))
  | Func (x, locals, e) => Interpreter.Func (fun v => interpret (Ident.Map.add x v (fun x => vtrans (locals x))) e)
  | value_Int (ty, i) => Interpreter.value_Int (ty, i)
  | Float f => Interpreter.Float f
  | Thunk v => Interpreter.Thunk (vtrans v)
  | fail x => Interpreter.fail x
  end.

Definition int_to_nat (i : int) : nat :=
  Z.to_nat (Int63.to_Z i).


Definition cond scr case : bool := 
  (match case, scr with
    | Tag n, Block (n', _) => Int63.eqb n n'
    | Deftag, Block _ => true
    | Intrange (min, max), value_Int (Int, n) => Z.leb (Int63.to_Z min) n && Z.leb n (Int63.to_Z max)
    | _, _ => false end).

Fixpoint find_match scr x : option t := match x with 
                                        | (cases, e) :: rest =>
                                            if List.existsb (cond scr) cases then
                                              Some e
                                            else
                                              find_match scr rest
                                        | [] => None end.


Definition Mklambda binders e :=
  match binders with [] => e | _ => Mlambda (binders, e) end.

Fixpoint add_recs' (locals : Ident.Map.t) allrecs recs  :=
  match recs with
  | [] => Some locals
  | (x, Mlambda (y :: more, e)) :: recs =>  
    match add_recs' locals allrecs recs with
    | Some locals => Some (Ident.Map.add x (Func (y, locals, Mlet ([Recursive allrecs], Mklambda more e))) locals)
    | None => None
    end
  | _ => None
  end.
Definition add_recs locals recs := add_recs' locals recs recs.

Unset Elimination Schemes.           
Inductive eval (locals : @Ident.Map.t value) : t -> value -> Prop :=
| eval_lambda_sing x e :
  eval locals (Mlambda ([x], e)) (Func (x, locals, e))
| eval_lambda x ids e :
  List.length ids > 0 ->
  eval locals (Mlambda (x :: ids, e)) (Func (x, locals, Mlambda (ids, e)))
| eval_app_sing x locals' e e2 v2 e1 v :
  eval locals e1 (Func (x, locals', e)) -> eval locals e2 v2 ->
  eval (Ident.Map.add x v2 locals') e v ->
  eval locals (Mapply (e1, [e2])) v
| eval_app e2 e1 v es :
  eval locals (Mapply (Mapply (e1, [e2]), es)) v ->
  eval locals (Mapply (e1, e2 :: es)) v
| eval_var id :
  eval locals (Mvar id) (Ident.Map.find id locals)
| eval_let_body e v : 
  eval locals e v -> eval locals (Mlet ([], e)) v
| eval_let_unnamed e1 v1 lts e2 v :
  eval locals e1 v1 ->
  eval locals (Mlet (lts, e2)) v ->
  eval locals (Mlet (Unnamed e1 :: lts, e2)) v 
| eval_let_named x e1 v1 lts e2 v :
  eval locals e1 v1 ->
  eval (Ident.Map.add x v1 locals) (Mlet (lts, e2)) v ->
  eval locals (Mlet (Named (x,e1) :: lts, e2)) v 
| eval_let_rec recs newlocals lts e2 v :
  add_recs locals recs = Some newlocals ->
  eval newlocals (Mlet (lts, e2)) v ->
  eval locals (Mlet (Recursive recs :: lts, e2)) v 
| eval_switch scr cases v v' e :
  eval locals scr v' ->
  find_match v' cases = Some e ->
  eval locals e v ->
  eval locals (Mswitch (scr, cases)) v
| eval_block tag es vals :
  Forall2 (eval locals) es vals ->
  eval locals (Mblock (tag, es)) (Block (tag, vals))
| eval_field idx b vals tag :
  eval locals b (Block (tag, vals)) ->
  Datatypes.length vals < Z.to_nat Int63.wB ->
  Datatypes.length vals <= int_to_nat max_length ->
  eval locals (Mfield (idx, b)) (nth (int_to_nat idx) vals (fail "")).

Lemma eval_ind :
forall P : Ident.Map.t -> t -> value -> Prop,
(forall (locals : Ident.Map.t) (x : Ident.t) (e : t),
 P locals (Mlambda ([x], e)) (Func (x, locals, e))) ->
(forall (locals : Ident.Map.t) (x : Ident.t) (ids : list Ident.t) (e : t),
 Datatypes.length ids > 0 ->
 P locals (Mlambda (x :: ids, e)) (Func (x, locals, Mlambda (ids, e)))) ->
(forall (locals : Ident.Map.t) (x : Ident.t) (locals' : Ident.Map.t) 
   (e e2 : t) (v2 : value) (e1 : t) (v : value),
 eval locals e1 (Func (x, locals', e)) ->
 P locals e1 (Func (x, locals', e)) ->
 eval locals e2 v2 ->
 P locals e2 v2 ->
 eval (Ident.Map.add x v2 locals') e v ->
 P (Ident.Map.add x v2 locals') e v -> P locals (Mapply (e1, [e2])) v) ->
(forall (locals : Ident.Map.t) (e2 e1 : t) (v : value) (es : list t),
 eval locals (Mapply (Mapply (e1, [e2]), es)) v ->
 P locals (Mapply (Mapply (e1, [e2]), es)) v -> P locals (Mapply (e1, e2 :: es)) v) ->
(forall (locals : Ident.Map.t) (id : Ident.t),
 P locals (Mvar id) (Ident.Map.find id locals)) ->
 (forall (locals : Ident.Map.t) (e : t) (v : value),
 eval locals e v -> P locals e v -> P locals (Mlet ([], e)) v) ->
(forall (locals : Ident.Map.t) (e1 : t) (v1 : value) 
   (lts : list binding) (e2 : t) (v : value),
 eval locals e1 v1 ->
 P locals e1 v1 ->
 eval locals (Mlet (lts, e2)) v ->
 P locals (Mlet (lts, e2)) v -> P locals (Mlet (Unnamed e1 :: lts, e2)) v) ->
(forall (locals : Ident.Map.t) (x : Ident.t) (e1 : t) 
   (v1 : value) (lts : list binding) (e2 : t) (v : value),
 eval locals e1 v1 ->
 P locals e1 v1 ->
 eval (Ident.Map.add x v1 locals) (Mlet (lts, e2)) v ->
 P (Ident.Map.add x v1 locals) (Mlet (lts, e2)) v ->
 P locals (Mlet (Named (x, e1) :: lts, e2)) v) ->
(forall (locals : Ident.Map.t) (recs : list (Ident.t * t))
   (newlocals : Ident.Map.t) (lts : list binding) 
   (e2 : t) (v : value),
 add_recs locals recs = Some newlocals ->
 eval newlocals (Mlet (lts, e2)) v ->
 P newlocals (Mlet (lts, e2)) v ->
 P locals (Mlet (Recursive recs :: lts, e2)) v) ->
(forall (locals : Ident.Map.t) (scr : t) (cases : list (list case * t))
   (v v' : value) (e : t),
 eval locals scr v' ->
 P locals scr v' ->
 find_match v' cases = Some e ->
 eval locals e v -> P locals e v -> P locals (Mswitch (scr, cases)) v) ->
(forall (locals : Ident.Map.t) (tag : int) (es : list t) (vals : list value),
    Forall2 (eval locals) es vals ->
    Forall2 (P locals) es vals ->
    P locals (Mblock (tag, es)) (Block (tag, vals))) ->
(forall (locals : Ident.Map.t) (idx : int) (b : t) (vals : list value) (tag : int),
 eval locals b (Block (tag, vals)) ->
 P locals b (Block (tag, vals)) ->
 Datatypes.length vals < Z.to_nat Int63.wB ->
 Datatypes.length vals <= int_to_nat max_length ->
 P locals (Mfield (idx, b)) (nth (int_to_nat idx) vals (fail ""))) ->
forall (locals : Ident.Map.t) (t : t) (v : value), eval locals t v -> P locals t v.
Proof.
  intros P H_lambda_sing H_lambda H_app_sing H_app H_var H_let_body H_let_unnamed H_let_named 
        H_let_rec H_switch H_block H_field.
  fix f 4. intros locals t v [ | | | | | | | | | | ? ? ? Hforall | ].
  1-10: eauto.
  - eapply H_block. 1: eauto. induction Hforall. 
    + econstructor.  
    + econstructor; eauto.
  - eapply H_field. 1: eauto. 1: eauto. all: lia.
Qed.
Set Elimination Schemes.

Axiom funext : forall A B, forall f g : A -> B, (forall x, f x = g x) -> f = g.

Definition int_of_nat n := Int63.of_Z (Z.of_nat n).

Lemma int_of_to_nat i :
  int_of_nat (int_to_nat i) = i.
Proof.
  unfold int_of_nat, int_to_nat.
  rewrite Z2Nat.id.
  1:eapply Int63.to_Z_bounded.
  now rewrite Int63.of_to_Z.
Qed.

Lemma int_to_of_nat i :
  (Z.of_nat i < Int63.wB)%Z ->
  int_to_nat (int_of_nat i) = i.
Proof.
  unfold int_of_nat, int_to_nat.
  intros H.
  rewrite Int63.of_Z_spec.
  rewrite Z.mod_small. 1:lia.
  now rewrite Nat2Z.id.
Qed.

Lemma Array_of_list'_get {A} s l (a : array A) i :
  i < s + List.length l ->
  (s + List.length l < Z.to_nat Int63.wB) ->
  s + List.length l <= int_to_nat (PArray.length a) ->
  PArray.get (Array_of_List' s l a) (int_of_nat i) =
    if (i <? s)%nat then
      a.[int_of_nat i]
    else
      nth (i - s) l (a.[int_of_nat i]).
Proof.
  intros Hl Hs Ha.
  induction l as [ | ? ? IHl] in s, i, a, Hl, Hs, Ha |- *.
  - destruct (Nat.ltb_spec i s).
    + cbn. reflexivity.
    + cbn. destruct (i - s); reflexivity.
  - rewrite IHl. 
    + cbn in Hl. lia.
    + cbn [Datatypes.length] in Hs. lia.
    + rewrite PArray.length_set. cbn [Datatypes.length] in Ha. lia.
    + fold (int_of_nat s). destruct (Nat.ltb_spec i s) as [H | H].
      * destruct (Nat.ltb_spec i (S s)) as [H0 | H0]; try lia.
        rewrite get_set_other.
        -- intros E. eapply (f_equal int_to_nat) in E.
           rewrite !int_to_of_nat in E.
           all:assert (H1 : s < Z.to_nat Int63.wB) by lia.
           all:eapply inj_lt in H1.
           all:rewrite Z2Nat.id in H1. all:lia. 
        -- reflexivity.
      * destruct (Nat.ltb_spec i (S s)); try lia.
        -- assert (i = s) by lia. subst.
           rewrite get_set_same.
           ++ eapply Int63.ltb_spec.
              1:eapply Z2Nat.inj_lt.
              1:eapply Int63.to_Z_bounded.
              1:eapply Int63.to_Z_bounded.
              fold (int_to_nat (int_of_nat s)).
              rewrite int_to_of_nat. 1:lia.
              unfold int_to_nat in Ha. lia.
           ++ cbn. destruct s. 1:reflexivity.
              rewrite minus_diag. reflexivity.
        -- cbn. destruct (i - s) as [ | n] eqn:E.
           ++ lia.
           ++ assert (H1 : i - S s = n) by lia. rewrite H1.
              eapply nth_indep.
              cbn in Hl. lia.
Qed.

Lemma Array_of_list_get {A} (a : A) l i :
  (i < Z.to_nat Int63.wB) ->
  (List.length l < Z.to_nat Int63.wB) ->
  List.length l <= int_to_nat max_length ->
  i < List.length l ->
  PArray.get (Array_of_list a l) (int_of_nat i) = nth i l a.
Proof.
  unfold Array_of_list. intros Hs Hl1 Hl Hi.
  rewrite Array_of_list'_get.
  + assumption.
  + lia. 
  + rewrite PArray.length_make.
    fold (int_of_nat (Datatypes.length l)).
    destruct (Int63.lebP (int_of_nat (Datatypes.length l)) max_length) as [ | n ].
    * rewrite int_to_of_nat.
      1:eapply Z2Nat.inj_lt. all: lia. 
    * destruct n.
      epose proof (int_to_of_nat (Datatypes.length l) _) as H.
      eapply Z2Nat.inj_le.
      1:eapply Int63.to_Z_bounded.
      1:eapply Int63.to_Z_bounded.
      unfold int_to_nat in H. rewrite H.
      unfold int_to_nat in Hl. exact Hl.
      Unshelve. all:lia.
  + destruct (Nat.ltb_spec i 0); try lia.
    rewrite Nat.sub_0_r.
    eapply nth_indep. lia.
Qed.

Lemma cond_correct scr x :
  cond scr x = Interpreter.cond (vtrans scr) x.
Proof. 
  now destruct x as [ | | [] ], scr as [ [] | [] | [[]] | [] | | | ]. 
Qed.

Lemma existsb_ext {A} (f g : A -> bool) l :
  (forall x, f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intros H; induction l; cbn; congruence.
Qed.

Lemma find_match_correct scr cases e ilocals :
  find_match scr cases = Some e ->
  Interpreter.find_match ilocals (vtrans scr) cases = interpret ilocals e.
Proof.
  induction cases as [ | a cases IHcases ]; cbn [find_match]; intros Eq.
  - inversion Eq.
  - destruct a.
    + cbn [Interpreter.find_match].
      destruct existsb eqn:E.
      * inversion Eq. subst.
        erewrite existsb_ext.
        2:{ intros. symmetry. eapply cond_correct. }
        now rewrite E.
      * erewrite existsb_ext.
        2:{ intros. symmetry. eapply cond_correct. }
        rewrite E. eauto.
Qed.

Lemma Array_of_list_get_again {A : Set} i s (l : list A) a :
  i >= s + List.length l ->
  s + List.length l < Z.to_nat Int63.wB ->
  i < Z.to_nat Int63.wB ->
  (Array_of_List' s l a).[int_of_nat i]  = PArray.get a (int_of_nat i).
Proof.
  induction l as [ | ? l IHl ] in s, i, a |- *; intros Hi Hs Ha.
  - cbn. reflexivity.
  - cbn. rewrite IHl. 
    + cbn in Hi. lia.
    + cbn [List.length] in Hs. lia. 
    + cbn [List.length] in Hs. lia.
    + rewrite get_set_other. 2:reflexivity.
      fold (int_of_nat s).
      intros H. eapply (f_equal int_to_nat) in H.
      rewrite !int_to_of_nat in H.
      * eapply inj_lt in Hs.
        rewrite Z2Nat.id in Hs. 1:cbn; lia.
        rewrite <- Hs.
        eapply inj_lt. cbn. lia.
      * eapply inj_lt in Ha.
        rewrite Z2Nat.id in Ha. 1:cbn; lia.
        lia.
      * subst. cbn in Hi. lia.
Qed.

Lemma Forall2_map {A B C} (f : A -> B) (g : C -> B) l1 l2 P :
  Forall2 P l1 l2 ->
  (forall x y, P x y -> f x = g y) ->
  map f l1 = map g l2.
Proof.
  induction 1; cbn; intros He; f_equal; eauto.
Qed.

Lemma Func_ext e1 e2 : (forall v, e1 v = e2 v) -> Interpreter.Func e1 = Interpreter.Func e2.
Proof.
  intros H. eapply funext in H.
  subst. reflexivity.
Qed.

Axiom todo : forall {A : Type}, A.

Lemma eval_correct locals e v ilocals :
  (forall x, ilocals x = vtrans (locals x)) ->
  eval locals e v -> interpret ilocals e = vtrans v.
Proof.
  intros Hloc.
  induction 1 as [ (* lambda_sing *) locals x e
                 | (* lambda *) locals x ids e H
                 | (* app_sing *) locals x locals' e e2 v2 e1 v H IHeval1 H0 IHeval2 H1 IHeval3
                 | (* app *) locals idx b vals tag H IHeval 
                 | (* var *) 
                 | (* let_body *) | (* let_unnamed *) | (* let_named *) | (* let_rec *)
                 | (* switch *) loc2 ? ? ? ? ? ? IHeval1 H0 ? IHeval2
                 | (* block *) loc3 IHeval2 
                 | (* field *) locals idx b vals tag H IHeval ] 
    in ilocals, Hloc |- *.
  1-6,11,12: cbn.
  11, 12: cycle 1.
  - eapply Func_ext. intros.
    f_equal. unfold Ident.Map.add. eapply funext. intros y.
    unfold Ident.eqb. destruct (String.eqb_spec y x).
    + reflexivity.
    + eauto.
  - destruct ids as [ | t ids ]; cbn in H. 1:inversion H. clear H.
      cbn. eapply Func_ext. intros ?.
      destruct match ids with
               | [] => (t, e)
               | _ :: _ => (t, Mlambda (ids, e))
               end eqn:E.
      rewrite E.
      eapply Func_ext. intros.
      repeat f_equal. 
      eapply funext. eauto. 
  - rewrite IHeval1; [eauto |].
    cbn. cbn in IHeval3.
    erewrite <- IHeval3 with (ilocals := fun x0 => vtrans (Ident.Map.add x v2 locals' x0)).
    2: reflexivity.
    f_equal.
    eapply funext. 
    intros x0. unfold Ident.Map.add.
    unfold Ident.eqb. destruct (String.eqb_spec x0 x).
    + eapply IHeval2. eauto.
    + reflexivity.
  - cbn in IHeval. eauto.
  - unfold Ident.Map.find. eauto.
  - eauto.
  - repeat f_equal. eapply Forall2_map.
    1:eassumption.
    intros. cbn in *. eauto.
  -  rewrite IHeval. 1:eauto.
    cbn. rewrite <- (int_of_to_nat idx).
    assert (int_to_nat idx < List.length vals \/ int_to_nat idx >= List.length vals)  as [Hl | Hl] by lia.
    + rewrite Array_of_list_get.
      * eapply Z2Nat.inj_lt.
        1:eapply Int63.to_Z_bounded; cbn. 1: lia.
        1:eapply Int63.to_Z_bounded.
      * rewrite map_length. assumption.
      * rewrite map_length. assumption.
      * now rewrite map_length.
      * change (Interpreter.fail "") with (vtrans (fail "")).
        rewrite int_of_to_nat.
        eapply map_nth.
    + rewrite nth_overflow.
      * rewrite int_to_of_nat. 1:unfold int_to_nat.
        1:rewrite Z2Nat.id. 1:eapply Int63.to_Z_bounded.
        1:eapply Int63.to_Z_bounded. lia.
      * unfold Array_of_list. rewrite Array_of_list_get_again.
        -- rewrite map_length. lia.
        -- rewrite map_length. cbn [plus]. assumption.
        -- unfold int_to_nat. eapply Z2Nat.inj_lt.
           1:eapply Int63.to_Z_bounded.
           1: cbn. 1: lia. 1:eapply Int63.to_Z_bounded.
        -- rewrite get_make. reflexivity.
  - cbn. eapply IHeval2. eauto.
  - cbn. eapply IHeval2. intros.
    rewrite IHeval1. 1:eauto.
    unfold Ident.Map.add, Ident.eqb.
    destruct (String.eqb_spec x0 x); eauto.
  - cbn [interpret].
    erewrite <- IHeval2; eauto.
    eapply find_match_correct in H0.
    rewrite <- H0.
    rewrite IHeval1; eauto.
Guarded. 
Unset Guard Checking.
  - cbn.  eapply IHeval. intros x.
    clear - H Hloc. revert H.
    unfold add_recs.
    rewrite newlocals_eqn.
    generalize recs at 1 3.
    intros allrecs H.
    induction recs as [ | (f, e) recs IH] in allrecs, ilocals, locals, H, newlocals, Hloc |- *.
    + cbn in H |- *. inversion H as [E]; subst. eapply Hloc.
    + cbn in H |- *. destruct e; try now inversion H.
      destruct p as (bindings, e).
      destruct bindings as [ | y ]; try now inversion H.
      destruct add_recs' as [ newlocals' | ] eqn:E; inversion H. subst. clear H. 
      unfold Ident.Map.add, Ident.eqb.
      destruct (String.eqb_spec x f).
      2: eapply IH; eauto.
      subst. cbn. clear IH.
      eapply Func_ext. intros v.
      enough (interpret
      (Ident.Map.add y v
         (fun x : Ident.t => newlocals interpret allrecs ilocals x))
      (Mklambda bindings e) = interpret
      (newlocals interpret allrecs
         (Ident.Map.add y v (fun x : Ident.t => vtrans (newlocals' x))))
      (Mklambda (bindings) e)) by (destruct bindings; eauto).
      f_equal. eapply funext in Hloc. subst. 
      (* This is true: y is not in allrecs.
          lemma 1: adding recs to locals and looking up an ident not in recs is equivalent to locals
          lemma 2: newlocals yields the same environment if passed locals1 and locals2 which are equal _outside of_ recs      
      *)
      apply todo.
Qed.
Set Guard Checking.