Require Import ssreflect.

Require Import ZArith Array.PArray List String Floats Lia.
Import ListNotations.

Require Malfunction.Malfunction Malfunction.SemanticsSpec.
Module N := Malfunction.Malfunction.
Module Spec := Malfunction.SemanticsSpec.
Import N.

From Malfunction Require Import Ast.

Set Default Goal Selector "!".

Inductive value :=
| Block of int * list value
| Vec of vector_type * list value
| Func of Ident.t * (list (Ident.t * value)) * t
| value_Int of inttype * Z
| Float of float
| Thunk of value
| fail of string
.

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

Definition scons {A} x (f : nat -> A) := 
  fun n =>
    match n with 
    | 0 => x
    | S n => f n
    end.

Fixpoint add_recs' (locals : list (Ident.t * value)) (allrecs recs : list (Ident.t * t)) : option (list (Ident.t * value)) :=
  match recs with
  | [] => Some locals
  | (x, Mlambda (y :: more, e)) :: recs =>  
     add_recs' (cons (x, Func (y, locals, Mlet ([Recursive allrecs], Mklambda more e))) locals) allrecs recs
  | _ => None
  end.
Definition add_recs locals recs := add_recs' locals recs recs.

Section eval.

Variable globals : list (Ident.t * t).

Unset Elimination Schemes.           
Inductive eval (locals : list (Ident.t * value)) : t -> value -> Prop :=
| eval_lambda_sing x e :
  eval locals (Mlambda ([x], e)) (Func (x, locals, e))
| eval_lambda x ids e :
  List.length ids > 0 ->
  eval locals (Mlambda (x :: ids, e)) (Func (x, locals, Mlambda (ids, e)))
| eval_app_sing x locals' e e2 v2 e1 v :
  eval locals e1 (Func (x, locals', e)) -> eval locals e2 v2 ->
  eval (cons (x, v2) locals') e v ->
  eval locals (Mapply (e1, [e2])) v
| eval_app e2 e1 v es :
  eval locals (Mapply (Mapply (e1, [e2]), es)) v ->
  eval locals (Mapply (e1, e2 :: es)) v
| eval_var n x v :
  nth_error locals n = Some (x, v) ->
  eval locals (Mvar n) v
| eval_let_body e v : 
  eval locals e v -> eval locals (Mlet ([], e)) v
| eval_let_unnamed e1 v1 lts e2 v :
  eval locals e1 v1 ->
  eval locals (Mlet (lts, e2)) v ->
  eval locals (Mlet (Unnamed e1 :: lts, e2)) v 
| eval_let_named x e1 v1 lts e2 v :
  eval locals e1 v1 ->
  eval (cons (x, v1) locals) (Mlet (lts, e2)) v ->
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
  eval locals (Mfield (idx, b)) (nth (int_to_nat idx) vals (fail ""))
| eval_global nm e v :
  In (nm, e) globals ->
  eval locals e v ->
  eval locals (Mglobal nm) v.

Lemma eval_ind :
forall P : (list (Ident.t * value)) -> t -> value -> Prop,
(forall (locals : (list (Ident.t * value))) (x : Ident.t) (e : t),
 P locals (Mlambda ([x], e)) (Func (x, locals, e))) ->
(forall (locals : (list (Ident.t * value))) (x : Ident.t) (ids : list Ident.t) (e : t),
 Datatypes.length ids > 0 ->
 P locals (Mlambda (x :: ids, e)) (Func (x, locals, Mlambda (ids, e)))) ->
(forall (locals : (list (Ident.t * value))) (x : Ident.t) (locals' : (list (Ident.t * value))) 
   (e e2 : t) (v2 : value) (e1 : t) (v : value),
 eval locals e1 (Func (x, locals', e)) ->
 P locals e1 (Func (x, locals', e)) ->
 eval locals e2 v2 ->
 P locals e2 v2 ->
 eval (cons (x, v2) locals') e v ->
 P (cons (x, v2) locals') e v -> P locals (Mapply (e1, [e2])) v) ->
(forall (locals : (list (Ident.t * value))) (e2 e1 : t) (v : value) (es : list t),
 eval locals (Mapply (Mapply (e1, [e2]), es)) v ->
 P locals (Mapply (Mapply (e1, [e2]), es)) v -> P locals (Mapply (e1, e2 :: es)) v) ->
(forall (locals : (list (Ident.t * value))) (n : nat) x v ,
  nth_error locals n = Some (x, v) ->
 P locals (Mvar n) v) ->
 (forall (locals : (list (Ident.t * value))) (e : t) (v : value),
 eval locals e v -> P locals e v -> P locals (Mlet ([], e)) v) ->
(forall (locals : (list (Ident.t * value))) (e1 : t) (v1 : value) 
   (lts : list binding) (e2 : t) (v : value),
 eval locals e1 v1 ->
 P locals e1 v1 ->
 eval locals (Mlet (lts, e2)) v ->
 P locals (Mlet (lts, e2)) v -> P locals (Mlet (Unnamed e1 :: lts, e2)) v) ->
(forall (locals : (list (Ident.t * value))) (x : Ident.t) (e1 : t) 
   (v1 : value) (lts : list binding) (e2 : t) (v : value),
 eval locals e1 v1 ->
 P locals e1 v1 ->
 eval (cons (x, v1) locals) (Mlet (lts, e2)) v ->
 P (cons (x, v1) locals) (Mlet (lts, e2)) v ->
 P locals (Mlet (Named (x, e1) :: lts, e2)) v) ->
(forall (locals : (list (Ident.t * value))) (recs : list (Ident.t * t))
   (newlocals : (list (Ident.t * value))) (lts : list binding) 
   (e2 : t) (v : value),
 add_recs locals recs = Some newlocals ->
 eval newlocals (Mlet (lts, e2)) v ->
 P newlocals (Mlet (lts, e2)) v ->
 P locals (Mlet (Recursive recs :: lts, e2)) v) ->
(forall (locals : (list (Ident.t * value))) (scr : t) (cases : list (list case * t))
   (v v' : value) (e : t),
 eval locals scr v' ->
 P locals scr v' ->
 find_match v' cases = Some e ->
 eval locals e v -> P locals e v -> P locals (Mswitch (scr, cases)) v) ->
(forall (locals : (list (Ident.t * value))) (tag : int) (es : list t) (vals : list value),
    Forall2 (eval locals) es vals ->
    Forall2 (P locals) es vals ->
    P locals (Mblock (tag, es)) (Block (tag, vals))) ->
(forall (locals : (list (Ident.t * value))) (idx : int) (b : t) (vals : list value) (tag : int),
 eval locals b (Block (tag, vals)) ->
 P locals b (Block (tag, vals)) ->
 Datatypes.length vals < Z.to_nat Int63.wB ->
 Datatypes.length vals <= int_to_nat max_length ->
 P locals (Mfield (idx, b)) (nth (int_to_nat idx) vals (fail ""))) ->
(forall (locals : (list (Ident.t * value))) (nm : Ident.t) (e : t) (v : value), In (nm, e) globals -> eval locals e v -> P locals e v -> P locals (Mglobal nm) v) ->
forall (locals : (list (Ident.t * value))) (t : t) (v : value), eval locals t v -> P locals t v.
Proof.
  intros P H_lambda_sing H_lambda H_app_sing H_app H_var H_let_body H_let_unnamed H_let_named 
        H_let_rec H_switch H_block H_field H_global.
  fix f 4. intros locals t v [ | | | | | | | | | | ? ? ? Hforall | | ].
  1-10, 13: eauto.
  - eapply H_block. 1: eauto. induction Hforall. 
    + econstructor.  
    + econstructor; eauto.
  - eapply H_field. 1: eauto. 1: eauto. all: lia.
Qed.
Set Elimination Schemes.

End eval.

Fixpoint names (x : t) {struct x} : list (Ident.t) :=
  match x with
  | Mvar v => []
  | Mlambda (xs, e) =>
      xs ++ names e
  | Mapply (f, vs) =>
      names f ++ flat_map names vs
  | Mlet (bindings, body) =>
      flat_map namesb bindings ++ names body
  | Mswitch (scr, cases) =>
      names scr ++ flat_map (fun '(_, e) => names e) cases
  | Mnumop1 (op, _, e) =>
      names e
  | Mnumop2 (op, _, e1, e2) =>
      names e1 ++ names e2
  | Mconvert (_, _, e) =>
      names e
  | Mvecnew (ty, len, def) =>
      names len ++ names def
  | Mvecget (ty, vec, idx) =>
      names vec ++ names idx 
  | Mvecset (ty, vec, idx, e) => names vec ++ names idx ++ names e
  | Mveclen (ty, vec) =>
      names vec
  | Mblock (idx, es) =>
      flat_map names es
  | Mfield (idx, b) =>
      names b
  | Mlazy e => names e
  | Mforce e => names e
  | _ => []
  end
with namesb (b : binding) : list (Ident.t) :=
       match b with
       | Unnamed e => names e
       | Named (x, e) => x :: names e
       | Recursive l => flat_map (fun '(x,e) => names e) l
       end.

Definition bound_names  (b : binding) : list (Ident.t) :=
  match b with
  | Unnamed e => []
  | Named (x, e) => [x]
  | Recursive l => map (fun '(x,e) => x) l
  end.

Fixpoint inb {A} (eqb : A -> A -> bool) (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: l => eqb x y || inb eqb x l
  end.

Definition disj : list Ident.t -> list Ident.t -> bool :=
fun l1 l2 =>
  forallb (fun x => negb (inb String.eqb x l2)) l1.

Fixpoint wf (x : t) {struct x} : bool :=
  match x with
  | Mvar v => true
  | Mlambda (xs, e) =>
      disj (names e) xs && wf e
  | Mapply (f, vs) =>
     wf f && forallb wf vs
  
   | Mlet (bindings, body) =>
      forallb wfb bindings && wf body && disj (flat_map bound_names bindings) (names body)
  
  | Mswitch (scr, cases) =>
      wf scr && forallb (fun '(_, e) => wf e) cases
  | Mnumop1 (op, _, e) =>
      wf e
  | Mnumop2 (op, _, e1, e2) =>
      wf e1 && wf e2
  | Mconvert (_, _, e) =>
      wf e
  | Mvecnew (ty, len, def) =>
      wf len && wf def
  | Mvecget (ty, vec, idx) =>
      wf vec && wf idx 
  | Mvecset (ty, vec, idx, e) => 
      wf vec && wf idx && wf e
  | Mveclen (ty, vec) =>
      wf vec
  | Mblock (idx, es) =>
      forallb wf es
  | Mfield (idx, b) =>
      wf b
  | Mlazy e => 
    wf e
  | Mforce e => wf e
  | _ => true
  end
with wfb (b : binding) : bool :=
  match b with
  | Unnamed e => wf e
  | Named (_, e) => wf e
  | Recursive l => forallb (fun '(x,e) => wf e) l
  end.

Fixpoint sapp {A} (l : list A) (env : nat -> A) : nat -> A :=
  match l with
  | [] => env
  | x :: l => sapp l (scons x env)
  end.

Fixpoint named (env : list string) (x : t) {struct x} : N.t :=
    match x with
    | Mvar v => 
       N.Mvar (nth v env EmptyString)
    | Mlambda (xs, e) =>
       N.Mlambda (xs, named (app (rev xs) env) e)
    | Mapply (f, vs) =>
        N.Mapply (named env f, map (named env) vs)
    | Mlet (bindings, body) =>
        N.Mlet (snd (fold_left (fun '(env, bindings) b => 
                                    let '(env', b') := namedb env b in
                                    (env', bindings ++ [b'] )) bindings (env, [])), 
                                    
                                named (rev (flat_map bound_names bindings) ++ env) body)
    | Mnum c => N.Mnum c
    | Mstring s => N.Mstring s 
    | Mglobal s => N.Mglobal s
    | Mswitch (scr, cases) =>
        N.Mswitch (named env scr, map (fun '(x, e) => (x, named env e)) cases)
    | Mnumop1 (op, ty, e) =>
        N.Mnumop1 (op, ty, named env e)
    | Mnumop2 (op, ty, e1, e2) =>
        N.Mnumop2 (op, ty, named env e1, named env e2)
    | Mconvert (ty1, ty2, e) =>
        N.Mconvert (ty1, ty2, named env e)
    | Mvecnew (ty, len, def) =>
        N.Mvecnew(ty, named env len, named env def)
    | Mvecget (ty, vec, idx) =>
        N.Mvecget (ty, named env vec, named env idx)
    | Mvecset (ty, vec, idx, e) => 
        N.Mvecset (ty, named env vec, named env idx, named env e)
    | Mveclen (ty, vec) =>
        N.Mveclen (ty, named env vec)
    | Mblock (idx, es) => 
        N.Mblock (idx, map (named env) es)
    | Mfield (idx, b) =>
        N.Mfield (idx, named env b)
    | Mlazy e => N.Mlazy (named env e)
    | Mforce e => N.Mforce (named env e)
    end
with namedb env (b : binding) : list string * N.binding :=
    match b with
    | Unnamed e => (env, N.Unnamed (named env e))
    | Named (x, e) => (x :: env, N.Named (x, named env e))
    | Recursive l => let nas := map fst l in 
      (app (rev nas) env, N.Recursive (map (fun '(x,e) => (x, named (app (rev nas) env) e)) l))
    end.
    
Compute (named []
(Mlambda (["z"%string; "x"%string], Mvar 0))).

Local Open Scope string_scope.

Compute (named []
  (Mlet
    ([ Named ("x1", (Mlambda (["z"],Mvar 0))) ;
       Named ("x2", Mvar 0)
     ],
    (Mvar 0))
)).

(* 
Goal prod (prod Ident.t (forall _ : nat, Spec.value)) N.t = prod (prod Malfunction.Ident.t (@Malfunction.Ident.Map.t Spec.value))
    Malfunction.t.
Proof. cbv. *)

Definition lookup : Ident.t -> list (Ident.t * value) -> option value :=
  fun id l => match find (fun x => String.eqb (fst x) id) l with Some (x, v) => Some v | None => None end.

#[bypass_check(guard)]
Fixpoint namedv (v : value) : Spec.value :=
  match v with
  | Block (idx, vs) => Spec.Block (idx, map namedv vs)
  | Vec (ty, vs) => Spec.Vec (ty, map (namedv) vs)
  | Func (x, locals, e) => Spec.Func (x, 
                                      fun id =>  
                                         match lookup id locals with 
                                         | Some v => namedv v 
                                         | _ => Spec.fail "notfound" 
                                         end,
                                      named (cons x (map fst locals)) e)
  | value_Int x => Spec.value_Int x
  | Float f => Spec.Float f
  | Thunk v => Spec.Thunk (namedv v)
  | fail s => Spec.fail s
  end.


Fixpoint wfv (v : value) : bool :=
  match v with
  | Block (idx, vs) => forallb wfv vs
  | Vec (ty, vs) => forallb wfv vs
  | Func (x, locals, e) => disj [x] (names e) && wf e
  | _ => true
  end.

Definition namede locals : @Ident.Map.t Spec.value :=
  fun id =>
  match lookup id locals with 
  | Some v => namedv v 
  | _ => Spec.fail "notfound" 
  end.

Lemma eval_ext glb l l' e e' v v' :
  l' = l -> e' = e -> v' = v ->
  Spec.eval glb l e v -> Spec.eval glb l' e' v'.
Proof.
  intros. subst. eauto.
Qed.

Lemma eval_correct glb locals e v :
  Forall (fun '(x,v) => wfv v = true) locals ->
  wf e = true ->
  eval glb locals e v ->
  Spec.eval (map (fun '(x,e) => (x, named [] e)) glb) (namede locals) (named (map fst locals) e) (namedv v).
Proof.
  intros Hloc Hwf Heval.
  induction Heval; cbn in Hwf.
  all: repeat match goal with [ H : (_ && _)%bool = true |- _ ] => 
     let Hwf1 := fresh "Hwf" in
     let Hwf2 := fresh "Hwf" in
     eapply Bool.andb_true_iff in H as [Hwf1 Hwf2] end.
  - cbn. econstructor.
  - cbn. eapply eval_ext, Spec.eval_lambda; eauto.
    now rewrite -app_assoc.
  - cbn. econstructor; eauto.
    fold namedv (namede locals').
    eapply eval_ext, IHHeval3; eauto.
    all: admit.
  - cbn. econstructor. eapply IHHeval; eauto.
    cbn. repeat rewrite Bool.andb_true_iff; firstorder.
  - cbn. eapply eval_ext, Spec.eval_var; eauto.
    erewrite nth_error_nth.
    2: now rewrite nth_error_map H.
    cbn. unfold namede.
    unfold Malfunction.Ident.Map.find.
    admit.
  - cbn. econstructor. eapply IHHeval; eauto.
  - cbn. eapply eval_ext, Spec.eval_let_unnamed; eauto.
    + repeat f_equal. admit.
    + eapply IHHeval2; eauto. cbn.
      rewrite !Bool.andb_true_iff; firstorder.
  - cbn. eapply eval_ext, Spec.eval_let_named; eauto.
    + repeat f_equal. admit.
    + eapply eval_ext, IHHeval2; eauto. 
      * admit.
      * cbn. do 3 f_equal.
        now rewrite <- !app_assoc.
      * econstructor; eauto. admit.
      * cbn. rewrite !Bool.andb_true_iff; firstorder.
  - cbn. eapply eval_ext, Spec.eval_let_rec; eauto.
    + repeat f_equal. admit.
    + admit.
    + eapply eval_ext, IHHeval; eauto.
      * cbn. do 3 f_equal.
        rewrite rev_app_distr -app_assoc. f_equal.
        admit.
      * admit.
      * cbn. rewrite !Bool.andb_true_iff; firstorder.
        admit.
  - cbn. econstructor; eauto.
    + admit.
    + eapply IHHeval2; eauto. admit.
  - cbn. econstructor; eauto.
    admit.
  - cbn. eapply eval_ext, Spec.eval_field.
    + reflexivity.
    + reflexivity.
    + admit.
    + eapply IHHeval; eauto.
    + admit.
    + admit.
  - admit.
Admitted.
