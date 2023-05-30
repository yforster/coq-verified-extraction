Require Import ssreflect.
From Malfunction Require Import Malfunction Interpreter.

Require Import ZArith Array.PArray List String Floats Lia.
Import ListNotations.

Set Default Goal Selector "!".

Class Heap := {
  pointer : Type;
  heapGen : forall (value : Type), Type;
  fresh : forall {value : Type}, heapGen value -> pointer -> heapGen value -> Prop;
  deref : forall {value : Type}, heapGen value -> pointer -> list value -> Prop;
  update : forall {value : Type}, heapGen value -> pointer -> list value -> heapGen value -> Prop
}.

Definition CanonicalHeap : Heap := 
{| pointer := int ;
   heapGen := fun value => (int * (int -> list value)) % type;
   fresh :=  fun _ '(ptr,h) fresh_ptr '(ptr',h') => Int63.ltb ptr fresh_ptr = true /\ fresh_ptr = ptr' /\ h = h' ;
   deref := fun _ '(_,h) ptr val => h ptr = val;
   update := fun _ '(_,h) ptr arr '(_,h') => forall ptr', h' ptr' = if Int63.eqb ptr ptr' then arr else h ptr |}. 

Record fresh_id : Type := freshid {}.

Inductive rec_value `{Heap} := 
  | RFunc of Ident.t * t
  | RThunk of pointer
  | Bad_recursive_value.

Inductive value `{Heap} :=
| Block of int * list value
| Vec of vector_type * pointer
| BString of vector_type * pointer
| Func of @Ident.Map.t value * Ident.t *  t
| RClos of @Ident.Map.t value * list rec_value * nat
| Lazy of @Ident.Map.t value * t
| value_Int of inttype * Z
| Float of float
| Thunk of pointer
| fail of string
| not_evaluated
.

Definition heap `{Heap} := heapGen value.

Class CompatiblePtr `{Heap} `{Interpreter.Heap} :=  
{ R_ptr : pointer -> Interpreter.pointer -> Prop }.

 From Coq Require Import Uint63.

 Definition list_of_array {A : Type} (a:array A) : list A :=
   (fix go (n : nat) (i : int) (acc : list A) :=
   match n with
   | 0 => acc
   | S n => go n (i - 1)%uint63 (cons a.[i] acc)
   end) (Z.to_nat (Uint63.to_Z (PArray.length a))) (PArray.length a - 1)%uint63 nil.
 
Definition isFunction `{Heap} (s : value) : bool :=
  match s with
  | Func _ => true
  | RClos _ => true
  | Lazy _ => true
  | _ => false
  end. 

Definition isThunk `{Heap} (s : value) : bool :=
  match s with
  | Thunk _ => true
  | _ => false
  end. 

Definition isBlock `{Heap} (s : value) : bool :=
  match s with
  | Block _ => true
  | _ => false
  end. 

Definition isNotEvaluated `{Heap} (s : value) : bool :=
  match s with
  | not_evaluated => true
  | _ => false
  end.  

Definition int_to_nat (i : int) : nat :=
  Z.to_nat (Int63.to_Z i).


Definition cond `{Heap} scr case : bool := 
  (match case, scr with
    | Tag n, Block (n', _) => Int63.eqb n n'
    | Deftag, Block _ => true
    | Intrange (min, max), value_Int (Int, n) => Z.leb (Int63.to_Z min) n && Z.leb n (Int63.to_Z max)
    | _, _ => false end).

Fixpoint find_match `{Heap} scr x : option t := match x with 
                                        | (cases, e) :: rest =>
                                            if List.existsb (cond scr) cases then
                                              Some e
                                            else
                                              find_match scr rest
                                        | [] => None end.


Definition Mklambda binders e :=
  match binders with [] => e | _ => Mlambda (binders, e) end.

Fixpoint mapi_ {A B} (f : nat -> A -> B) (l : list A) (n:nat) : list B :=
  match l with
    | [] => []
    | x :: l' =>  f n x :: mapi_ f l' (S n) 
  end.

Definition mapi {A B} (f : nat -> A -> B) l := mapi_ f l 0. 

Definition RFunc_build `{Heap} recs := 
    map (fun t =>
      match t with 
      Mlambda ([x], e) => RFunc (x , e)
    | Mlambda (x :: xs , e) => RFunc (x , Mlambda (xs , e))
    | _ => Bad_recursive_value
    end) 
    recs.

Definition add_recs `{Heap} locals (self : list Ident.t) rfunc := 
    mapi (fun n x => (x , RClos (locals, rfunc, n))) self.

Definition Forall2Array {A B:Type} (R : A -> B -> Prop) 
  (l:list A) (a:array B) default := 
    List.length l = int_to_nat (PArray.length a) /\
    forall i:int, int_to_nat i < List.length l -> R (nth (int_to_nat i) l default ) a.[i].

Inductive
  Forall2_acc {X A B : Type} (R : X -> A -> X -> B -> Prop) : X -> list A -> X -> list B -> Prop :=
    Forall2_acc_nil : forall x, Forall2_acc R x [] x []
    | Forall2_acc_cons : forall (x y z : X) (a : A) (b : B) 
                            (l : list A) (l' : list B) ,
                     R x a y b -> Forall2_acc R y l z l' -> Forall2_acc R x (a :: l) z (b :: l').

Section eval.

Variable _Heap:Heap.
Variable globals : list (Ident.t * value).

Unset Elimination Schemes.
Inductive eval (locals : @Ident.Map.t value) : heap -> t -> heap -> value -> Prop := 
| eval_lambda_sing h x e :
  eval locals h (Mlambda ([x], e)) h (Func (locals, x , e))
| eval_lambda h x ids e :
  List.length ids > 0 ->
  eval locals h (Mlambda (x :: ids, e)) h (Func (locals, x, Mlambda (ids, e)))
| eval_app_sing h h1 h2 h3 x locals' e e2 v2 e1 v :
  eval locals h e1 h1 (Func (locals', x , e)) -> 
  eval locals h1 e2 h2 v2 ->
  eval (Ident.Map.add x v2 locals') h2 e h3 v ->
  eval locals h (Mapply (e1, [e2])) h3 v
| eval_app_sing_rec h h1 h2 h3 mfix n y e locals' locals'' e2 v2 e1 v : (* todo *)
  eval locals h e1 h1 (RClos (locals', mfix , n)) -> 
  eval locals h1 e2 h2 v2 ->
  nth n mfix Bad_recursive_value = RFunc (y , e) -> 
  eval (Ident.Map.add y v2 locals'') h2 e h3 v ->
  eval locals h (Mapply (e1, [e2])) h3 v
| eval_app_fail h h1 e2 e1 v :
  eval locals h e1 h1 v ->
  isFunction v = false ->
  eval locals h (Mapply (e1, [e2])) h1 (fail "not a function:  evaluated to: ")
| eval_app h h1 e2 e1 v es :
  eval locals h (Mapply (Mapply (e1, [e2]), es)) h1 v ->
  eval locals h (Mapply (e1, e2 :: es)) h1 v
| eval_var h id :
  eval locals h (Mvar id) h (Ident.Map.find id locals)
| eval_let_body h h1 e v : 
  eval locals h e h1 v -> eval locals h (Mlet ([], e)) h1 v
| eval_let_unnamed h h1 h2 e1 v1 lts e2 v :
  eval locals h e1 h1 v1 ->
  eval locals h1 (Mlet (lts, e2)) h2 v ->
  eval locals h (Mlet (Unnamed e1 :: lts, e2)) h2 v 
| eval_let_named h h1 h2 x e1 v1 lts e2 v :
  eval locals h e1 h1 v1 ->
  eval (Ident.Map.add x v1 locals) h1 (Mlet (lts, e2)) h2 v ->
  eval locals h (Mlet (Named (x,e1) :: lts, e2)) h2 v 
| eval_let_rec h h1 recs newlocals lts e2 v :
  let self := map fst recs in
  let rfunc := RFunc_build (map snd recs) in
    newlocals = fold_left (fun l '(x,t) => Ident.Map.add x t l) 
                          (add_recs locals self rfunc) locals ->
    eval newlocals h (Mlet (lts, e2)) h1 v ->
    eval locals h (Mlet (Recursive recs :: lts, e2)) h1 v 
| eval_switch h h1 h2 scr cases v v' e :
  eval locals h scr h1 v' ->
  find_match v' cases = Some e ->
  eval locals h1 e h2 v ->
  eval locals h (Mswitch (scr, cases)) h2 v
| eval_block tag h h' es vals :
  Forall2_acc (eval locals) h es  h' vals ->
  List.length vals < int_to_nat max_length ->
  eval locals h (Mblock (tag, es)) h' (Block (tag, vals))
| eval_field h h' idx b vals tag :
  eval locals h b h' (Block (tag, vals)) ->
  Datatypes.length vals < Z.to_nat Int63.wB ->
  Datatypes.length vals <= int_to_nat max_length ->
  int_to_nat idx < List.length vals ->
  eval locals h (Mfield (idx, b)) h' (nth (int_to_nat idx) vals (fail ""))
| eval_field_fail h h' idx b v :
  eval locals h b h' v ->
  isBlock v = false ->
  eval locals h (Mfield (idx, b)) h' (fail "not a block")
| eval_thunk h h' h'' ptr e :
  let arr := [not_evaluated; Lazy (locals , e)] in
  fresh h ptr h' -> 
  update h' ptr arr h'' ->
  eval locals h (Mlazy e) h'' (Thunk ptr) 
| eval_force_done h h' e ptr vals lazy :
  eval locals h e h' (Thunk ptr) ->
  deref h' ptr vals ->
  List.length vals > 0 -> 
  nth 0 vals (fail "") = lazy ->
  isNotEvaluated lazy = false ->
  eval locals h (Mforce e) h' lazy 
| eval_force h h' h'' h''' ptr vals locals' e v :
  eval locals h e h' (Thunk ptr) ->
  deref h' ptr vals ->
  List.length vals = 2 ->
  isNotEvaluated (nth 0 vals (fail "")) = true -> 
  nth 1 vals (fail "") = Lazy (locals' , e) ->
  eval locals' h' e h'' v ->
  update h'' ptr [v; Lazy (locals' , e)] h''' ->
  eval locals h (Mforce e) h''' v  
| eval_force_fail h h' e v :
  eval locals h e h' v ->
  isThunk v = false ->
  eval locals h (Mforce e) h' (fail "not a lazy value")
| eval_global h nm v :
  In (nm, v) globals ->
  eval locals h (Mglobal nm) h v.

Lemma eval_inf :
forall P : Ident.Map.t -> heap -> t -> heap -> value -> Prop,
       (forall (locals : Ident.Map.t) (h : heap) (x : Ident.t) (e : t),
        P locals h (Mlambda ([x], e)) h (Func (locals, x, e))) ->
       (forall (locals : Ident.Map.t) (h : heap) (x : Ident.t)
          (ids : list Ident.t) (e : t),
        Datatypes.length ids > 0 ->
        P locals h (Mlambda (x :: ids, e)) h
          (Func (locals, x, Mlambda (ids, e)))) ->
       (forall (locals : Ident.Map.t) (h h1 h2 h3 : heap) 
          (x : Ident.t) (locals' : Ident.Map.t) (e e2 : t) 
          (v2 : value) (e1 : t) (v : value),
        eval locals h e1 h1 (Func (locals', x, e)) ->
        P locals h e1 h1 (Func (locals', x, e)) ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        eval (Ident.Map.add x v2 locals') h2 e h3 v ->
        P (Ident.Map.add x v2 locals') h2 e h3 v ->
        P locals h (Mapply (e1, [e2])) h3 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 h3 : heap)
          (mfix : list rec_value) (n : nat) (y : Ident.t) 
          (e : t) (locals' locals'' : Ident.Map.t) 
          (e2 : t) (v2 : value) (e1 : t) (v : value),
        eval locals h e1 h1 (RClos (locals', mfix, n)) ->
        P locals h e1 h1 (RClos (locals', mfix, n)) ->
        eval locals h1 e2 h2 v2 ->
        P locals h1 e2 h2 v2 ->
        nth n mfix Bad_recursive_value = RFunc (y, e) ->
        eval (Ident.Map.add y v2 locals'') h2 e h3 v ->
        P (Ident.Map.add y v2 locals'') h2 e h3 v ->
        P locals h (Mapply (e1, [e2])) h3 v) ->
       (forall (locals : Ident.Map.t) (h h1 : heap) (e2 e1 : t) (v : value),
        eval locals h e1 h1 v ->
        P locals h e1 h1 v ->
        isFunction v = false ->
        P locals h (Mapply (e1, [e2])) h1
          (fail "not a function:  evaluated to: ")) ->
       (forall (locals : Ident.Map.t) (h h1 : heap) 
          (e2 e1 : t) (v : value) (es : list t),
        eval locals h (Mapply (Mapply (e1, [e2]), es)) h1 v ->
        P locals h (Mapply (Mapply (e1, [e2]), es)) h1 v ->
        P locals h (Mapply (e1, e2 :: es)) h1 v) ->
       (forall (locals : Ident.Map.t) (h : heap) (id : Ident.t),
        P locals h (Mvar id) h (Ident.Map.find id locals)) ->
       (forall (locals : Ident.Map.t) (h h1 : heap) (e : t) (v : value),
        eval locals h e h1 v ->
        P locals h e h1 v -> P locals h (Mlet ([], e)) h1 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (e1 : t) (v1 : value) (lts : list binding) 
          (e2 : t) (v : value),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval locals h1 (Mlet (lts, e2)) h2 v ->
        P locals h1 (Mlet (lts, e2)) h2 v ->
        P locals h (Mlet (Unnamed e1 :: lts, e2)) h2 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (x : Ident.t) (e1 : t) (v1 : value) (lts : list binding) 
          (e2 : t) (v : value),
        eval locals h e1 h1 v1 ->
        P locals h e1 h1 v1 ->
        eval (Ident.Map.add x v1 locals) h1 (Mlet (lts, e2)) h2 v ->
        P (Ident.Map.add x v1 locals) h1 (Mlet (lts, e2)) h2 v ->
        P locals h (Mlet (Named (x, e1) :: lts, e2)) h2 v) ->
       (forall (locals : Ident.Map.t) (h h1 : heap)
          (recs : list (Ident.t * t)) (newlocals : Ident.Map.t)
          (lts : list binding) (e2 : t) (v : value),
        let self := map fst recs in
        let rfunc := RFunc_build (map snd recs) in
        newlocals =
        fold_left (fun (l : Ident.Map.t) '(x, t) => Ident.Map.add x t l)
          (add_recs locals self rfunc) locals ->
        eval newlocals h (Mlet (lts, e2)) h1 v ->
        P newlocals h (Mlet (lts, e2)) h1 v ->
        P locals h (Mlet (Recursive recs :: lts, e2)) h1 v) ->
       (forall (locals : Ident.Map.t) (h h1 h2 : heap) 
          (scr : t) (cases : list (list case * t)) 
          (v v' : value) (e : t),
        eval locals h scr h1 v' ->
        P locals h scr h1 v' ->
        find_match v' cases = Some e ->
        eval locals h1 e h2 v ->
        P locals h1 e h2 v -> P locals h (Mswitch (scr, cases)) h2 v) ->
       (forall (locals : Ident.Map.t) (tag : Malfunction.int) 
          (h h' : heap) (es : list t) (vals : list value),
        Forall2_acc (eval locals) h es h' vals ->
        Datatypes.length vals < int_to_nat max_length ->
        Forall2_acc (P locals) h es h' vals ->
        P locals h (Mblock (tag, es)) h' (Block (tag, vals))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (idx : Malfunction.int) (b : t) (vals : list value)
          (tag : Malfunction.int),
        eval locals h b h' (Block (tag, vals)) ->
        P locals h b h' (Block (tag, vals)) ->
        Datatypes.length vals < Z.to_nat Int63.wB ->
        Datatypes.length vals <= int_to_nat max_length ->
        int_to_nat idx < Datatypes.length vals ->
        P locals h (Mfield (idx, b)) h' (nth (int_to_nat idx) vals (fail ""))) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (idx : Malfunction.int) (b : t) (v : value),
        eval locals h b h' v ->
        P locals h b h' v ->
        isBlock v = false ->
        P locals h (Mfield (idx, b)) h' (fail "not a block")) ->
       (forall (locals : Ident.Map.t) (h h' h'' : heapGen value)
          (ptr : pointer) (e : t),
        let arr := [not_evaluated; Lazy (locals, e)] in
        fresh h ptr h' ->
        update h' ptr arr h'' -> P locals h (Mlazy e) h'' (Thunk ptr)) ->
       (forall (locals : Ident.Map.t) (h h' : heap) 
          (e : t) (ptr : pointer) (vals : list value) 
          (lazy : value),
        eval locals h e h' (Thunk ptr) ->
        P locals h e h' (Thunk ptr) ->
        deref h' ptr vals ->
        Datatypes.length vals > 0 ->
        nth 0 vals (fail "") = lazy ->
        isNotEvaluated lazy = false -> P locals h (Mforce e) h' lazy) ->
       (forall (locals : Ident.Map.t) (h h' h'' : heap)
          (h''' : heapGen value) (ptr : pointer) (vals : list value)
          (locals' : Ident.Map.t) (e : t) (v : value),
        eval locals h e h' (Thunk ptr) ->
        P locals h e h' (Thunk ptr) ->
        deref h' ptr vals ->
        Datatypes.length vals = 2 ->
        isNotEvaluated (nth 0 vals (fail "")) = true ->
        nth 1 vals (fail "") = Lazy (locals', e) ->
        eval locals' h' e h'' v ->
        P locals' h' e h'' v ->
        update h'' ptr [v; Lazy (locals', e)] h''' ->
        P locals h (Mforce e) h''' v) ->
       (forall (locals : Ident.Map.t) (h h' : heap) (e : t) (v : value),
        eval locals h e h' v ->
        P locals h e h' v ->
        isThunk v = false ->
        P locals h (Mforce e) h' (fail "not a lazy value")) ->
       (forall (locals : Ident.Map.t) (h : heap) (nm : Ident.t) (v : value),
        In (nm, v) globals -> P locals h (Mglobal nm) h v) ->
       forall (locals : Ident.Map.t) (h : heap) (t : t) 
         (h0 : heap) (v : value), eval locals h t h0 v -> P locals h t h0 v.
Proof.
  intros P H_lambda_sing H_lambda H_app_sing Happ_sing_rec H_app_fail H_app H_var H_let_body H_let_unnamed H_let_named 
        H_let_rec H_switch H_block H_field H_field_fail H_lazy H_force_done H_force H_force_fail H_global.
  fix f 6. intros locals h t h' v [| | | | | | | | | | | | ? ? ? ? ? Hforall | | | | | | | ].
  1-12, 15-20:eauto.
  - eapply H_block; eauto. induction Hforall; try econstructor; eauto. 
    eapply IHHforall. cbn in *. lia.  
  - eapply H_field. 1: eauto. 1: eauto. all: lia.
Qed.
Set Elimination Schemes.

Lemma int_of_to_nat i :
  Int63_of_nat (int_to_nat i) = i.
Proof.
  unfold Int63_of_nat, int_to_nat.
  rewrite Z2Nat.id.
  1:eapply Int63.to_Z_bounded.
  now rewrite Int63.of_to_Z.
Qed.

Lemma int_to_of_nat i :
  (Z.of_nat i < Int63.wB)%Z ->
  int_to_nat (Int63_of_nat i) = i.
Proof.
  unfold Int63_of_nat, int_to_nat.
  intros ?.
  rewrite Int63.of_Z_spec.
  rewrite Z.mod_small. 1:lia.
  now rewrite Nat2Z.id.
Qed.

Lemma Array_of_list'_get {A} s l (a : array A) i :
  i < s + List.length l ->
  (s + List.length l < Z.to_nat Int63.wB) ->
  s + List.length l <= int_to_nat (PArray.length a) ->
  PArray.get (Array_of_List' s l a) (Int63_of_nat i) =
    if (i <? s)%nat then
      a.[Int63_of_nat i]
    else
      nth (i - s) l (a.[Int63_of_nat i]).
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
    + fold (Int63_of_nat s). destruct (Nat.ltb_spec i s) as [H | H].
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
              fold (int_to_nat (Int63_of_nat s)).
              rewrite int_to_of_nat. 1:lia.
              unfold int_to_nat in Ha. lia.
           ++ cbn. destruct s. 1:reflexivity.
              rewrite Nat.sub_diag. reflexivity.
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
  (Array_of_list a l).[Int63_of_nat i] = nth i l a.

Proof.
  unfold Array_of_list. intros Hs Hl1 Hl Hi.
  rewrite Array_of_list'_get.
  + assumption.
  + lia. 
  + rewrite PArray.length_make.
    fold (Int63_of_nat (Datatypes.length l)).
    destruct (Int63.lebP (Int63_of_nat (Datatypes.length l)) max_length) as [ | n ].
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

Lemma existsb_ext {A} (f g : A -> bool) l :
  (forall x, f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intros H; induction l; cbn; congruence.
Qed.

Lemma Array_of_list_get_again {A : Set} i s (l : list A) a :
  i >= s + List.length l ->
  s + List.length l < Z.to_nat Int63.wB ->
  i < Z.to_nat Int63.wB ->
  (Array_of_List' s l a).[Int63_of_nat i]  = PArray.get a (Int63_of_nat i).
Proof.
  induction l as [ | ? l IHl ] in s, i, a |- *; intros Hi Hs Ha.
  - cbn. reflexivity.
  - cbn. rewrite IHl. 
    + cbn in Hi. lia.
    + cbn [List.length] in Hs. lia. 
    + cbn [List.length] in Hs. lia.
    + rewrite get_set_other. 2:reflexivity.
      fold (Int63_of_nat s).
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

End eval.


Inductive vrel `{CompatiblePtr} (globals: @Ident.Map.t Interpreter.value) 
    : value -> Interpreter.value -> Prop :=
  | vBlock : forall tag vals vals', Forall2Array (vrel globals) vals vals' (fail "") ->
      vrel globals (Block (tag, vals)) (Interpreter.Block (tag, vals'))
  | vVec : forall ty ptr ptr', R_ptr ptr ptr' -> vrel globals (Vec (ty, ptr)) (Interpreter.Vec (ty, ptr'))
  | vBString : forall ty ptr ptr', R_ptr ptr ptr' -> vrel globals (BString (ty, ptr)) (Interpreter.BString (ty, ptr'))
  | vFunc : forall f x locals locals' e,  
    (forall x, vrel globals (locals x) (locals' x)) ->
    (forall h v, interpret h globals (Ident.Map.add x v locals') e = f h v) -> 
    vrel globals (Func (locals,x,e)) (Interpreter.Func f)
(*  | vFunc : forall (f : Interpreter.heap -> Interpreter.value -> Interpreter.heap * Interpreter.value)  x locals locals' e,  
    (forall x, vrel eval (locals x) (locals' x)) ->
    (forall h h' ih v v' res, vrel eval v v' -> eval (Ident.Map.add x v locals) h e h' res -> 
      let (ih', res') := f ih v' in R_heap h' ih' /\ vrel eval res res') -> 
    vrel eval (Func (x,locals,e)) (Interpreter.Func f)*)
  | vRClos : forall f mfix n locals locals',  
    (forall x, vrel globals (locals x) (locals' x)) ->
    (*  (forall h v, interpret h globals (Ident.Map.add x v (add_all mfix E locals') locals') e = f h v) -> *)
    vrel globals (RClos (locals,mfix,n)) (Interpreter.Func f)
  | vInt : forall ty i , 
      vrel globals (value_Int (ty, i)) (Interpreter.value_Int (ty, i))
  | vFloat : forall f, 
      vrel globals (Float f) (Interpreter.Float f)
  | vThunk : forall ptr ptr', R_ptr ptr ptr' -> 
      vrel globals (Thunk ptr) (Interpreter.Thunk ptr')
  | vLazy : forall f e locals locals',  
    (forall x, vrel globals (locals x) (locals' x)) ->
    (forall h v, f h v = interpret h globals locals' e) -> 
    vrel globals (Lazy (locals, e)) (Interpreter.Func f)
  | vFail : forall s, 
      vrel globals (fail s) (Interpreter.fail s)
  | vNot_evaluated : vrel globals not_evaluated Interpreter.not_evaluated.

Definition vrel_locals `{CompatiblePtr} (globals: @Ident.Map.t Interpreter.value) 
  : Ident.Map.t -> Ident.Map.t -> Prop := fun locals ilocals => forall x, vrel globals (locals x) (ilocals x).

Class CompatibleHeap `{CompatiblePtr} :=  
  { R_heap : heap -> Interpreter.heap -> Prop;
    fresh_compat : forall h ptr h' ih, 
      R_heap h ih -> fresh h ptr h' -> 
      let (iptr,ih') := Interpreter.fresh ih in R_ptr ptr iptr /\ R_heap h' ih';
    update_compat : forall globals default h ih ptr ptr' h' v v', 
      R_heap h ih -> update h ptr v h' -> 
      R_ptr ptr ptr' -> Forall2Array (vrel globals) v v' default ->
      let ih' := Interpreter.update ih ptr' v' in R_heap h' ih';
    deref_compat : forall globals default h ih ptr ptr' vals, 
      R_heap h ih -> deref h ptr vals -> 
      R_ptr ptr ptr' -> 
      let vals' := Interpreter.deref ih ptr' in 
      Forall2Array (vrel globals) vals vals' default 
   }.


Lemma Forall2_acc_map {S S' A B B'} (R : S -> S' -> Prop) (RB : B -> B' -> Prop)
        (f : S' -> A -> S' * B') (P : S -> A -> S -> B -> Prop) x x' y l1 l2 :
  Forall2_acc P x l1 y l2 ->
  (forall x x' a b y, R x x' -> P x a y b -> let (y' , b') := f x' a in R y y' /\ RB b b') ->
  R x x' -> 
  let (y' , l') := map_acc f x' l1 in R y y' /\ Forall2 RB l2 l'.
Proof.
  intros H H'. revert x'. induction H; cbn; intros x' Hx; f_equal; eauto.
  specialize (H' _ _ _ _ _ Hx H). destruct (f _ _ ) as (s',b').
  destruct H'. specialize (IHForall2_acc _ H1). destruct (map_acc _ _ _).
  destruct IHForall2_acc. split; eauto.  
Qed.

Lemma cond_correct  `{CompatiblePtr} 
  globals' scr scr' x : vrel globals' scr scr' -> 
  cond scr x = Interpreter.cond scr' x.
Proof.
  now destruct x as [ | | [] ]; destruct 1. 
Qed.

Lemma find_match_correct `{CompatiblePtr}  scr scr' cases e h iglobals ilocals :
  vrel iglobals scr scr' ->
  find_match scr cases = Some e ->
  Interpreter.find_match Interpreter.interpret h iglobals ilocals scr' cases = interpret h iglobals ilocals e.
Proof.
  induction cases as [ | a cases IHcases ]; cbn [find_match]; intros rel Eq.
  - inversion Eq.
  - destruct a.
    cbn [Interpreter.find_match].
    destruct existsb eqn:E.
    * inversion Eq. subst.
      erewrite existsb_ext.
      2:{ intros. symmetry. eapply cond_correct. eauto.  }
      now rewrite E.
    * erewrite existsb_ext.
      2:{ intros. symmetry. eapply cond_correct. eauto. }
      rewrite E. eauto.
Qed.

Axiom todo : forall {A : Type}, A.

Ltac fail_case IHeval Hloc Hheap Heq := 
  let Hv := fresh "iv1" in cbn; specialize (IHeval _ _ Hloc Hheap); destruct interpret as [? ?];
  destruct IHeval as [? Hv]; destruct Hv; inversion Heq; split;eauto; econstructor.

Lemma vrel_add `{CompatiblePtr} iglobals x v iv locals ilocals : vrel iglobals v iv -> vrel_locals iglobals locals ilocals -> 
  vrel_locals iglobals (Ident.Map.add x v locals) (Ident.Map.add x iv ilocals).
Proof.
  intros Hv Hlocals nm. unfold Ident.Map.add. now destruct Ident.eqb.
Qed.

Lemma Array_of_list_S A default n a (l:list A) : 
  n < Datatypes.length l ->
  S (Datatypes.length l) <= int_to_nat max_length ->
  (Array_of_list default (a :: l)).[Int63_of_nat (S n)] = 
  (Array_of_list default l).[Int63_of_nat n].
Proof.
  intros. 
  repeat rewrite Array_of_list_get; cbn in *; try lia; eauto.
Qed. 

Lemma Array_of_list'_length A k (l:list A) a :
  PArray.length (Array_of_List' k l a) =
  PArray.length a.
Proof. 
  revert k a. induction l; [reflexivity|].
  intros; cbn. rewrite IHl. now rewrite PArray.length_set.
Qed.    

Lemma Array_of_list_length A default (l:list A) :
  Datatypes.length l < int_to_nat max_length -> 
  int_to_nat (PArray.length (Array_of_list default l)) =
  List.length l.
Proof.
  unfold Array_of_list. rewrite Array_of_list'_length.
  rewrite PArray.length_make. intro H. 
  assert (Hl: (Int63_of_nat (Datatypes.length l) ≤? max_length)%uint63 = true).
  { apply leb_spec. rewrite Int63.of_Z_spec. rewrite Z.mod_small; [cbn in *; lia |].
    cbn in *; lia. }
  rewrite Hl. apply int_to_of_nat. cbn in *; lia. 
Qed.    
  
Lemma Forall2_acc_length {X A B R x l y l'} : @Forall2_acc X A B R x l y l' -> List.length l = List.length l'.
Proof. 
  induction 1; cbn; eauto.
Qed.   

Lemma Forall2_length {A B P l l'} : @Forall2 A B P l l' -> List.length l = List.length l'.
Proof. 
  induction 1; cbn; eauto.
Qed.

Lemma isNotEvaluated_vrel `{CompatiblePtr} iglobals v v' b : 
  vrel iglobals v v' -> isNotEvaluated v = b <-> is_not_evaluated v' = b.
Proof.
  now destruct 1.
Qed.    

Axiom funext : forall A B, forall f g : A -> B, (forall x, f x = g x) -> f = g.

Lemma interpret_ilocals_proper `{CompatiblePtr} ih iglobals ilocals ilocals' e :
  (forall x, ilocals x = ilocals' x) ->
  interpret ih iglobals ilocals e = interpret ih iglobals ilocals' e.
Proof.
  intros Hlocal; apply funext in Hlocal. now subst.
Qed.  
  
Lemma eval_correct `{CompatibleHeap} 
  globals locals ilocals iglobals e h h' ih v :
  (forall nm val, In (nm, val) globals -> vrel iglobals val (iglobals nm)) ->
  vrel_locals iglobals locals ilocals ->
  R_heap h ih ->
  eval _ globals locals h e h' v -> 
  let (ih',iv) := interpret ih iglobals ilocals e in R_heap h' ih' /\ vrel iglobals v iv.  
Proof.
  rename H into _Heap; rename H0 into _iHeap; rename H1 into _CPtr; rename H2 into _CHeap. 
  intros Hglob Hloc Hheap.
  induction 1 as [ (* lambda_sing *) locals h x e
                 | (* lambda *) locals h x ids e H
                 | (* app_sing *) locals h1 h2 h3 h4 x locals' e e2 v2 e1 v H IHeval1 H0 IHeval2 H1 IHeval3
                 | (* app_fail *) locals h h' e2 e v Heval IHeval Heq
                 | (* app *) locals h h' e2 e1 v vals tag IHeval 
                 | (* var *) 
                 | (* let_body *) | (* let_unnamed *) | (* let_named *) | (* let_rec *)
                 | (* switch *) 
                 | (* block *)  
                 | (* field *) locals h h' idx b vals tag H IHeval | | | | | | ]
                 in ih, Hheap, ilocals, Hloc |- *. 
  (* eval_lambda_sing *) 
  - split; eauto. econstructor; eauto.
  (* eval_lambda *)
  - split; eauto. 
    destruct ids as [ | t ids ]; cbn in H. 1:inversion H. clear H.
    econstructor; eauto.  
  (* eval_app_sing *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    specialize (IHeval2 _ _ Hloc Hheap1). destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2].
    inversion Hiv1 ; subst. rewrite <- H7. clear H7 f Hiv1.
    specialize (IHeval3 (Ident.Map.add x iv2 locals'0) ih2). 
    destruct interpret as [ih3 iv3]; cbn in *.
    apply IHeval3; eauto. now apply vrel_add. 
  (* eval_app_fail *)
  - fail_case IHeval Hloc Hheap Heq.
  (* eval_app *)
  - now apply IHeval.
  (* eval_var *)
  - cbn; eauto.
  (* eval_let_body *)
  - now eapply IHeval.
  (* eval_let_unnamed *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    now eapply IHeval2. 
  (* eval_let_named *)
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    eapply IHeval2; eauto. now apply vrel_add. 
  (* eval_let_rec *)
  - cbn; eapply IHeval; eauto. intros x. clear IHeval.
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
      subst. cbn.  clear IH. econstructor; [eauto|].
      intros ih iv. cbn. 
      enough (
        interpret ih iglobals
        (Ident.Map.add y iv
           (fun x : Ident.t => newlocals (fun h => interpret h iglobals) allrecs ilocals x))
        (Mklambda bindings e) =
      interpret ih iglobals (Ident.Map.add y iv ilocals)
        (Mlet ([Recursive allrecs], Mklambda bindings e))) by (destruct bindings; eauto).
      generalize (Mklambda bindings e). clear e. intros e. cbn.
      clear E. apply interpret_ilocals_proper. intros.
      assert (~(In y (map fst allrecs))) by apply todo.
      unfold Ident.Map.add. 
      case_eq (Ident.eqb x y); cbn.
      * intro eqxy. rewrite eqb_eq in eqxy. subst. 
        enough (forall allrecs y l, ~ In y (map fst allrecs) ->
          newlocals (fun h : Interpreter.heap => interpret h iglobals) allrecs l y = l y).
         ** rewrite H0; eauto. unfold Ident.eqb. now rewrite String.eqb_refl.
         ** clear. intros. rewrite newlocals_eqn.
            generalize allrecs at 1. revert y H. 
            induction allrecs; cbn; intros; [reflexivity|].
            destruct a. unfold Ident.Map.add. 
            rewrite not_in_cons in H; destruct H. cbn in H. 
            assert (Ident.eqb y t = false) by now rewrite eqb_neq.
            rewrite H1. apply IHallrecs; eauto. 
      * intro neqxy. pose proof (H' := H). revert H' H. repeat rewrite newlocals_eqn.
        generalize allrecs at 2 3 5.
        induction allrecs.
        ** cbn. now rewrite neqxy.
        ** cbn. intro. 
           rewrite not_in_cons; intros.
           destruct a. unfold Ident.Map.add.
           case_eq (Ident.eqb x t).
          *** intro. destruct t0; try reflexivity.
            f_equal. apply funext. intro. apply funext.
            intro. assert (forall t0, interpret x0 iglobals
            (fun x2 : Ident.t =>
                newlocals (fun h : Interpreter.heap => interpret h iglobals) allrecs0 ilocals x2) t0 =
            interpret x0 iglobals
            (fun x2 : Ident.t =>
                newlocals (fun h : Interpreter.heap => interpret h iglobals) allrecs0
                  (fun y0 : string => if Ident.eqb y0 y then iv else ilocals y0) x2) t0) by apply todo.
            now rewrite H1.
        *** destruct H. intro; apply IHallrecs; eauto.  
  (* eval_switch *)
  - cbn.
    specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    erewrite find_match_correct; eauto. now apply IHeval2.
  (* eval_block *)
  - cbn. clear H. revert ih Hheap. induction H1. 
    + intros ih Hheap. split ; eauto. econstructor.
      split; [ reflexivity|]. cbn. lia.
    + intros ih Hheap. simpl. 
      specialize (H _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct H as [Hheap1  Hiv1]. 
      assert (Hlength: Datatypes.length l' < int_to_nat max_length) by (cbn in *; lia). 
      specialize (IHForall2_acc Hlength ih1 Hheap1).     
      unshelve epose proof (Forall2_acc_map R_heap (vrel iglobals)
        (fun (h : Interpreter.heap) (e : t) => interpret h iglobals ilocals e) _ _ _ _ _ _ H1 _ Hheap1).
      { clear -Hloc. intros. cbn in *. specialize (H0 ilocals x'). destruct interpret. apply H0; eauto. }
      set (p := map_acc _ ih1 l) in *. destruct p. destruct H as [Heahp2 Hl0]. split; eauto. 
      destruct IHForall2_acc as [? IHForall2_acc]. 
      assert (Hl: (Int63_of_nat (Datatypes.length l) ≤? max_length)%uint63 = true).
      { apply leb_spec. rewrite Int63.of_Z_spec.
        rewrite (Forall2_acc_length H1). rewrite Z.mod_small; [cbn in *; lia |]. cbn in *; lia. } 
      assert (Hl': (Int63_of_nat (S (Datatypes.length l)) ≤? max_length)%uint63 = true).
      { apply leb_spec. rewrite Int63.of_Z_spec. rewrite (Forall2_acc_length H1). rewrite Z.mod_small; [cbn in *; lia |].
        cbn in *; lia. } 
      rewrite Hl in IHForall2_acc. rewrite Hl'. inversion IHForall2_acc; subst. clear IHForall2_acc.  
      econstructor. destruct H3. split.
      * simpl. rewrite Array_of_list_length.
        { cbn. rewrite <- (Forall2_length Hl0). clear - H0; cbn in *; lia. }
        now rewrite (Forall2_length Hl0).
      * intros idx Hidx. rewrite <- (int_of_to_nat idx) at 2.
        pose proof (Hbounded := to_Z_bounded idx).
        destruct (int_to_nat idx).
        ** simpl. pose Int63.wB_pos. rewrite Array_of_list_get; try (cbn; lia).
          ++ cbn in H0. rewrite (Forall2_length Hl0) in H0. clear - H0; cbn in *; lia. 
          ++ cbn in H0. rewrite (Forall2_length Hl0) in H0. clear - H0; cbn in *; lia. 
          ++ eauto.
        ** simpl. rewrite Array_of_list_S. 
           ++ cbn; cbn in Hidx. rewrite <- (Forall2_length Hl0). lia.
           ++ cbn; cbn in H0. rewrite <- (Forall2_length Hl0). lia.
           ++ specialize (H3 (Int63_of_nat n)). 
              rewrite int_to_of_nat in H3.
              { cbn; cbn in Hidx; cbn in H0. lia. }
              eapply H3. cbn in Hidx; lia.  
  (* eval_field *)    
  - cbn. specialize (IHeval _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1].
    split; eauto. inversion Hiv1; subst. clear Hiv1. destruct H6 as [? H5]. 
    now eapply (H5 idx).  
  (* eval_field_fail *)    
  - fail_case IHeval Hloc Hheap H0.
  (* eval_lazy *)  
  - cbn. pose proof (fresh_compat _ _ _ _ Hheap H).
    set (Interpreter.fresh ih) in *. destruct p.
    destruct H1; split; [| now econstructor].
    eapply update_compat with (default := fail ""); eauto. split; [reflexivity|].
    intros idx Hidx. rewrite <- (int_of_to_nat idx). destruct int_to_nat. 
    * cbn. econstructor; eauto.
    * cbn in Hidx. lia.
  (* eval_force_done *)  
  - cbn. specialize (IHeval _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval as [Hheap1  Hiv1]. 
    inversion Hiv1; subst; clear Hiv1.
    pose proof (deref_compat iglobals (fail "") _ _ _ _ _ Hheap1 H0 H5).
    destruct H1 as [? Hderef]. pose proof (Hderef (int_of_nat 0) H2).
    cbn in H4. rewrite isNotEvaluated_vrel in H3; eauto. 
    now destruct is_not_evaluated; inversion H3.
  (* eval_force *)  
  - cbn; specialize (IHeval1 _ _ Hloc Hheap). destruct interpret as [ih1 iv1]; destruct IHeval1 as [Hheap1  Hiv1].
    inversion Hiv1; subst; clear Hiv1.
    pose proof (deref_compat iglobals (fail "") _ _ _ _ _ Hheap1 H0 H7).
    destruct H6 as [? Hderef]. pose proof (Hderef (int_of_nat 0)).
    cbn in H8. rewrite isNotEvaluated_vrel in H1; [eapply H8; lia|]. 
    destruct is_not_evaluated; inversion H1. clear H1. rewrite H3 in Hderef. 
    pose proof (Hderef (int_of_nat 1) (ltac:(eauto))). cbn in H1.
    rewrite H2 in H1. set _.[1] in *.  inversion H1; subst; clear H1.
    rewrite H13.
    specialize (IHeval2 _ _ H12 Hheap1). destruct interpret as [ih2 iv2]; destruct IHeval2 as [Hheap2  Hiv2].
    split; eauto. 
    eapply update_compat with (default := fail ""); eauto. split; cbn.   
    * rewrite PArray.length_set. lia.
    * intro i. pose proof (int_of_to_nat i). destruct (int_to_nat i); [| destruct  n].
      + subst. intros _. rewrite get_set_same; eauto.
        rewrite <- (int_of_to_nat (PArray.length _)). rewrite <- H6. 
        rewrite H3. cbn; lia.
      + subst; intros _. rewrite get_set_other; [now apply eqb_false_spec|]. cbn.
        fold y. rewrite <- H11. econstructor; eauto.
      + lia. 
  (* eval_force_fail *)  
  - fail_case IHeval Hloc Hheap H0.
  - cbn. split; eauto. 
  Qed.
Set Guard Checking.


(*  Lemma vtrans_inj v v' : vtrans v = vtrans v' -> v = v'.
  Admitted. 
  Lemma apD {A B} {f g : forall a:A, B a} : f = g -> forall x, f x = g x. 
  now destruct 1.
  Defined.  *)

  Lemma interp_correct iglobals globals locals e v ilocals :
    (forall x, vrel iglobals (ilocals x) (locals x)) ->
    vrel (interpret ilocals e) v -> eval globals locals e v.
  induction e; intro Hlocal; cbn in *. 
  - intros Hvar. unfold Ident.Map.find in Hvar. rewrite Hlocal in Hvar.
    apply vtrans_inj in Hvar. subst. econstructor. 
  - intros Hlambda. destruct p as [xs e]. induction xs; cbn in *.
    * admit.
    * destruct xs.
      + destruct v; cbn in Hlambda; try destruct p; try now inversion Hlambda.
        destruct p. inversion Hlambda. clear Hlambda.
        pose proof (Hlambda := apD H0 a). 
        
         H0. pose (ap )
        f_equal
        
        eapply eval_lambda_sing. 
           

  destruct v. inversion Hvar.  eapply eval_var. 


