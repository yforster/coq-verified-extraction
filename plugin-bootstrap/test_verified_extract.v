From VerifiedMalfunction.Plugin Require Import Loader.
From MetaCoq.Template Require Import All.

From Coq Require Import String.
From Coq Require Vector.

Inductive three := ZERO | ONE | TWO | THREE.

Definition two := TWO.


Recursive Extraction plus.

MetaCoq Verified Extract two "two.mlf".

Axiom axiom : nat.

MetaCoq Verified Extract axiom "axiom.mlf".


(* From Malfunction Require Import Compile.
MetaCoq Verified Bypass Extract compile.

From Malfunction Require Import Pipeline.
MetaCoq Verified Extract Module compile_malfunction "compile_malfunction.mlf". *)

Definition many_list_functions := (@List.firstn, @List.filter, @List.skipn).

MetaCoq Verified Extract many_list_functions "list.mlf".

Definition prf := match conj I I with conj x y => (x,0) end.

MetaCoq Verified Extract prf "proof.mlf".

Definition test_add := plus 2 5.

MetaCoq Verified Extract test_add "add.mlf".


(* 
MetaCoq Quote Recursively Definition tm := compile_malfunction.
Definition test := compile_malfunction tm.
MetaCoq Verified Extract Module test "test.mlf". *)

MetaCoq Verified Extract (match cons THREE nil with cons x _ => x | _ => ONE end).
MetaCoq Verified Extract -help.

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

MetaCoq Verified Extract (ack 3 5).

Definition bla {A} (a : A) (b : bool) : b = true -> A :=
  match b with
  | true => fun _ => a
  | false => fun E => match E with end
  end.

MetaCoq Verified Extract @Vector.nil.

MetaCoq Verified Extract @Vector.cons.

Definition vtest :=
  fun (A : Type) (P : Vector.t A 0 -> Type) (H : P (Vector.nil A)) (v : Vector.t A 0) =>
match
  v as v0 in (Vector.t _ n)
  return (match n as x return (Vector.t A x -> Type) with
          | 0 => fun v1 : Vector.t A 0 => P v1
          | S n0 => fun _ : Vector.t A (S n0) => False -> IDProp
          end v0)
with
| @Vector.nil _ => H
| @Vector.cons _ _ _ _ => fun devil : False => False_ind IDProp devil
end.

MetaCoq Verified Extract vtest.

Arguments Vector.case0 : clear implicits.

MetaCoq Verified Extract @Vector.map.

MetaCoq Verified Extract (@exist nat (fun x => x = 0) 0 (@eq_refl _ 0)).

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := Vector.hd (vplus v01 v23).

MetaCoq Verified Extract @Vector.hd.

Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.
Arguments leaf {A}.
Arguments fcons {A}.
Arguments node {A}.

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).

MetaCoq Verified Extract (forest_size arden).
