From Malfunction.Plugin Require Import Loader.
From MetaCoq.Template Require Import All.

From Coq Require Import String.
From Coq Require Vector.

Inductive three := ZERO | ONE | TWO | THREE.

Definition two := TWO.

MetaCoq Extract Module two "two.mlf".

From Malfunction Require Import Compile.
MetaCoq Extract Module compile "compile.mlf".

From Malfunction Require Import Pipeline.
MetaCoq Extract Module compile_malfunction "compile_malfunction.mlf".
(* 
MetaCoq Quote Recursively Definition tm := compile_malfunction.

Definition test := compile_malfunction tm.
MetaCoq Extract Module test "test.mlf". *)

MetaCoq Extract (match cons THREE nil with cons x _ => x | _ => ONE end).
MetaCoq Extract -help.

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

MetaCoq Extract (ack 3 5).

MetaCoq Extract (@exist nat (fun x => x = 0) 0 (@eq_refl _ 0)).

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := Vector.hd (vplus v01 v23).

MetaCoq Extract vplus0123.

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

MetaCoq Extract (forest_size arden).