From Coq Require Import String.
From Ceres Require Import Ceres.
From Malfunction Require Import Pipeline Serialize.

From MetaCoq Require Import ETransform Transform bytestring.
From MetaCoq.Template Require All Loader TemplateMonad.

Import Transform.

Definition eval_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : String.string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  let t := Malfunction.Mlet (MCList.rev_map Malfunction.Named (fst p'), snd p') in
  time "Pretty printing"%bs (@to_string _ Serialize_t) t.

Definition compile_malfunction {cf : config.checker_flags} (p : Ast.Env.program)
  : String.string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (@to_string _ Serialize_program) p'.

Section something.

Import Loader All.
Import MCMonadNotation.

Definition extract {A : Type} (a : A) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_malfunction t) ;;
  (* tmMsg "Extraction to Malfunction:"%bs ;; *)
  tmMsg (String.of_string s) ;; tmReturn tt.

End something.

Notation "'Extraction' a" :=
  (extract a) (at level 1, a at level 2).

Inductive three := ZERO | ONE | TWO | THREE.

MetaCoq Run Extraction (match cons THREE nil with cons x _ => x | _ => ONE end).
MetaCoq Run Extraction plus.

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

MetaCoq Run Extraction (ack 3 5).

MetaCoq Run Extraction (@exist _ _ 0 (@eq_refl _ 0) : {x : nat | x = 0}).

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := Vector.hd (vplus v01 v23).

MetaCoq Run Extraction vplus0123.

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

MetaCoq Run Extraction (forest_size arden).
