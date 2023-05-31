From Coq Require Import String.
From Ceres Require Import Ceres.
From Malfunction Require Import Pipeline Serialize.

From MetaCoq Require Import ETransform Common.Transform bytestring.
From MetaCoq.Template Require All Loader TemplateMonad.

Import Transform.

Definition Mlet_ '(l, b) :=
  match l with
  | nil => b
  | _ => Malfunction.Mlet (l, b)
  end.

Definition eval_malfunction (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  let t := Mlet_ (MCList.rev_map Malfunction.Named (fst p'), snd p') in
  time "Pretty printing"%bs (@to_string _ Serialize_t) t.

Definition eval_malfunction_sexp (cf := config.extraction_checker_flags) (p : Ast.Env.program)
  : Malfunction.t :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  let t := Mlet_ (MCList.rev_map Malfunction.Named (fst p'), snd p') in
  time "Pretty printing"%bs id t.


Definition compile_malfunction {cf : config.checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run malfunction_pipeline p (MCUtils.todo "wf_env and welltyped term"%bs) in
  time "Pretty printing"%bs (@to_string _ Serialize_program) p'.

Section something.

Import Loader All.
Import MCMonadNotation.

Definition extract {A : Type} (a : A) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_malfunction t) ;;
  (* tmMsg "Extraction to Malfunction:"%bs ;; *)
  tmMsg s ;; tmReturn tt.

Definition extract_def {A : Type} (a : A) (nm : string) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_malfunction_sexp t) ;;
  (* tmMsg "Extraction to Malfunction:"%bs ;; *)
  tmDefinition nm s.

From Malfunction Require Import Interpreter.

(* Compute (interpret (fun x => fail "empty"%string) def). *)

Definition interpret_mlf {A : Type} (a : A) :=
  t <- tmQuoteRec a ;;
  s <- tmEval lazy (eval_malfunction_sexp t) ;;
  v <- tmEval lazy (interpret (fun x => fail "empty"%string) s) ;;
  (* tmMsg "Extraction to Malfunction:"%bs ;; *)
  tmMsg (to_string v) ;; tmReturn tt.

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

MetaCoq Run Extraction (@exist nat (fun x => x = 0) 0 (@eq_refl _ 0)).

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
(* MetaCoq Run (interpret_mlf (forest_size arden)). *)

(*
with length - idx:

(let ($Coq.Init.Nat.add (lambda ($n) (apply (let (rec ($add (lambda ($n) (lambda ($m) (switch $n ((tag 0) $m) ((tag 1) (apply (lambda ($p) (block (tag 1) (apply $add $p $m))) (field 0 $n)))))))) $n) $n))) ($Malfunction.Tests.forest_size (lambda ($f) (apply (let (rec ($tree_size (lambda ($t) (switch $t ((tag 0) (apply (lambda ($a $f) (block (tag 1) (apply $forest_size $f))) (field 0 $t) (field 1 $t)))))) ($forest_size (lambda ($f) (switch $f ((tag 0) (apply (lambda ($b) (block (tag 1) (block (tag 0)))) (field 0 $f))) ((tag 1) (apply (lambda ($t $f1) (apply $Coq.Init.Nat.add (apply $tree_size $t) (apply $forest_size $f1))) (field 0 $f) (field 1 $f))))))) $tree_size) $f))) ($Malfunction.Tests.arden (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 0) (block (tag 1)))) (block (tag 0) (block (tag 0))))) (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 0) (block (tag 1)))) (block (tag 0) (block (tag 0))))) (block (tag 0) (block (tag 1)))))) (apply $Malfunction.Tests.forest_size $Malfunction.Tests.arden))

 *)

(* MetaCoq Run (extract_sexp (forest_size arden) "def"%bs). *)


(* 
MetaCoq Run (extract_sexp (ack 1 1) "def2"%bs).

Compute (interpret (fun x => fail "empty"%string) def).

Print def.
Compute def.

Definition parse := "(let ($Coq.Init.Nat.add (lambda ($n) (apply (let (rec ($add (lambda ($n) (lambda ($m) (switch $n ((tag 0) $m) ((tag 1) (apply (lambda ($p) (block (tag 1) (apply $add $p $m))) (field 0 $n)))))))) $add) $n))) ($Malfunction.Tests.forest_size (lambda ($f) (apply (let (rec ($tree_size (lambda ($t) (switch $t ((tag 0) (apply (lambda ($a $f) (block (tag 1) (apply $forest_size $f))) (field 0 $t) (field 1 $t)))))) ($forest_size (lambda ($f) (switch $f ((tag 0) (apply (lambda ($b) (block (tag 1) (block (tag 0)))) (field 0 $f))) ((tag 1) (apply (lambda ($t $f1) (apply $Coq.Init.Nat.add (apply $tree_size $t) (apply $forest_size $f1))) (field 0 $f) (field 1 $f))))))) $tree_size) $f))) ($Malfunction.Tests.arden (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 0) (block (tag 1)))) (block (tag 0) (block (tag 0))))) (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 1) (block (tag 0) (block (tag 0)) (block (tag 0) (block (tag 1)))) (block (tag 0) (block (tag 0))))) (block (tag 0) (block (tag 1)))))) (apply $Malfunction.Tests.forest_size $Malfunction.Tests.arden))
"%string.
 *)