Require Import ssreflect.
Require Import Malfunction.Malfunction.

Require Import ZArith Floats String.

Section list_notation.
Local Notation "A 'list'" := (list A) (at level 4).
(* type t = *)
Inductive t :=
| Mvar of nat
| Mlambda of Ident.t list * t
| Mapply of t * t list
| Mlet of binding list * t
| Mnum of numconst
| Mstring of string
| Mglobal of Longident.t
| Mswitch of t * (case list * t) list

(* Numbers *)
| Mnumop1 of unary_num_op * numtype * t
| Mnumop2 of binary_num_op * numtype * t * t
| Mconvert of numtype * numtype * t

(* Vectors *)
| Mvecnew of vector_type * t * t
| Mvecget of vector_type * t * t
| Mvecset of vector_type * t * t * t
| Mveclen of vector_type * t

(* Lazy *)
| Mlazy of t
| Mforce of t

(* Blocks *)
| Mblock of int * t list
| Mfield of int * t
with binding :=
| Unnamed of t | Named of Ident.t * t | Recursive of (Ident.t * t) list.
End list_notation.