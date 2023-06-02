
(* begin hide *)
From Coq Require Import
  List ZArith Ascii String.

From Ceres Require Import
  CeresString
  CeresS.
(* end hide *)

From MetaCoq Require Import bytestring.

Coercion Tree.string : string >-> Tree.t.
Coercion byte_to_string (b : Byte.byte) := String.String b String.EmptyString.
Infix "^" := Tree.append.
Open Scope bs.

(** Helper for [string_of_sexp]. *)
Local Definition dstring_of_sexp {A} (dstring_A : A -> Tree.t)
  : sexp_ A -> Tree.t
  := fix _to_dstring (x : sexp_ A) : Tree.t :=
    match x with
    | Atom_ a => dstring_A a
    | List nil => "()"
    | List (x :: xs) =>
        "("
        ^ _to_dstring x ^
             (fold_right (fun x y => " "%byte ^ _to_dstring x ^ y)%dstring
                (")")
                xs)
    end%dstring.

(** Convert a [sexp] to a [string]. *)
Definition string_of_sexp_ {A} (string_A : A -> string) (x : sexp_ A) : Tree.t :=
  dstring_of_sexp string_A x.

(** Convert an [atom] to a [string]. *)
Definition string_of_atom (a : atom) : string :=
  match a with
  | Num n => String.of_string (string_of_Z n)
  | Str s => String.of_string (escape_string s)
  | Raw s => String.of_string s
  end.

(** Convert a [sexp] to a [string]. *)
Definition string_of_sexp : sexp -> string :=
  fun s => Tree.to_string (string_of_sexp_ string_of_atom s).
