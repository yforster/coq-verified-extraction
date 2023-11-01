Require Import Nat List.
From Coq Require Import Strings.Ascii.
From MetaCoq.Template Require Import Loader All Checker.
From MetaCoq.Utils Require Import bytestring.

Open Scope bool_scope.
Open Scope bs.

Definition newline : ascii := "010".
Definition nl : string := String.String (byte_of_ascii newline) String.EmptyString.

Definition uncapitalize_char (c : Byte.byte) : Byte.byte :=
  let n := Byte.to_nat c in
  if (65 <=? n)%nat && (n <=? 90)%nat then match Byte.of_nat (n + 32) with Some c => c | _ => c end
  else c.

Definition uncapitalize (s : bytestring.string) : bytestring.string :=
  match s with 
  | bytestring.String.EmptyString => bytestring.String.EmptyString
  | bytestring.String.String c s => bytestring.String.String (uncapitalize_char c) s
  end.

Definition capitalize_char (c : Byte.byte) : Byte.byte :=
  let n := Byte.to_nat c in
  if (97 <=? n)%nat && (n <=? 123)%nat then match Byte.of_nat (n - 32) with Some c => c | _ => c end
  else c.

Definition capitalize (s : bytestring.string) : bytestring.string :=
  match s with 
  | bytestring.String.EmptyString => bytestring.String.EmptyString
  | bytestring.String.String c s => bytestring.String.String (capitalize_char c) s
  end.

Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_graph t1 t2.

Notation "t === u" := (term_eqb t u) (at level 70).

Fixpoint print_type_def (names : list ident) (t : term) :=
  let def := "Obj.t (* not supported *)" in
  match t with
  | tInd {| inductive_mind := (_, i) |} _ => uncapitalize i
  | tProd {| binder_name := nNamed na |}  A B =>
      print_type_def names A ++ " -> " ++ print_type_def (("'" ++ uncapitalize na) :: names) B
  | tProd _ A B =>
      print_type_def names A ++ " -> " ++ print_type_def ("Obj.t (* insert correct type variable manually *)" :: names) B
  | tApp f args =>
      if f === <% list %> then
        match args with [A] => print_type_def names A ++ " list"
                   | _ => def
        end
      else 
      if f === <% prod %> then
        match args with [A; B] => "(" ++ print_type_def names A ++ " * " ++ print_type_def names B ++ ")"
                   | _ => def
        end
      else print_type_def names f ++ String.concat " " (map (print_type_def names) args)
  | tSort _ =>
      "Obj.t (* insert correct type variable manually *)"
  | tRel n =>
      nth n names " Obj.t (* dependent type *) "
  | t =>
      if t === <% PrimInt63.int %>
      then "int"
      else def
  end.

Definition print_type := print_type_def [].

Fixpoint print_types names (ctx : context) :=
  match ctx with
  | [] => ""
  | [{| decl_type := T |}] => print_type_def names T
  | {| decl_type := T |} :: l => print_type_def names T ++ " * " ++ print_types ("Obj.t (* dependent type *)" :: names) l
  end.

Definition print_constructor na (names : list ident) (ctx : context) :=
  capitalize na ++
  match ctx with
  | [] => " "
  | l => " of " ++ print_types names l
  end.

Fixpoint print_constructors (names : list ident) (l : list constructor_body) :=
  match l with
  | [] => ""
  | [c] => print_constructor c.(cstr_name) names (MCList.rev (fst (decompose_prod_assum [] c.(cstr_type))))
  | c :: l => print_constructor c.(cstr_name) names (MCList.rev (fst (decompose_prod_assum [] c.(cstr_type)))) ++ " | " ++ print_constructors names l
  end.

Fixpoint print_record (ctx : context) :=
  match ctx with
  | {| decl_name := {| binder_name := nNamed na |} ;
       decl_type := A
   |} :: ctx => na ++ " : " ++ print_type A ++ " ; " ++ print_record ctx
  | _ => ""
  end.

Definition print_record_bodies (bds : list one_inductive_body) :=
  match bds with
  | b :: _ => match  b.(ind_ctors) with
              [c] => print_record (rev (fst (decompose_prod_assum [] c.(cstr_type))))
            | _ => "<this is not a record>"
            end
  | _ => ""
  end.

Fixpoint print_inductive_bodies (names : list ident) (bds : list one_inductive_body) :=
  match bds with
  | [] => ""
  | [b] => b.(ind_name) ++ " = " ++ print_constructors names b.(ind_ctors) 
  | b :: bds => b.(ind_name) ++ " = " ++ print_constructors names b.(ind_ctors) ++ nl ++ "and " ++ print_inductive_bodies names bds 
  end.

Definition print_inductive na (m : mutual_inductive_body) :=
  match m.(ind_finite) with
  | Finite =>
      "type " ++ 
      print_inductive_bodies (MCList.rev_map ind_name m.(ind_bodies)) m.(ind_bodies)
  | BiFinite => "type " ++ na ++ " = " ++ "{ " ++ print_record_bodies m.(ind_bodies) ++ " }"
  | CoFinite => "<co recursive type not supported>"
  end.

Fixpoint print_globals (Σ : global_declarations) :=
  match Σ with
  | [] => ""
  | (na, InductiveDecl m) :: l =>
      if (na == (MPfile ["Datatypes"; "Init"; "Coq"], "list"))
        || (na == (MPfile ["Datatypes"; "Init"; "Coq"], "prod"))
      then print_globals l
      else print_inductive na.2 m ++ nl ++
             print_globals l
  | _ :: l => print_globals l
  end.

Definition print_mli na (p : program) :=
  print_globals (MCList.rev p.1.(declarations)) ++ nl ++ "val " ++ na ++ " : " ++ print_type p.2.
Import MCMonadNotation.

Definition PrintMLI {A} (a : A) :=
  A <- tmEval cbv A ;;
  p <- tmQuoteRec A ;;
  t <- tmQuote a ;;
  match t with
  | tConst kn _ =>
      tmEval cbv (print_mli kn.2 p) >>= tmMsg
  | _ => tmFail "only constants supported"
  end.

Notation "'Print' 'mli' x" := (PrintMLI x) (at level 0).

(* Record testrec := *)
(*   { *)
(*     testproj1 : nat; *)
(*     testproj2 : bool *)
(*   }. *)

(* Inductive ltree := Tree (a : nat) (b1 : ltree) (b2 : ltree) (d : bla) *)
(*                      with bla := a (n : nat) (b : blub) with blub := B (c : bla). *)

(* Definition test (A : Type) (u : testrec) (a : list A) (l : ltree) := a. *)

(* MetaCoq Run Print mli test. *)
(* (* MetaCoq Run Print mli Byte.to_nat. *) *)
