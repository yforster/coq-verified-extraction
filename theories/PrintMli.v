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

Fixpoint print_type_def def (t : term) :=
  match t with
  | tInd {| inductive_mind := (_, i) |} _ => uncapitalize i
  | tProd _ A B =>
      print_type_def def A ++ " -> " ++ print_type_def def B
  | tApp l [A] =>
      if l === <% list %> then
        print_type_def def A ++ " list"
      else def
  | tApp p [A;B] =>
      if p === <% prod %> then
        "(" ++ print_type_def def A ++ " * " ++ print_type_def def B ++ ")"
      else def
  | _ => def
  end.

Definition print_type := print_type_def "<NOTSUPPORTED>".

Fixpoint print_types indna (ctx : context) :=
  match ctx with
  | [] => ""
  | [{| decl_type := T |}] => print_type_def indna T
  | {| decl_type := T |} :: l => print_type_def indna T ++ " * " ++ print_types indna l
  end.

Definition print_constructor indna  (na : ident) (ctx : context) :=
  capitalize na ++
  match ctx with
  | [] => " "
  | l => " of " ++ print_types indna l
  end.

Fixpoint print_constructors indna (l : list constructor_body) :=
  match l with
  | [] => ""
  | [c] => print_constructor indna c.(cstr_name) (fst (decompose_prod_assum [] c.(cstr_type)))
  | c :: l => print_constructor indna c.(cstr_name) (fst (decompose_prod_assum [] c.(cstr_type))) ++ " | " ++ print_constructors indna l
  end.

Definition print_inductive na (m : mutual_inductive_body) :=
  "type " ++ na ++ " = " ++ 
  match m.(ind_bodies) with
  | b :: _ => print_constructors na b.(ind_ctors) 
  | _ => ""
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

MetaCoq Quote Recursively Definition p := (nat -> bool).
Import MCMonadNotation.

Definition PrintMLI {A} (a : A) :=
  A <- tmEval cbv A ;;
  p <- tmQuoteRec A ;;
  t <- tmQuote a ;;
  match t with
  | tConst kn _ =>
      tmEval cbv (print_mli kn.2 p) >>= tmPrint
  | _ => tmFail "only constants supported"
  end.

Definition test (u : nat * bool) := @nil (bool * nat).

Notation "'Print' 'mli' x" := (PrintMLI x) (at level 0).

MetaCoq Run Print mli test.
