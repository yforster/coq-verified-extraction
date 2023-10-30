From MetaCoq.Template Require Import Loader All Pretty.
From MetaCoq.Utils Require Import bytestring.
Require Import Nat List.

Open Scope bs.
Open Scope bool_scope.

From Coq Require Import Strings.Ascii.

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

Print BasicAst.context_decl.

Fixpoint print_type (t : term) :=
  match t with
  | tInd {| inductive_mind := (_, i) |} _ => uncapitalize i
  | tProd _ A B =>
      print_type A ++ " -> " ++ print_type B
  | _ => "aaa"
  end.

Fixpoint print_type_def def (t : term) :=
  match t with
  | tInd {| inductive_mind := (_, i) |} _ => uncapitalize i
  | tProd {| binder_name := nAnon |} A B =>
      print_type A ++ " -> " ++ print_type B
  | _ => def
  end.

Fixpoint print_types indna (ctx : context) :=
  match ctx with
  | [] => ""
  | [{| decl_type := T |}] => print_type_def indna T
  | {| decl_type := T |} :: l => print_type_def indna T ++ " * " ++ print_types indna l
  end.

Definition print_constructor indna  (na : ident) (ctx : context) :=
  na ++
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
  | (na, InductiveDecl m) :: l => print_inductive na.2 m ++ nl ++
                                                print_globals l
  | _ :: l => print_globals l
  end.

Definition print_mli na (p : program) :=
  print_globals p.1.(declarations) ++ nl ++ "val " ++ na ++ " : " ++ print_type p.2.

MetaCoq Quote Recursively Definition p := (nat -> bool).

Import MCMonadNotation.

Definition PrintMLI {A} (a : A) :=
  p <- tmQuoteRec A ;;
  t <- tmQuote a ;;
  match t with
  | tConst kn _ =>
      tmEval lazy (print_mli kn.2 p) >>= tmPrint
  | _ => tmFail "only constants supported"
  end.

Notation "'Print' 'mli' x" := (PrintMLI x) (at level 0).

MetaCoq Run Print mli Nat.ltb.
