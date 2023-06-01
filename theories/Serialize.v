Require Import String Ascii Bool Arith.
Require Import Malfunction.Malfunction.

Require Import Ceres.Ceres Ceres.CeresString.

Local Open Scope sexp.
Local Open Scope string.

Fixpoint _escape_ident (_end s : string) : string :=
  match s with
  | ""%string => _end
  | (c :: s')%string => let escaped_s' := _escape_ident _end s' in if ("'" =? c)%char2 then ("_" :: escaped_s')%string else (c :: escaped_s')%string
  end.

#[export] Instance Serialize_Ident : Serialize Ident.t :=
  fun a => Atom (append "$" (_escape_ident "" (bytestring.String.to_string a))).

#[export] Instance Integral_int : Integral int :=
  fun n => (Int63.to_Z n).

(* #[export] Instance Serialize_int : Serialize int := *)
(*   fun i => to_sexp (Int63.to_Z i). *)

#[export] Instance Serialize_numconst : Serialize numconst :=
  fun a => match a with
        | numconst_Int i => to_sexp i
        | numconst_Bigint x => Atom (append (CeresString.string_of_Z x) ".bigint")
        | numconst_Float64 x => Atom "not supported"
        end.

Definition Cons x (l : sexp) :=
  match l with
  | List l => List (x :: l)
  | x => x
  end.

Definition rawapp (s : sexp) (a : string) :=
  match s with
  | Atom_ (Raw s) => Atom (Raw (append s a))
  | x => x
  end.

#[export] Instance Serialize_case : Serialize case :=
  fun a => match a with
        | Tag tag => [Atom "tag"; Atom (Int63.to_Z tag)]
        | Deftag => Atom "_"
        | Intrange (i1, i2) => [ to_sexp i1 ; to_sexp i2  ]
        end.

#[export] Instance Serialize_unary_num_op : Serialize unary_num_op :=
  fun a => match a with Neg => Atom "neg" | Not => Atom "what to insert for Not?" end.

Definition numtype_to_string (n : numtype) :=
  match n with
  | embed_inttype x => match x with
                      | Int => ""
                      | Int32 => ".i32"
                      | Int64 => ".i64"
                      | Bigint => ".ibig"
                      end
  | Float64 => ""
  end.

Definition vector_type_to_string (n : vector_type) :=
  match n with
  | Array => ""
  | Bytevec => ".byte"
  end.

#[export] Instance Serialize_binary_arith_op : Serialize binary_arith_op :=
  fun a => Atom match a with
        | Add => "+"
        | Sub => "-"
        | Mul => "*"
        | Div => "/"
        | Mod => "%"
        end.

#[export] Instance Serialize_binary_bitwise_op : Serialize binary_bitwise_op :=
  fun a => Atom match a with
             | And => "&"
             | Or => "|"
             | Xor => "^"
             | Lsl => "<<"
             | Lsr => ">>"
             | Asr => "a>>"
             end.

#[export] Instance Serialize_binary_comparison : Serialize binary_comparison :=
  fun a => Atom match a with
             | Lt => "<"
             | Gt => ">"
             | Lte => "<="
             | Gte => ">="
             | Eq => "=="
             end.

#[export] Instance Serialize_binary_num_op : Serialize binary_num_op :=
  fun a => match a with
        | embed_binary_arith_op x => to_sexp x
        | embed_binary_bitwise_op x => to_sexp x
        | embed_binary_comparison x => to_sexp x
        end.

Definition Serialize_singleton_list {A} `{Serialize A} : Serialize (list A)
  := fun xs => match xs with cons x nil => to_sexp x | xs =>List (List.map to_sexp xs) end.

(* Fixpoint split_dot accl accw (s : string) := *)
(*   match s with *)
(*   | EmptyString => (string_reverse accl, string_reverse accw) *)
(*   | String c s => *)
(*       if (c =? ".")%char2 then *)
(*         let accl' := match accl with EmptyString => accw *)
(*                                 | accl => (accw ++ "." ++ accl) *)
(*                      end in *)
(*         split_dot accl' EmptyString s *)
(*       else *)
(*         split_dot accl (String c accw) s *)
(*   end. *)
(* Definition before_dot s := fst (split_dot EmptyString EmptyString s). *)
(* Definition after_dot s := snd (split_dot EmptyString EmptyString s). *)

Fixpoint to_sexp_t (a : t) : sexp :=
  match a with
  | Mvar x => to_sexp x
  | Mlambda (ids, x) => [ Atom "lambda" ; to_sexp ids ; to_sexp_t x ]
  | Mapply (x, args) => List (Atom "apply" :: to_sexp_t x :: List.map to_sexp_t args)
  | Mlet (binds, x) => List (Atom "let" :: List.map to_sexp_binding binds ++ (to_sexp_t x :: nil))
  | Mnum x => to_sexp x
  | Mstring x => Atom (Str (bytestring.String.to_string x))
  | Mglobal x => (* [Atom "global" ; Atom ("$Top") ; *) to_sexp x  (* ] *)
  | Mswitch (x, sels) => Cons (Atom "switch") (Cons (to_sexp_t x) (@Serialize_list _ (@Serialize_product _ _ (@Serialize_singleton_list _ _) to_sexp_t) sels))
  | Mnumop1 (op, num, x) => [ rawapp (to_sexp op) (numtype_to_string num) ; to_sexp_t x ]
  | Mnumop2 (op, num, x1, x2) => [ rawapp (to_sexp op) (numtype_to_string num) ; to_sexp_t x1 ; to_sexp_t x2 ]
  | Mconvert (from, to, x) => [rawapp (rawapp (Atom "convert") (numtype_to_string from)) (numtype_to_string to) ; to_sexp_t x]
  | Mvecnew (ty, x1, x2) => [ Atom (append "makevec" (vector_type_to_string ty)) ; to_sexp_t x1 ; to_sexp_t x2 ]
  | Mvecget (ty, x1, x2) => [ Atom (append "load" (vector_type_to_string ty)) ; to_sexp_t x1 ; to_sexp_t x2 ]
  | Mvecset (ty, x1, x2, x3) => [ Atom (append "store" (vector_type_to_string ty)) ; to_sexp_t x1 ; to_sexp_t x2; to_sexp_t x3 ]
  | Mveclen (ty, x) => [ Atom (append "load" (vector_type_to_string ty)) ; to_sexp_t x ]
  | Mlazy x => [Atom "lazy"; to_sexp_t x]
  | Mforce x => [Atom "force"; to_sexp_t x]
  | Mblock (tag, xs) => List (Atom "block" :: [Atom "tag"; Atom (Int63.to_Z tag)] :: List.map to_sexp_t xs)
  | Mfield (i, x) => [ Atom "field"; to_sexp i; to_sexp_t x]
  end
with
to_sexp_binding (a : binding) : sexp :=
  match a with
  | Unnamed x => [ Atom "_"; to_sexp_t x ]
  | Named (id, x) => [ to_sexp id ; to_sexp_t x ]
  | Recursive x => Cons (Atom "rec") (@Serialize_list _ (@Serialize_product _ _ _ to_sexp_t) x)
  end.


#[export] Instance Serialize_t : Serialize t := to_sexp_t.
#[export] Instance Serialize_binding : Serialize binding := to_sexp_binding.

Definition Serialize_program : Serialize program :=
  fun '(m, x) =>
    match
      Cons (Atom "module") (Serialize_list (m ++ ((bytestring.String.of_string "_main", x)  :: nil))%list)
    with
      List l => List (l ++ ([Atom "export"] :: nil))
    | x => x
    end.

Fixpoint string_map (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (f c) (string_map f s)
  end.

Definition dot_to_underscore (id : string) :=
  string_map (fun c => 
    match c with
    | "."%char => "_"%char
    | _ => c
    end) id.

Definition uncapitalize_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if (65 <=? n)%nat && (n <=? 90)%nat then ascii_of_nat (n + 32)
  else c.

Definition uncapitalize (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (uncapitalize_char c) s
  end.

Definition encode_name (s : string) : string :=
  uncapitalize (dot_to_underscore s).

Definition exports (m : list (Ident.t * t)) : list (Ident.t * t) :=
  List.map (fun '(x, v) => (bytestring.String.of_string (encode_name (bytestring.String.to_string x)), Mglobal x)) m.

Definition Serialize_module : Serialize program :=
  fun '(m, x) =>
    let exports := exports m in
    match
      Cons (Atom "module") (Serialize_list (m ++ exports)%list)
    with
      List l =>
        let exports := List.map (fun x => Atom (Raw ("$" ++ (bytestring.String.to_string (fst x))))) exports in
        List (l ++ (Cons (Atom "export") (List exports) :: nil))
    | x => x
    end.
