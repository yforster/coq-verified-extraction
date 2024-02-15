
open Stdarg
open Pp
open PeanoNat.Nat
open Datatypes
open Vernacextend
open Tm_util

type malfunction_command_args =
  | Unsafe
  | Time
  | Typed
  | BypassQeds
  | Fast

type malfunction_plugin_config = 
  { malfunction_pipeline_config : Pipeline.malfunction_pipeline_config;
    bypass_qeds : bool;
    time : bool }

(* Separate registration of primitive extraction *)

type prim = Kernames.kername * (Bytestring.String.t * Bytestring.String.t)

type package = string (* Findlib package names to link for external references *)

let extract_constant (g : Names.GlobRef.t) (s : string) : prim =
  match g with
  | Names.GlobRef.ConstRef c -> 
    let s = String.split_on_char '.' s in 
    let label, module_ = CList.sep_last s in
    let label = Caml_bytestring.bytestring_of_caml_string label in
    let module_ = Caml_bytestring.bytestring_of_caml_string (String.concat "." module_) in
    (Obj.magic (Metacoq_template_plugin.Ast_quoter.quote_kn (Names.Constant.canonical c)), (module_, label))
  | Names.GlobRef.VarRef(v) -> CErrors.user_err (str "Expected a constant but found a variable. Only constants can be realized in Malfunction.")
  | Names.GlobRef.IndRef(i) -> CErrors.user_err (str "Expected a constant but found an inductive type. Only constants can be realized in Malfunction.")
  | Names.GlobRef.ConstructRef(c) -> CErrors.user_err (str "Expected a constant but found a constructor. Only constants can be realized in Malfunction. ")


let global_registers = 
  Summary.ref (([], []) : prim list * package list) ~name:"MetaCoq Malfunction Registration"

let global_registers_name = "metacoq-malfunction-registration"

let cache_registers (prims, packages) =
  let (prims', packages') = !global_registers in
  global_registers := (prims @ prims', packages @ packages')

let global_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_registers_name
    ~cache:(fun r -> cache_registers r)
    ~subst:None)

let register (prims : prim list) (packages : package list) : unit =
  Lib.add_leaf (global_registers_input (prims, packages))

let get_global_prims () = fst !global_registers
let get_global_package () = snd !global_registers

let pr_char c = str (Char.escaped c)

let bytes_of_list l =
  let bytes = Bytes.create (List.length l) in
  let rec fill acc = function
    | [] -> bytes
    | c :: cs ->
      Bytes.set bytes acc c;
      fill (1 + acc) cs
  in fill 0 l

let pr_char_list l =
  (* We allow utf8 encoding *)
  str (Caml_bytestring.caml_string_of_bytestring l)

let make_options l =
  let open Pipeline in
  let prims = get_global_prims () in
  let default = {
    malfunction_pipeline_config = { default_malfunction_config with prims };
    bypass_qeds = false; time = false }  
  in
  let rec parse_options opts l = 
    let open Erasure0 in
    match l with
    | [] -> opts
    | Unsafe :: l -> parse_options { opts with 
      malfunction_pipeline_config = { opts.malfunction_pipeline_config with erasure_config = 
      { opts.malfunction_pipeline_config.erasure_config with enable_cofix_to_fix = true } } } l
    | Typed :: l -> parse_options { opts with 
      malfunction_pipeline_config = { opts.malfunction_pipeline_config with erasure_config = 
      { opts.malfunction_pipeline_config.erasure_config with enable_typed_erasure = true } } } l
    | Fast :: l -> parse_options { opts with
      malfunction_pipeline_config = { opts.malfunction_pipeline_config with erasure_config = 
      { opts.malfunction_pipeline_config.erasure_config with enable_fast_remove_params = true } } } l
    | BypassQeds :: l -> parse_options { opts with bypass_qeds = true } l
    | Time :: l -> parse_options { opts with time = true } l
  in parse_options default l

let extract opts env evm c dest =
  let opts = make_options opts in
  let time = 
    if opts.time then (fun label fn arg -> time label fn arg) 
    else fun _label fn arg -> fn arg
  in
  let prog = time (str"Quoting") (Ast_quoter.quote_term_rec ~bypass:opts.bypass_qeds env) evm (EConstr.to_constr evm c) in
  let eprog = time (str"Extraction") (Pipeline.compile_malfunction_gen opts.malfunction_pipeline_config) prog in
  match dest with
  | None -> Feedback.msg_notice (pr_char_list eprog)
  | Some fname -> 
    let oc = open_out fname in (* Does not raise? *)
    let () = output_string oc (Caml_bytestring.caml_string_of_bytestring eprog) in
    let () = output_char oc '\n' in
    close_out oc;
    Feedback.msg_notice (str"Extracted code written to " ++ str fname)