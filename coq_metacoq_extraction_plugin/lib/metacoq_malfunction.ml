type erasure_configuration = { enable_cofix_to_fix : bool;
                               enable_typed_erasure : bool;
                               enable_fast_remove_params : bool }

type prim_def =
| Global of string * string
| Primitive of string * int
| Erased

type prim = Kernames.kername * prim_def

type primitives = prim list

type malfunction_pipeline_config = { erasure_config : erasure_configuration;
                                     prims : primitives }


let default_erasure_config = 
  { enable_cofix_to_fix = false; enable_typed_erasure = false; enable_fast_remove_params = false }

let default_malfunction_config = 
  { erasure_config = default_erasure_config; prims = [] }

type program_type =
  | Standalone of bool (* Link statically with Coq's libraries *)
  | Plugin
  
type pipeline = OCaml | Malfunction

type malfunction_command_args =
  | Unsafe
  | Verbose
  | Time
  | Typed
  | BypassQeds
  | Fast
  | ProgramType of program_type
  | Run
  | Format
  | Pipeline of pipeline

type malfunction_plugin_config = 
  { malfunction_pipeline_config : malfunction_pipeline_config;
    bypass_qeds : bool;
    time : bool;
    verbose : bool;
    program_type : program_type option;
    run : bool;
    loc : Loc.t option;
    format : bool;
    pipeline : pipeline }

let debug_extract = CDebug.create ~name:"metacoq-extraction" ()
let debug = debug_extract

let get_stringopt_option key =
  let open Goptions in
  let tables = get_tables () in
  try
    let _ = OptionMap.find key tables in
    fun () ->
      let tables = get_tables () in
      let opt = OptionMap.find key tables in
      match opt.opt_value with
      | StringOptValue b -> b
      | _ -> assert false
  with Not_found ->
    declare_stringopt_option_and_ref ~depr:false ~key

let get_build_dir_opt =
  get_stringopt_option ["MetaCoq"; "Extraction"; "Build"; "Directory"]

(* When building standalone programs still relying on Coq's/MetaCoq's FFIs, use these packages for linking *)
let statically_linked_pkgs =
  "coq-core.boot,coq-core.clib,coq-core.config,coq-core,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.parsing,coq-core.pretyping,coq-core.printing,coq-core.proofs,coq-core.stm,coq-core.sysinit,coq-core.tactics,coq-core.toplevel,coq-core.vernac,coq-core.vm,coq-metacoq-template-ocaml,coq-metacoq-template-ocaml.plugin,coq_metacoq_extraction_ocaml_ffi,dynlink,findlib,findlib.dynload,findlib.internal,stdlib-shims,str,threads,threads.posix,unix,zarith"

let notice opts pp = 
  if opts.verbose then
    Feedback.msg_notice ?loc:opts.loc (pp ())
  else ()

let time opts = 
  if opts.time then (fun label fn arg -> Tm_util.time label fn arg) 
  else fun _label fn arg -> fn arg

(* Separate registration of primitive extraction *)

type package = string (* Findlib package names to link for external references *)

let kername_of_qualid ~loc (gr : Libnames.qualid) : Kernames.kername =
  match Constrintern.locate_reference gr with
  | None -> CErrors.user_err ~loc Pp.(Libnames.pr_qualid gr ++ str " not found.")
  | Some g ->
    match g with
    | Names.GlobRef.ConstRef c -> 
      let quoted_kn = Metacoq_template_plugin.Ast_quoter.quote_kn (Names.Constant.canonical c) in
      quoted_kn
    | Names.GlobRef.VarRef(v) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found a variable. Only constants can be realized in Malfunction.")
    | Names.GlobRef.IndRef(i) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found an inductive type. Only constants can be realized in Malfunction.")
    | Names.GlobRef.ConstructRef(c) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found a constructor. Only constants can be realized in Malfunction. ")
    
let extract_constant (gr : Kernames.kername) (s : string) : prim =
  let s = String.split_on_char '.' s in 
  let label, module_ = CList.sep_last s in
  let module_ =  (String.concat "." module_) in
  (gr, Global (module_, label))
  
let extract_primitive (gr : Kernames.kername) (symb : string) (arity : int) : prim =
  (gr, Primitive (symb, arity))

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
let get_global_packages () = snd !global_registers

let pr_char c = Pp.str (Char.escaped c)

let bytes_of_list l =
  let bytes = Bytes.create (List.length l) in
  let rec fill acc = function
    | [] -> bytes
    | c :: cs ->
      Bytes.set bytes acc c;
      fill (1 + acc) cs
  in fill 0 l

let make_options loc l =
  let prims = get_global_prims () in
  let default = {
    malfunction_pipeline_config = { default_malfunction_config with prims };
    bypass_qeds = false; time = false; program_type = None; run = false;
    verbose = false; loc; format = false; pipeline = OCaml }  
  in
  let rec parse_options opts l = 
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
    | Verbose :: l -> parse_options { opts with verbose = true } l
    | ProgramType t :: l -> parse_options { opts with program_type = Some t } l
    | Run :: l -> parse_options { opts with run = true } l
    | Format :: l -> parse_options { opts with format = true } l
    | Pipeline p :: l -> parse_options { opts with pipeline = p } l
  in parse_options default l

let find_executable opts cmd = 
  let whichcmd = Unix.open_process_in cmd in
  let result = 
    try Stdlib.input_line whichcmd 
    with End_of_file -> ""
  in
  let status = Unix.close_process_in whichcmd in
  match status with
  | Unix.WEXITED 0 -> debug Pp.(fun () -> str "Compiler is" ++ spc () ++ str result);
    result
  | _ -> 
    CErrors.user_err ?loc:opts.loc Pp.(str "Executable" ++ spc () ++ str cmd ++ spc () ++ str "not found." ++ fnl () ++
      str result)
      
type line = 
| EOF
| Info of string
| Error of string

let read_line stdout stderr =
  try Info (input_line stdout)
  with End_of_file -> 
    try Error (input_line stderr)
  with End_of_file -> EOF

let push_line buf line =
  Buffer.add_string buf line; 
  Buffer.add_string buf "\n"

let string_of_buffer buf = Bytes.to_string (Buffer.to_bytes buf)

let execute cmd =
  let (stdout, stdin, stderr) = Unix.open_process_full cmd (Unix.environment ()) in
  let continue = ref true in
  let outbuf, errbuf = Buffer.create 100, Buffer.create 100 in
  let push_info = push_line outbuf in
  let push_error = push_line errbuf in
  while !continue do
    match read_line stdout stderr with
    | EOF -> debug Pp.(fun () -> str "Program terminated"); continue := false
    | Info s -> push_info s
    | Error s -> push_error s
  done;
  let status = Unix.close_process_full (stdout, stdin, stderr) in
  status, string_of_buffer outbuf, string_of_buffer errbuf

let execute opts cmd =
  let status, out, err = execute cmd in
  match status with
  | Unix.WEXITED 0 -> out, err
  | Unix.WEXITED n -> 
    CErrors.user_err ?loc:opts.loc Pp.(str"Command" ++ spc () ++ str cmd ++ spc () ++
      str"exited with code " ++ int n ++ str "." ++ fnl () ++
      str"stdout: " ++ spc () ++ str out ++ fnl () ++ str "stderr: " ++ str err)
  | Unix.WSIGNALED n | Unix.WSTOPPED n -> 
    CErrors.user_err ?loc:opts.loc Pp.(str"Command" ++ spc () ++ str cmd ++ spc () ++ 
    str"was signaled with code " ++ int n ++ str"." ++ fnl () ++
    str"stdout: " ++ spc () ++ str out ++ fnl () ++ str "stderr: " ++ str err)


type compilation_result = 
  | SharedLib of string
  | StandaloneProgram of string

let get_prefix () = 
  match get_build_dir_opt () with
  | None -> "."
  | Some s -> s 

let build_fname f = 
  Filename.concat (get_prefix ()) f

let compile opts fname = 
  match opts.program_type with
  | None -> None
  | Some t ->
    let malfunction = find_executable opts "which malfunction" in
    let packages = get_global_packages () in
    let packages = String.concat "," packages in
    match t with
    | Plugin -> 
      let compile_cmd = 
        Printf.sprintf "%s cmx -shared -package %s %s" malfunction packages fname
      in
      let _out, _err = execute opts compile_cmd in (* we now have fname . cmx *)
      let shared_lib = Filename.chop_extension fname ^ ".cmxs" in
      Some (SharedLib shared_lib)
    | Standalone link_coq -> 
      let output = Filename.chop_extension fname in
      let flags, packages =
        if link_coq then 
          "-thread -linkpkg", statically_linked_pkgs ^ "," ^ packages
        else "-thread -linkpkg", packages
      in
      let compile_cmd = 
        Printf.sprintf "%s compile %s -package %s -o %s %s" malfunction flags packages output fname
      in
      let _out, _err = execute opts compile_cmd in (* we now have fname . cmx *)
      notice opts Pp.(fun () -> str "Compiled to " ++ str output);
      Some (StandaloneProgram output)


let run opts result =
  match result with
  | SharedLib shared_lib -> Dynlink.loadfile_private shared_lib
  | StandaloneProgram s -> 
    let out, err = execute opts ("./" ^ s) in
    if err <> "" then Feedback.msg_warning (Pp.str err);
    if out <> "" then Feedback.msg_notice (Pp.str out)

let extract (compile_malfunction : malfunction_pipeline_config -> TemplateProgram.template_program -> string)
  ?loc opts env evm c dest =
  let opts = make_options loc opts in
  let prog = time opts Pp.(str"Quoting") (Ast_quoter.quote_term_rec ~bypass:opts.bypass_qeds env) evm (EConstr.to_constr evm c) in
  let run_pipeline opts prog = compile_malfunction opts.malfunction_pipeline_config prog in
  let eprog = time opts Pp.(str"Extraction") (run_pipeline opts) prog in
  let dest = match dest with
  | None -> notice opts Pp.(fun () -> str eprog); None
  | Some fname ->
    let fname = build_fname fname in
    let oc = open_out fname in (* Does not raise? *)
    let () = output_string oc eprog in
    let () = output_char oc '\n' in
    close_out oc;
    notice opts Pp.(fun () -> str"Extracted code written to " ++ str fname);
    Some fname
  in
  match dest with
  | None -> ()
  | Some fname -> 
    if opts.format then 
      let malfunction = find_executable opts "which malfunction" in
      let temp = fname ^ ".tmp" in
      ignore (execute opts (Printf.sprintf "%s fmt < %s > %s && mv %s %s" malfunction fname temp temp fname))
    else ();
    match compile opts fname with
    | None -> ()
    | Some result -> 
      if opts.run then run opts result
      else ()
