type inductive_mapping = Kernames.inductive * (string * int list) (* Target inductive type and mapping of constructor names to constructor tags *)
type inductives_mapping = inductive_mapping list

type erasure_configuration = { enable_cofix_to_fix : bool;
                               enable_typed_erasure : bool;
                               enable_fast_remove_params : bool; 
                               inductives_mapping : inductives_mapping }

type prim_def =
| Global of string * string
| Primitive of string * int
| Erased

type prim = Kernames.kername * prim_def

type primitives = prim list

type malfunction_pipeline_config = { 
  erasure_config : erasure_configuration;
  prims : primitives }

let default_erasure_config inductives_mapping = 
  { enable_cofix_to_fix = false; enable_typed_erasure = false; enable_fast_remove_params = false; inductives_mapping }

let default_malfunction_config inductives_mapping prims = 
  { erasure_config = default_erasure_config inductives_mapping; prims }

type program_type =
  | Standalone of bool (* Link statically with Coq's libraries *)
  | Plugin

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
  | Optimize

type malfunction_plugin_config = 
  { malfunction_pipeline_config : malfunction_pipeline_config;
    bypass_qeds : bool;
    time : bool;
    verbose : bool;
    program_type : program_type option;
    run : bool;
    loc : Loc.t option;
    format : bool;
    optimize : bool }

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

let time prefix f x =
  let start = Unix.gettimeofday () in
  let res = f x in
  let stop = Unix.gettimeofday () in
  let () = Feedback.msg_info Pp.(prefix ++ str " executed in: " ++ Pp.real (stop -. start) ++ str "s") in
  res

let time opts = 
  if opts.time then (fun label fn arg -> time label fn arg) 
  else fun _label fn arg -> fn arg

(* Separate registration of primitive extraction *)

type package = string (* Findlib package names to link for external references *)

let globref_of_qualid ?loc (gr : Libnames.qualid) : Names.GlobRef.t  =
  match Constrintern.locate_reference gr with
  | None -> CErrors.user_err ?loc Pp.(Libnames.pr_qualid gr ++ str " not found.")
  | Some g -> g
    
let quoted_globref_of_qualid ~loc (gr : Libnames.qualid) : Kernames.global_reference =
  Metacoq_template_plugin.Ast_quoter.quote_global_reference (globref_of_qualid ~loc gr)

let constant_of_qualid ~loc (gr : Libnames.qualid) : Kernames.kername =
  match quoted_globref_of_qualid ~loc gr with
  | Kernames.ConstRef kn -> kn
  | Kernames.VarRef(v) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found a variable. Only constants can be realized in Malfunction.")
  | Kernames.IndRef(i) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found an inductive type. Only constants can be realized in Malfunction.")
  | Kernames.ConstructRef(_, _) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found a constructor. Only constants can be realized in Malfunction. ")
    
let inductive_of_qualid ~loc (gr : Libnames.qualid) : Kernames.inductive =
  match quoted_globref_of_qualid ~loc gr with
  | Kernames.ConstRef kn -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a constant. Only inductives can be translated in Malfunction.")
  | Kernames.VarRef(v) -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a variable. Only constants can be translated in Malfunction.")
  | Kernames.IndRef(i) -> i
  | Kernames.ConstructRef(_, _) -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a constructor. Only constants can be translated in Malfunction. ")
  
let extract_constant (gr : Kernames.kername) (s : string) : prim =
  let s = String.split_on_char '.' s in 
  let label, module_ = CList.sep_last s in
  let module_ =  (String.concat "." module_) in
  (gr, Global (module_, label))
  
let extract_primitive (gr : Kernames.kername) (symb : string) (arity : int) : prim =
  (gr, Primitive (symb, arity))

let extract_inductive (gr : Kernames.inductive) (cstrs : string * int list) : inductive_mapping =
  (gr, cstrs)

let global_inductive_registers = 
  Summary.ref ([] : inductives_mapping) ~name:"MetaCoq Malfunction Inductive Registration"
  
let global_inductive_registers_name = "metacoq-malfunction-inductive-registration"

let cache_inductive_registers inds =
  let inds' = !global_inductive_registers in
  global_inductive_registers := inds @ inds'

let global_inductive_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_inductive_registers_name
    ~cache:(fun r -> cache_inductive_registers r)
    ~subst:None)

let register_inductives (inds : inductives_mapping) : unit =
  Lib.add_leaf (global_inductive_registers_input inds)

let get_global_inductives_mapping () = !global_inductive_registers

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
  let inductives_mapping = get_global_inductives_mapping () in
  let prims = get_global_prims () in
  let default = {
    malfunction_pipeline_config = default_malfunction_config inductives_mapping prims;
    bypass_qeds = false; time = false; program_type = None; run = false;
    verbose = false; loc; format = false; optimize = false }  
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
    | Optimize :: l -> parse_options { opts with optimize = true } l
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
  debug Pp.(fun () -> str "Executing: " ++ str cmd);
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
  | SharedLib of string list * string
  | StandaloneProgram of string

let get_prefix () = 
  match get_build_dir_opt () with
  | None -> "."
  | Some s -> s 

let build_fname f = 
  Filename.concat (get_prefix ()) f
let increment_subscript id =
  let len = String.length id in
  let rec add carrypos =
    let c = id.[carrypos] in
    if Util.is_digit c then
      if Int.equal (Char.code c) (Char.code '9') then begin
        assert (carrypos>0);
        add (carrypos-1)
      end
      else begin
        let newid = Bytes.of_string id in
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid carrypos (Char.chr (Char.code c + 1));
        newid
      end
    else begin
      let newid = Bytes.of_string (id^"0") in
      if carrypos < len-1 then begin
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid (carrypos+1) '1'
      end;
      newid
    end
  in String.of_bytes (add (len-1))

let next_string_away_from s bad =
  let rec name_rec s = if bad s then name_rec (increment_subscript s) else s in
  name_rec s

let loaded_modules = ref CString.Set.empty
  
let compile opts names fname = 
  match opts.program_type with
  | None -> None
  | Some t ->
    let malfunction = find_executable opts "which malfunction" in
    let ocamlfind = find_executable opts "which ocamlfind" in
    let packages = get_global_packages () in
    let packages = String.concat "," packages in
    let optimize = if opts.optimize then "-O2" else "" in
    match t with
    | Plugin -> 
      let fname = 
        let basename = Filename.chop_extension fname in
        let freshname = next_string_away_from basename (fun s -> CString.Set.mem s !loaded_modules) in
        let freshfname = freshname ^ ".mlf" in
        if freshname <> basename then 
          ignore (execute opts (Printf.sprintf "mv %s %s" fname freshfname));
        loaded_modules := CString.Set.add freshname !loaded_modules;
        freshfname
      in
      let compile_cmd = 
        Printf.sprintf "%s cmx %s -shared -package %s %s" malfunction optimize packages fname
      in
      let _out, _err = execute opts compile_cmd in (* we now have fname . cmx *)
      let cmxfile =  Filename.chop_extension fname ^ ".cmx" in
      let cmxsfile = Filename.chop_extension fname ^ ".cmxs" in
      (* Build the shared library *)
      let link_cmd = 
        Printf.sprintf "%s opt -shared -package %s -o %s %s" ocamlfind packages cmxsfile cmxfile
      in
      let _out, _err = execute opts link_cmd in
      Some (SharedLib (names, cmxsfile))
    | Standalone link_coq -> 
      let output = Filename.chop_extension fname in
      let flags, packages =
        if link_coq then 
          "-thread -linkpkg", statically_linked_pkgs ^ "," ^ packages
        else "-thread -linkpkg", packages
      in
      let compile_cmd = 
        Printf.sprintf "%s compile %s %s -package %s -o %s %s" 
          malfunction optimize flags packages output fname
      in
      let _out, _err = time opts Pp.(str "Compilation") (execute opts) compile_cmd in (* we now have fname . cmx *)
      notice opts Pp.(fun () -> str "Compiled to " ++ str output);
      Some (StandaloneProgram output)

type malfunction_program_type = 
  | Standalone_binary
  | Shared_library of string * string

type plugin_function = Obj.t

let register_plugins = Summary.ref ~name:"metacoq-extraction-plugins" (CString.Map.empty : plugin_function CString.Map.t)

let cache_plugin (name, fn) = 
  register_plugins := CString.Map.add name fn !register_plugins
  
let plugin_input =
  let open Libobject in 
  declare_object 
    (global_object_nodischarge "metacoq-extraction-plugins"
    ~cache:(fun r -> cache_plugin r)
    ~subst:None)
  
let register_plugin name fn : unit =
  Lib.add_leaf (plugin_input (name, fn))
  
module Reify =
struct

  type reifyable_value_type =
  | IsInductive of Names.inductive * Univ.Instance.t * Constr.t list
  | IsPrimitive of Names.Constant.t * Univ.Instance.t * Constr.t list
  
  type reifyable_type = 
  | IsThunk of reifyable_value_type
  | IsValue of reifyable_value_type

  let type_of_reifyable_type = function
    | IsInductive (hd, u, args) -> Term.applistc (Constr.mkIndU ((hd, u))) args
    | IsPrimitive (c, u, args) -> Term.applistc (Constr.mkConstU ((c, u))) args

  let pr_reifyable_type env sigma ty =
    Printer.pr_constr_env env sigma (type_of_reifyable_type ty)

  let find_nth_constant n ar =
    let open Inductiveops in
    let rec aux i const = 
      if Array.length ar <= i then raise Not_found
      else if CList.is_empty ar.(i).cs_args then  (* FIXME lets in constructors *)
        if const = n then i 
        else aux (i + 1) (const + 1)
      else aux (i + 1) const
    in aux 0 0

  let find_nth_non_constant n ar =
    let open Inductiveops in
    let rec aux i nconst = 
      if Array.length ar <= i then raise Not_found
      else if not (CList.is_empty ar.(i).cs_args) then 
        if nconst = n then i
        else aux (i + 1) (nconst + 1)
      else aux (i + 1) nconst
    in aux 0 0
    
  let invalid_type ?loc env sigma ty = 
    CErrors.user_err ?loc
      Pp.(str"Cannot reify values of non-inductive or non-primitive type: " ++ 
          Printer.pr_econstr_env env sigma ty)
    
  let check_reifyable_value_type ?loc env sigma ty =
    (* We might have bound universes though. It's fine! *)
    try let (hd, u), args = Inductiveops.find_inductive env sigma ty in
      IsInductive (hd, EConstr.EInstance.kind sigma u, args)
    with Not_found -> 
      let hnf = Reductionops.whd_all env sigma ty in
      let hd, args = EConstr.decompose_app sigma hnf in
      match EConstr.kind sigma hd with
      | Const (c, u) when Environ.is_primitive_type env c -> 
        IsPrimitive (c, EConstr.EInstance.kind sigma u, List.map EConstr.Unsafe.to_constr args)
      | _ -> invalid_type ?loc env sigma hnf

  let check_reifyable_value ?loc env sigma c =
    check_reifyable_value_type ?loc env sigma (Retyping.get_type_of env sigma c)
  
  let check_reifyable_thunk_or_value_type ?loc env sigma ty =
    debug Pp.(fun () -> str "Checking reifyability of " ++ Printer.pr_econstr_env env sigma ty);
    match EConstr.kind sigma ty with
    | Constr.Prod (na, dom, codom) -> 
      (match Inductiveops.find_inductive env sigma dom with
      | exception Not_found -> invalid_type ?loc env sigma dom
      | (hd, u), args -> 
        if Names.GlobRef.equal (Coqlib.lib_ref "core.unit.type") (IndRef hd) then
          let tt = Coqlib.lib_ref "core.unit.tt" in
          let sigma, ttc = Evd.fresh_global env sigma tt in
          IsThunk (check_reifyable_value_type ?loc env sigma (EConstr.Vars.subst1 ttc codom))
        else invalid_type ?loc env sigma dom)
    | _ -> IsValue (check_reifyable_value_type ?loc env sigma ty)
  
  let check_reifyable_thunk_or_value ?loc env sigma v =
    check_reifyable_thunk_or_value_type ?loc env sigma (Retyping.get_type_of env sigma v)
  
  let ill_formed env sigma ty =
    match ty with
    | IsInductive _ -> 
      CErrors.anomaly ~label:"metacoq-extraction-reify-ill-formed"
      Pp.(str "Ill-formed inductive value representation in MetaCoq's Extraction reification for type " ++
        pr_reifyable_type env sigma ty)
    | IsPrimitive _ ->
      CErrors.anomaly ~label:"metacoq-extraction-reify-ill-formed"
      Pp.(str "Ill-formed primitive value representation in MetaCoq's Extraction reification for type " ++
        pr_reifyable_type env sigma ty)

  (* let ocaml_get_boxed_ordinal v = 
    (* tag is the header of the object *)
    let tag = Array.unsafe_get (Obj.magic v : Obj.t array) (-1) in
    (* We turn it into an ocaml int usable for arithmetic operations *)
    let tag_int = (Stdlib.Int.shift_left (Obj.magic (Obj.repr tag)) 1) + 1 in
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml tag: %i" (Obj.tag tag)));
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml get_boxed_ordinal int: %u" tag_int));
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml get_boxed_ordinal ordinal: %u" (tag_int land 255)));
    tag_int land 255 *)

  let reify env sigma ty v : Constr.t = 
    let open Declarations in
    let debug s = debug Pp.(fun () -> str ("reify: ") ++ s ()) in
    let rec aux ty v =
    Control.check_for_interrupt ();
    let () = debug Pp.(fun () -> str "Reifying value of type " ++ pr_reifyable_type env sigma ty) in
    match ty with
    | IsInductive (hd, u, args) -> 
      let open Inductive in
      let open Inductiveops in
      let spec = lookup_mind_specif env hd in
      let npars = inductive_params spec in
      let params, _indices = CList.chop npars args in
      let indfam = make_ind_family ((hd, u), params) in
      let cstrs = get_constructors env indfam in
      if Obj.is_block v then
        let ord = Obj.tag v in
        let () = debug Pp.(fun () -> str (Printf.sprintf "Reifying constructor block of tag %i" ord)) in
        let coqidx = 
          try find_nth_non_constant ord cstrs 
          with Not_found -> ill_formed env sigma ty
        in
        let cstr = cstrs.(coqidx) in
        let ctx = Vars.smash_rel_context cstr.cs_args in
        let vargs = List.init (List.length ctx) (Obj.field v) in
        let args' = List.map2 (fun decl v -> 
          let argty = check_reifyable_value env sigma 
          (EConstr.of_constr (Context.Rel.Declaration.get_type decl)) in
          aux argty v) (List.rev ctx) vargs in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) (params @ args')
      else (* Constant constructor *)
        let ord = (Obj.magic v : int) in
        let () = debug Pp.(fun () -> str @@ Printf.sprintf "Reifying constant constructor: %i" ord) in
        let coqidx = 
          try find_nth_constant ord cstrs 
          with Not_found -> ill_formed env sigma ty 
        in
        let () = debug Pp.(fun () -> str @@ Printf.sprintf "Reifying constant constructor: %i is %i in Coq" ord coqidx) in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) params
    | IsPrimitive (c, u, _args) -> 
      if Environ.is_array_type env c then 
        CErrors.user_err Pp.(str "Primitive arrays are not supported yet in MetaCoq r Extractioneification")
      else if Environ.is_float64_type env c then
        Constr.mkFloat (Obj.magic v)
      else if Environ.is_int63_type env c then
        Constr.mkInt (Obj.magic v)
      else CErrors.user_err Pp.(str "Unsupported primitive type in MetaCoq r Extractioneification")
    in aux ty v

  let reify opts env sigma tyinfo result =
    if opts.time then time opts (Pp.str "Reification") (reify env sigma tyinfo) result
    else reify env sigma tyinfo result

end

let run_code opts env sigma tyinfo code : Constr.t =
  let open Reify in
  let value, tyinfo =
    match tyinfo with
    | IsThunk vty -> ((Obj.magic code : unit -> Obj.t) (), vty)
    | IsValue vty -> code, vty
  in
  Reify.reify opts env sigma tyinfo value

let run opts env sigma tyinfos result : Constr.t list =
  match result with
  | SharedLib (fns, shared_lib) ->
    time opts Pp.(str "Dynamically linking " ++ str shared_lib) Dynlink.loadfile_private shared_lib;
    debug Pp.(fun () -> str"Loaded shared library: " ++ str shared_lib);
    let run fn tyinfo = 
      match CString.Map.find_opt fn !register_plugins with
      | None -> CErrors.anomaly Pp.(str"Couldn't find funtion " ++ str fn ++ str" which should have been registered by " ++ str shared_lib)
      | Some code -> time opts Pp.(str fn) (run_code opts env sigma tyinfo) code
    in
    List.map2 run fns tyinfos

  | StandaloneProgram s -> 
    let out, err = time opts Pp.(str s) (execute opts) ("./" ^ s) in
    if err <> "" then Feedback.msg_warning (Pp.str err);
    if out <> "" then Feedback.msg_notice (Pp.str out);
    []

type malfunction_compilation_function =
  malfunction_pipeline_config -> malfunction_program_type -> TemplateProgram.template_program -> 
  string list * string

let decompose_argument env sigma c =
  let rec aux c =
    let fn, args = EConstr.decompose_app sigma c in
    match EConstr.kind sigma fn, args with
    | Construct (cstr, u), [ _; _; fst; snd ] when Names.GlobRef.equal (ConstructRef cstr) (Coqlib.lib_ref "core.prod.intro") ->
    aux fst @ [Reify.check_reifyable_thunk_or_value env sigma snd]
    | _ -> [Reify.check_reifyable_thunk_or_value env sigma c]
  in aux c

let extract_and_run
  (compile_malfunction : malfunction_compilation_function)
  ?loc opts env sigma c dest : (Constr.t list) option =
  let opts = make_options loc opts in
  let prog = time opts Pp.(str"Quoting") (Ast_quoter.quote_term_rec ~bypass:opts.bypass_qeds env) sigma (EConstr.to_constr sigma c) in
  let pt = match opts.program_type with 
    | Some (Standalone _) | None -> Standalone_binary 
    | Some Plugin -> Shared_library ("Coq_metacoq_extraction_plugin__Metacoq_malfunction", "register_plugin")
  in
  let tyinfos =
    try decompose_argument env sigma c
    with e -> if not opts.run then [] else raise e
  in
  let run_pipeline opts prog = compile_malfunction opts.malfunction_pipeline_config pt prog in
  let names, eprog = time opts Pp.(str"Extraction") (run_pipeline opts) prog in
  let dest = match dest with
  | None -> Feedback.msg_notice Pp.(str eprog); None
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
  | None -> None
  | Some fname -> 
    if opts.format then 
      let malfunction = find_executable opts "which malfunction" in
      let temp = fname ^ ".tmp" in
      ignore (execute opts (Printf.sprintf "%s fmt < %s > %s && mv %s %s" malfunction fname temp temp fname))
    else ();
    match compile opts names fname with
    | None -> None
    | Some result -> 
      if opts.run then Some (run opts env sigma tyinfos result)
      else None

let print_results env sigma = function
  | None -> ()
  | Some [res] ->
    Feedback.msg_notice Pp.(str"  = " ++ Printer.pr_constr_env env sigma res)
  | Some res ->
    Feedback.msg_notice Pp.(str"  = (" ++ Pp.(prlist_with_sep (fun () -> str", ") (Printer.pr_constr_env env sigma) res) ++ str ")")

let eval_name (fn : string) =
  match CString.Map.find_opt fn !register_plugins with
  | None -> CErrors.anomaly Pp.(str"Couldn't find funtion " ++ str fn ++ str" in registered plugins")
  | Some code -> code

let eval_term ?loc opts env sigma c =
  let tyinfo = Reify.check_reifyable_thunk_or_value ?loc env sigma c in
  let name = 
    let fn, args = EConstr.decompose_app sigma c in
    match EConstr.kind sigma fn with
    | Constr.Const (kn, u) -> Names.Constant.to_string kn
    | _ -> "term"
  in
  let code = eval_name name in
  let c = run_code opts env sigma tyinfo code in
  print_results env sigma (Some [c])

let eval_plugin ?loc opts (gr : Libnames.qualid) =
  let opts = make_options loc opts in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let gr = globref_of_qualid gr in
  let c = match gr with Names.GlobRef.ConstRef c -> c | _ -> 
    CErrors.user_err Pp.(Printer.pr_global gr ++ str " does not bind to a reference") in
  let fn = Names.Constant.to_string c in
  let sigma, grc = Evd.fresh_global env sigma gr in
  let tyinfo = Reify.check_reifyable_thunk_or_value env sigma grc in
  let code = eval_name fn in
  let c = run_code opts env sigma tyinfo code in
  print_results env sigma (Some [c])

let extract compile_malfunction ?loc opts env sigma c dest = 
  let res = extract_and_run compile_malfunction ?loc opts env sigma c dest in
  print_results env sigma res