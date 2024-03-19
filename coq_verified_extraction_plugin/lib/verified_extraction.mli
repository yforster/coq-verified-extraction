type inductive_mapping = Kernames.inductive * (string * int list) (* Target inductive type and mapping of constructor names to constructor tags *)
type inductives_mapping = inductive_mapping list

type unsafe_passes = 
  { cofix_to_lazy : bool;
    reorder_constructors : bool;
    inlining : bool;
    unboxing : bool;
    betared : bool }

type erasure_configuration = { 
  enable_unsafe : unsafe_passes;
  enable_typed_erasure : bool;
  enable_fast_remove_params : bool; 
  inductives_mapping : inductives_mapping;
  inlined_constants : Kernames.KernameSet.t }

type prim_def =
| Global of string * string
| Primitive of string * int
| Erased

type prim = Kernames.kername * prim_def

type primitives = prim list

type malfunction_pipeline_config = { 
  erasure_config : erasure_configuration;
  prims : primitives }

type program_type =
  | Standalone of bool (* Link statically with Coq's libraries *)
  | Plugin
  
type unsafe_pass = 
  | CoFixToLazy
  | ReorderConstructors
  | Inlining
  | Unboxing
  | BetaRed

type malfunction_command_args =
  | Unsafe of unsafe_pass list
  | Verbose
  | Time
  | Typed
  | BypassQeds
  | Fast
  | ProgramType of program_type
  | Load
  | Run
  | Format
  | Optimize

val constant_of_qualid : loc:Loc.t -> Libnames.qualid -> Kernames.kername
val inductive_of_qualid : loc:Loc.t -> Libnames.qualid -> Kernames.inductive

val extract_constant : Kernames.kername -> string -> prim
val extract_primitive : Kernames.kername -> string -> int -> prim

(* This allows only reordering and renaming of the constructors *)
val extract_inductive : Kernames.inductive -> string * int list -> inductive_mapping

type package = string

val register_inductives : inductives_mapping -> unit
val register_inlines : Kernames.kername list -> unit
val register : prim list -> package list -> unit

type malfunction_program_type = 
| Standalone_binary
| Shared_library of string * string

type plugin_function = Obj.t

val register_plugin : string -> plugin_function -> unit

type malfunction_compilation_function =
  malfunction_pipeline_config -> malfunction_program_type -> TemplateProgram.template_program -> 
  string list * string

val extract : 
  malfunction_compilation_function ->
  ?loc:Loc.t ->
  malfunction_command_args list ->
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  string option ->
  unit

val eval_plugin : ?loc:Loc.t -> malfunction_command_args list -> Libnames.qualid -> unit
