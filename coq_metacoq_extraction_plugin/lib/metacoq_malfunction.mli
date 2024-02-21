type erasure_configuration = { enable_cofix_to_fix : bool;
                               enable_typed_erasure : bool;
                               enable_fast_remove_params : bool }

type prim_def =
| Global of string * string
| Primitive of string * int
| Erased

type prim = Kernames.kername * prim_def

type primitives = prim list

type inductive_mapping = Kernames.inductive * (string * int list) (* Target inductive type and mapping of constructor names to constructor tags *)
type inductives_mapping = inductive_mapping list

type malfunction_pipeline_config = { 
  erasure_config : erasure_configuration;
  prims : primitives;
  ind_mapping : inductives_mapping }

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

val constant_of_qualid : loc:Loc.t -> Libnames.qualid -> Kernames.kername
val inductive_of_qualid : loc:Loc.t -> Libnames.qualid -> Kernames.inductive

val extract_constant : Kernames.kername -> string -> prim
val extract_primitive : Kernames.kername -> string -> int -> prim

(* This allows only reordering and renaming of the constructors *)
val extract_inductive : Kernames.inductive -> string * int list -> inductive_mapping

type package = string

val register_inductives : inductives_mapping -> unit
val register : prim list -> package list -> unit

val extract : 
  (malfunction_pipeline_config -> TemplateProgram.template_program -> string) ->
  ?loc:Loc.t ->
  malfunction_command_args list ->
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  string option ->
  unit
