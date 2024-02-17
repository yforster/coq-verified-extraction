
type program_type = 
  | Standalone of bool (* Link with Coq's packages? *)
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

type prim = Bytestring.String.t * Bytestring.String.t Malfunction.prim_def

(** Checks that the qualid is defined and translate it to a fully qualified name *)
val bytestring_of_qualid : loc:Loc.t -> Libnames.qualid -> Bytestring.String.t

val extract_primitive : Bytestring.String.t -> string -> int -> prim
  
val extract_constant : Bytestring.String.t -> string -> prim

type package = string (* Findlib package names to link for external references *)

val register : prim list -> package list -> unit

(* Main commands *)
val extract : ?loc:Loc.t -> malfunction_command_args list -> Environ.env -> Evd.evar_map -> EConstr.t -> 
  string option -> unit
