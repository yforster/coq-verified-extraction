type malfunction_command_args =
  | Unsafe
  | Time
  | Typed
  | BypassQeds
  | Fast

val extract : malfunction_command_args list -> Environ.env -> Evd.evar_map -> EConstr.t -> string option -> unit

type prim = Kernames.kername * (Bytestring.String.t * Bytestring.String.t)

val extract_constant : Names.GlobRef.t -> string -> prim

type package = string (* Findlib package names to link for external references *)

val register : prim list -> package list -> unit