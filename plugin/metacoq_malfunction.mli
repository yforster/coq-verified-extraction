type malfunction_command_args =
  | Unsafe
  | Time
  | Typed
  | BypassQeds
  | Fast

val extract : malfunction_command_args list -> Environ.env -> Evd.evar_map -> EConstr.t -> string option -> unit