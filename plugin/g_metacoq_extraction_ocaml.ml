let _ = Mltop.add_known_module "coq-metacoq-extraction-ocaml.plugin"

# 5 "g_metacoq_extraction_ocaml.mlg"
 

open Names
open Pp
open Ltac_plugin
open Stdarg
open Pcoq.Prim
open Tacexpr
open Tacinterp
open Stdarg
open Tacarg
open Genredexpr

open Coq_metacoq_extraction_plugin.Metacoq_malfunction
open Coq_metacoq_extraction_plugin.G_metacoq_malfunction

module MLExtaction : ExtractionInterface =
struct
  type pipeline_config = Pipeline.malfunction_pipeline_config

  let interp_prim = function
    | Global (module_, label) ->
      let module_ = Caml_bytestring.bytestring_of_caml_string module_ in
      let label = Caml_bytestring.bytestring_of_caml_string label in
      Malfunction.Global (module_, label)
    | Erased -> Malfunction.Erased
    | Primitive (symb, arity) ->
      let symbol = Caml_bytestring.bytestring_of_caml_string symb in
      let arity = Caml_nat.nat_of_caml_int arity in
      Malfunction.Primitive (symbol, arity)

  let interp_prims prims = 
    List.map (fun (kn, p) -> (Kernames.string_of_kername kn, interp_prim p)) prims

  let interp_pipeline_config c = 
    let { 
      erasure_config = 
       { enable_cofix_to_fix = enable_cofix_to_fix; 
         enable_typed_erasure = enable_typed_erasure; 
         enable_fast_remove_params = enable_fast_remove_params };
      prims = prims } = c in
    let erasure_config = 
      Erasure0.({ 
        enable_cofix_to_fix; enable_typed_erasure; enable_fast_remove_params;
        dearging_config = default_dearging_config })
    in
    Pipeline.{ 
      erasure_config;
      prims = interp_prims prims
    }

  let compile_malfunction conf p = 
    Caml_bytestring.caml_string_of_bytestring (Pipeline.compile_malfunction_gen conf p)

end

let () = 
  pipelines := { !pipelines with ocaml_pipeline = Some (module MLExtaction : ExtractionInterface) }



let () = Vernacextend.vernac_extend ~plugin:"coq-metacoq-extraction-ocaml.plugin" ~command:"MetaCoq_Extraction" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("MetaCoq", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("-help", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 67 "g_metacoq_extraction_ocaml.mlg"
                                         
  let usage = "MetaCoq (Bypass)? Extraction [term] [output_file]?" in
  Feedback.msg_notice (str usage)
  
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("MetaCoq", 
                                    Vernacextend.TyTerminal ("Extraction", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_extract_args)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                    Vernacextend.TyNil))))), (let coqpp_body l
                                                             c dest
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 71 "g_metacoq_extraction_ocaml.mlg"
                                                                                 
    let env = Global.env () in
    let evm = Evd.from_env env in
    let loc = Constrexpr_ops.constr_loc c in
    let (c, _) = Constrintern.interp_constr env evm c in
    extract ?loc l env evm c dest
  
                                                                  ) in fun l
                                                             c dest
                                                             ?loc ~atts ()
                                                             -> coqpp_body l
                                                             c dest
                                                             (Attributes.unsupported_attributes atts)), None))]

