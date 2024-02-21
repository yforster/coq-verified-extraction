Require Import MetaCoq.Utils.bytestring.
From Malfunction.Plugin Require Import Loader.

Axiom (coq_msg_info : string -> unit).
Axiom (coq_msg_notice : string -> unit).
Axiom (coq_msg_debug : string -> unit).
Axiom (coq_user_error : string -> unit).

MetaCoq Extract Constants [ 
  coq_msg_info => "Feedback.coq_msg_info",
  coq_msg_notice => "Feedback.coq_msg_notice",
  coq_msg_debug => "Feedback.coq_msg_debug",
  coq_user_error => "Feedback.coq_user_error" ]
Packages [ "coq-core.lib" ].