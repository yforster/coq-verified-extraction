Require Import MetaCoq.Utils.bytestring.
From Malfunction.Plugin Require Import Loader.
From Malfunction Require Import FFI.

Verified Extract Constants [ 
  coq_msg_info => "Coq_verified_extraction_plugin__Coq_ffi.msg_info",
  coq_msg_notice => "Coq_verified_extraction_plugin__Coq_ffi.msg_notice",
  coq_msg_debug => "Coq_verified_extraction_plugin__Coq_ffi.msg_debug",
  coq_user_error => "Coq_verified_extraction_plugin__Coq_ffi.user_error" ]
Packages [ "coq_verified_extraction.plugin" ].
