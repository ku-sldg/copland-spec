(* Abstract place-holders for error string constant definitions.
    Once instantiated, these should provide descriptive error messages for 
    dynamic error cases in Coq-extracted code. *)
From RocqCandy Require Import All.
Local Open Scope string_scope.

(* AM and CVM Errors *)
Definition errStr_peel_n_am := "Error peeling 'n' elements; ran out of RawEv".

Definition errStr_disclosePolicy := "errStr_disclosePolicy".

Definition errStr_app_auth_tok := "errStr_app_auth_tok".

Definition errStr_dispatch_error := "errStr_dispatch_error".

Definition errStr_cvm_error := "errStr_cvm_error".

Definition err_str_am_nonce := "err_str_am_nonce".

Definition errStr_decryption_prim := "errStr_decryption_prim".

Definition errStr_et_size := "errStr_et_size".

Definition errStr_lib_supports_man_check := "errStr_lib_supports_man_check".

Definition errStr_lib_supports_man_app_check := "errStr_lib_supports_man_app_check".

(* EvidenceT Bundling Errors *)
Definition errStr_empty_raw_ev := "errStr_empty_raw_ev".

Definition errStr_raw_EvidenceT_too_long := "errStr_raw_EvidenceT_too_long".

Definition errStr_raw_EvidenceT_wrong_length_comp := "errStr_raw_EvidenceT_wrong_length_comp".

(* JSON Interface Error String *)
Definition errStr_remote_am_failure := "errStr_remote_am_failure".

Definition errStr_incorrect_resp_type := "errStr_incorrect_resp_type".

Definition errStr_json_parsing := "errStr_json_parsing".

Definition errStr_invalid_request_type := "errStr_invalid_request_type".

Definition errStr_negotiation_not_implemented := "errStr_negotiation_not_implemented".

(* Run CVM Error Strings *)
Definition errStr_run_cvm_at_error_dynamic := "errStr_run_cvm_at_error_dynamic".

Definition errStr_run_cvm_at_error_static := "errStr_run_cvm_at_error_static".

Definition errStr_run_cvm_dispatch_unavailable := "errStr_run_cvm_dispatch_unavailable".

(* Type/Size Errors *)
Definition err_str_asp_bad_size `{Stringifiable nat} (got expect : nat) := 
  "ASP requires input of size " ++ to_string expect ++ 
  " but received input of size " ++ to_string got ++ "\n".

(* Global Context Errors *)
Definition err_str_asp_no_type_sig := 
  "ASP Type signature not found in the Global Context".

Definition err_str_asp_no_compat_appr_asp := 
  "Compatible Appraisal ASP not found in Global Context".

Definition err_str_asps_not_duals := "2 nested ASPs are not duals".

Definition err_str_appr_asp_not_unwrap := "Compatible Appraisal ASP is not an UNWRAP ASP".

Definition err_str_asp_is_not_wrap := "ASP is not a WRAP ASP".

Definition err_str_no_possible_left_evt := ("No possible left_evt").
Definition err_str_no_possible_right_evt := ("No possible right_evt").
Definition err_str_no_evidence_below := ("No evidence below the trail").
Definition err_str_trail_mismatch := ("Trail mismatch while trying to get belwo evidence").

Definition err_str_asp_under_unwrap := "ASP under UNWRAP is not a WRAP".
Definition err_str_wrap_asp_not_duals := "A WRAP and UNWRAP ASPs are not duals".
Definition err_str_unwrap_only_asp := "UNWRAP ASPs must be applied to ASPs".
Definition err_str_no_asp_under_evidence := "No ASP under evidence".
Definition err_str_asp_at_bottom_not_wrap := "ASP at bottom of evidence is not a WRAP ASP".

Definition err_str_cannot_have_outwrap := ("Invalid Output Signature of type 'OutUnwrap' on an ASP").

Definition err_str_01 := "Invalid request type".
Definition err_str_fwd_from_string := "Error parsing FWD from string".

Definition err_str_unwrap_must_have_outwrap := "UNWRAP ASPs must have an OutWrap output signature".

Definition err_str_only_unwrap_can_be_outwrap := "Only UNWRAP ASPs can have an OutWrap output signature".

Definition err_str_unwrap_of_wrap_same_size := "UNWRAP of a WRAP ASP must have the sime size as the WRAPed evidence".

Definition err_str_unwrap_only_wrap := "UNWRAP ASPs must be appplied to a WRAP ASP".

Definition err_str_appr_wrap_failed := "Appraisal for WRAP ASP failed. Size of input to wrap is not same as output of UNWRAP".

Definition err_str_extend_must_have_outn := "EXTEND ASPs must have OutN".

Definition err_str_ev_split_failed_not_empty := "Evidence splitting failed: rest of evidence not empty".

Definition err_str_json_nat_string := "Error converting JSON to nat: JSON was not a string".

Definition err_str_json_cannot_interp_nat := "Error:  cannot interpret nat string in Jsonifiable_nat".

Definition err_str_json_parsing_outn := "Error parsing OutN from JSON (wrong number of arguments, expected 1)".

Definition err_str_evoutsig_json_constructor := "Invalid EvOutSig JSON constructor name".

Definition err_str_invalid_evinsig_json := "Invalid EvInSig JSON".

Definition err_str_json_parsing_failure_wrong_number_args :=
  "Error parsing JSON: Wrong number of arguments".

Definition err_str_json_invalid_constructor_name :=
  "Error parsing JSON: Invalid constructor name".

Definition err_str_json_parsing_SP := "Error parsing SP from JSON (not ALL or NONE)".

Definition err_str_json_parsing_ASPC := "Error parsing ASPC from JSON".

Definition err_str_invalid_evidence_json := "Invalid Evidence JSON".

Definition err_str_parsing_global_ctx := "Error parsing Global Context from JSON".

Definition err_str_list_json_to_manifest_set := "Error converting list from JSON to Manifest Set".

Definition err_str_appr_compute_evt_neq := "Error in appraisal procedure computation, type of evidence passed into an appraisal procedure does not match the expected type (evidence types are not equivalent)". 
Definition err_str_appr_compute_appr_wrap_no_unwrap := "Error in appraisal procedure computation: Attempting to appraise WRAPPED evidence but the dual appraisal ASP is not an UNWRAP.".
Definition err_str_appr_not_originally_a_wrap := "Error in appraisal procedure computation: Attempting to appraise UNWRAPPED evidence but the UNWRAPPED evidence was not originally a WRAP.".
Definition err_str_appr_only_allow_on_asp := "Error in appraisal procedure computation: Attempting to appraise UNWRAPPED evidence but evidence that was UNWRAPPED was not an ASP (UNWRAP can only be applied to an ASP input).".

Definition err_str_split_evidence_not_split := "Error in appraisal procedure computation, type of evidence passed into a split appraisal procedure is not a split evidence type".
