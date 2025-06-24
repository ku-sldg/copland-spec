From Stdlib Require Import String.

(* Interface string Values *)
Definition STR_REQ_PLC : string := "REQ_PLC".
Definition STR_TERM : string := "TERM".
Definition STR_RAWEV : string := "RAWEV".
Definition STR_SUCCESS : string := "SUCCESS".
Definition STR_PAYLOAD : string := "PAYLOAD".
Definition STR_EVIDENCE : string := "EVIDENCE".

Definition STR_ACTION : string := "ACTION".
Definition STR_TYPE : string := "TYPE".

Definition STR_RUN : string := "RUN".
Definition STR_APPSUMM : string := "APPSUMM".
Definition STR_NEGOTIATE : string := "NEGOTIATE".
Definition STR_APPRAISE : string := "APPRAISE".
Definition STR_REQUEST : string := "REQUEST".
Definition STR_RESPONSE : string := "RESPONSE".

Definition STR_ATTEST_SESS : string := "ATTESTATION_SESSION".

(* ASP String Admits *)
Definition STR_ASP : string := "ASP".
Definition STR_ASP_RUN : string := "ASP_RUN".
Definition STR_ASP_ID : string := "ASP_ID".
Definition STR_ASP_ARGS : string := "ASP_ARGS".
Definition STR_ASP_PLC : string := "ASP_PLC".
Definition STR_ASP_TARG_ID : string := "ASP_TARG_ID".

Definition type_string_constant : string := "CONSTRUCTOR".
Definition body_string_constant : string := "BODY".
Definition type_sep : string := "_".

Definition fwd_name_constant  : string := "FWD".
Definition replace_name_constant : string := "REPLACE".
Definition wrap_name_constant : string := "WRAP".
Definition unwrap_name_constant : string := "UNWRAP".
Definition extend_name_constant : string := "EXTEND".

Definition mt_name_constant : string := "mt_evt".
Definition nonce_evt_name_constant : string := "nonce_evt".
Definition asp_evt_name_constant : string := "asp_evt".
Definition left_evt_name_constant : string := "left_evt".
Definition right_evt_name_constant : string := "right_evt".

Definition split_evt_name_constant : string := "split_evt".

Definition asp_name_constant  : string := "asp".
Definition null_name_constant : string := "NULL".
Definition appr_name_constant : string := "APPR".
Definition copy_name_constant : string := "CPY".
Definition aspc_name_constant : string := "ASPC".
Definition sig_name_constant  : string := "SIG".
Definition hsh_name_constant  : string := "HSH".
Definition enc_name_constant  : string := "ENC".

Definition evidencet_name_constant : string := "EvidenceT".

Definition att_name_constant  : string := "att".
Definition lseq_name_constant : string := "lseq".
Definition bseq_name_constant : string := "bseq".
Definition bpar_name_constant : string := "bpar".

Definition rawev_name_constant : string := "RawEv".

Definition sp_name_constant   : string := "SP".
Definition all_name_constant  : string := "ALL".
Definition none_name_constant : string := "NONE".

Definition split1_name_constant : string := "split1".
Definition split2_name_constant : string := "split2".

Definition ev_out_sig_name_constant : string := "EvOutSig".
Definition outn_name_constant : string := "OutN".
Definition outunwrap_name_constant : string := "OutUnwrap".

Definition asp_types_name_constant : string := "ASP_Types".
Definition asp_comps_name_constant : string := "ASP_Comps".

Definition ev_in_sig_name_constant : string := "EvInSig".

Definition term_plc_list_name_constant : string := "Term_Plc_List".