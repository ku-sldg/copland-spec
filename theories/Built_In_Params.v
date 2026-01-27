
(** Abstract definitions for cryptographic ASP parameters.
        These act as default parameters to cryptographic functions (e.g. signing, hashing)
        that should be instantiated on a per-AM/per-platform basis. *)

From CoplandSpec Require Import Term_Defs_Core.
Local Open Scope string_scope.

Definition sig_aspid : ASP_ID := "sig".
Definition sig_aspargs : ASP_ARGS := JSON_Object [].
Definition sig_params : ASP_PARAMS :=
    asp_paramsC sig_aspid sig_aspargs.

Definition check_nonce_aspid : ASP_ID := "check_nonce".
Definition check_nonce_aspargs : ASP_ARGS := JSON_Object [].
Definition check_nonce_params : ASP_PARAMS :=
    asp_paramsC check_nonce_aspid check_nonce_aspargs.

Definition hsh_aspid : ASP_ID := "hsh".
Definition hsh_aspargs : ASP_ARGS := JSON_Object []. 
Definition hsh_params : ASP_PARAMS :=
    asp_paramsC hsh_aspid hsh_aspargs.

Definition enc_aspid : ASP_ID := "enc".
Definition enc_target : string := "enc_targ".
Definition enc_aspargs : string -> ASP_ARGS := 
  fun enc_targ_plc => JSON_Object [(enc_target, JSON_String enc_targ_plc)].
Definition enc_params : Plc -> ASP_PARAMS :=
  fun enc_targplc => asp_paramsC enc_aspid (enc_aspargs enc_targplc).
Close Scope string_scope.