
(** Abstract definitions for cryptographic ASP parameters.
        These act as default parameters to cryptographic functions (e.g. signing, hashing)
        that should be instantiated on a per-AM/per-platform basis. *)

From CoplandSpec Require Import Term_Defs_Core.
Local Open Scope string_scope.

Definition sig_aspid : ASP_ID := "sig".
Definition sig_aspargs : ASP_ARGS := JSON_Object [].
Definition sig_targid : ASP_ID := "sig_targ".
Definition sig_targplc : Plc := "sig_targplc".
Definition sig_params : ASP_PARAMS :=
    asp_paramsC sig_aspid sig_aspargs sig_targplc sig_targid.

Definition check_nonce_aspid : ASP_ID := "check_nonce".
Definition check_nonce_aspargs : ASP_ARGS := JSON_Object [].
Definition check_nonce_targid : ASP_ID := "check_nonce_targ".
Definition check_nonce_targplc : Plc := "check_nonce_targplc".
Definition check_nonce_params : ASP_PARAMS :=
    asp_paramsC check_nonce_aspid check_nonce_aspargs check_nonce_targplc check_nonce_targid.

Definition hsh_aspid : ASP_ID := "hsh".
Definition hsh_aspargs : ASP_ARGS := JSON_Object []. 
Definition hsh_targid : ASP_ID := "hsh_targ".
Definition hsh_targplc : Plc := "hsh_targplc".
Definition hsh_params : ASP_PARAMS :=
    asp_paramsC hsh_aspid hsh_aspargs hsh_targplc hsh_targid.

Definition enc_aspid : ASP_ID := "enc".
Definition enc_aspargs : ASP_ARGS := JSON_Object [].
Definition enc_targid : ASP_ID := "enc_targ".
Definition enc_params : Plc -> ASP_PARAMS :=
  fun enc_targplc => asp_paramsC enc_aspid enc_aspargs enc_targplc enc_targid.
Close Scope string_scope.