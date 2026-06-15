(** A worked cross-place / cryptographic example exercising the WRAP/UNWRAP
    machinery (ENC / @ / the synthesized DEC) and the [tc_appr_asp_unwrap_wrap]
    typing rule, which the flagship INSPECTA example never touches.

    Narrative: a target [P] measures a kernel ([kim]), encrypts the result
    toward a remote appraiser [R] (ENC R = a WRAP), and ships it (@R).  The
    appraiser writes only [APPR]; the type system synthesizes the matching
    decryption ([dec] = the UNWRAP counterpart of [enc]) and, after the
    WRAP/UNWRAP pair cancels under normalization, the kernel-appraisal step.

    Identifiers in the spec are abstract ([ID_Type] is opaque), so -- exactly as
    in the rest of the mechanization -- the context's signature lookups are
    hypotheses rather than computed.  The lemma therefore states: *every* Global
    Context that assigns the expected signatures types this protocol. *)

From CoplandSpec Require Import
  Term_Defs_Core Term_Defs_Core_Typeclasses Term_Defs Built_In_Params
  Normalize TypeSys.
From Equations Require Import Equations.
From RocqCandy Require Import All.

Definition one_pos : pos_nat := exist _ 1 (Nat.lt_0_succ 0).

Section CryptoExample.
  Variable G : GlobalContext.
  Variables P R : Plc.
  Variables kim_aspid appr_kim_aspid dec_aspid : ASP_ID.

  (* enc is the built-in WRAP; dec its UNWRAP counterpart; kim a fresh
     measurement; appr_kim the appraisal counterpart of kim. *)
  Hypothesis Henc  : (asp_types G) ![ enc_aspid ] = Some (ev_arrow (WRAP one_pos) []).
  Hypothesis Hdec  : (asp_types G) ![ dec_aspid ] = Some (ev_arrow UNWRAP []).
  Hypothesis Hkim  : (asp_types G) ![ kim_aspid ]
                       = Some (ev_arrow (EXTEND one_pos InNone) []).
  Hypothesis Happr : (asp_types G) ![ appr_kim_aspid ]
                       = Some (ev_arrow (REPLACE one_pos) []).
  Hypothesis Hcenc : (asp_comps G) ![ enc_aspid ] = Some dec_aspid.
  Hypothesis Hckim : (asp_comps G) ![ kim_aspid ] = Some appr_kim_aspid.

  Definition kim_params : ASP_PARAMS := asp_paramsC kim_aspid (JSON_Object []).
  Definition e_meas : EvidenceT := asp_evt P kim_params mt_evt.
  Definition e_enc  : EvidenceT := asp_evt P (enc_params R) e_meas.

  (* The protocol:  kim  ->  ENC R  ->  @R APPR    (executed at P). *)
  Definition crypto_term : Term :=
    lseq (asp (ASPC kim_params)) (lseq (asp (ENC R)) (att R (asp APPR))).

  (* --- Normalization facts -------------------------------------------------*)

  (* The measurement and the encrypted evidence are already canonical. *)
  Lemma norm_e_meas : normalize_ev G e_meas = e_meas.
  Proof.
    unfold e_meas, kim_params.
    erewrite normalize_asp_keep with (fwd := EXTEND one_pos InNone).
    - ltac1:(simp normalize_ev); reflexivity.
    - exact Hkim.
    - discriminate.
  Qed.

  Lemma norm_e_enc : normalize_ev G e_enc = e_enc.
  Proof.
    unfold e_enc, enc_params.
    erewrite normalize_asp_keep with (fwd := WRAP one_pos).
    - rewrite norm_e_meas; reflexivity.
    - exact Henc.
    - discriminate.
  Qed.

  (* The synthesized DEC applied to the encrypted evidence cancels the ENC:
     normalize_ev G (dec (enc (kim mt))) = kim mt.  This is the crux of the
     T-Appr-Unwrap rule. *)
  Lemma norm_cancel :
    normalize_ev G (asp_evt R (asp_paramsC dec_aspid (enc_aspargs R)) e_enc)
      = e_meas.
  Proof.
    ltac1:(simp normalize_ev).
    rewrite norm_e_enc. unfold e_enc, enc_params. cbn.
    rewrite Hdec. cbn.
    rewrite Henc. cbn.
    rewrite Hcenc. cbn.
    ltac1:(destruct (DecEq.dec_eq dec_aspid dec_aspid) as [ Heq | Hne]).
    - reflexivity.
    - ltac1:(exfalso; apply Hne; reflexivity).
  Qed.

  (* --- The type-checking derivation ---------------------------------------*)

  (* Appraising the (decrypted) measurement: APPR on anything normalizing to
     kim(mt) synthesizes appr_kim and records its check. *)
  Lemma appr_meas : forall e,
    normalize_ev G e = e_meas ->
    typeof G R e (asp APPR)
      (split_evt (asp_evt R (asp_paramsC appr_kim_aspid (JSON_Object [])) e) mt_evt).
  Proof.
    intros e Hnorm.
    eapply tc_appr_asp_extend with (appr_id := appr_kim_aspid) (fwd := REPLACE one_pos).
    - (* recursively appraise the inner mt *)
      eapply tc_appr_mt. ltac1:(simp normalize_ev); reflexivity.
    - unfold e_meas, kim_params in Hnorm. exact Hnorm.
    - exact Happr.
    - exact Hckim.
    - exact Hkim.
    - discriminate.
  Qed.

  Lemma denot_e_meas : evt_stack_denotation G e_meas 1.
  Proof.
    unfold e_meas, kim_params.
    eapply interp_asp_extend with (n_ext := 1) (n := 0).
    - exact Hkim.
    - econstructor.
  Qed.

  Theorem crypto_appraisal_example :
    typeof G P mt_evt crypto_term
      (split_evt
        (asp_evt R (asp_paramsC appr_kim_aspid (JSON_Object []))
          (asp_evt R (asp_paramsC dec_aspid (enc_aspargs R)) e_enc))
        mt_evt).
  Proof.
    unfold crypto_term.
    (* kim : mt ==> e_meas *)
    eapply tc_lseq with (e1 := e_meas).
    { eapply tc_extend_in_none.
      - econstructor.
      - unfold kim_params. exact Hkim. }
    (* ENC R : e_meas ==> e_enc *)
    eapply tc_lseq with (e1 := e_enc).
    { eapply tc_enc.
      - exact denot_e_meas.
      - ltac1:(lia).
      - exact Henc. }
    (* @R APPR *)
    eapply tc_att.
    (* APPR on e_enc at R : fires tc_appr_asp_unwrap_wrap *)
    eapply tc_appr_asp_unwrap_wrap
      with (aid := enc_aspid) (appr_id := dec_aspid) (e' := e_meas).
    - (* premise 1: appraise the inner (wrapped) evidence e_meas *)
      eapply appr_meas. exact norm_e_meas.
    - (* premise 2: appraise the synthesized DEC applied to e_enc *)
      eapply appr_meas. exact norm_cancel.
    - (* e_enc normalizes to the wrapped term *)
      unfold e_enc, enc_params. exact norm_e_enc.
    - exact Hdec.
    - exact Hcenc.
    - exact Henc.
  Qed.

End CryptoExample.
