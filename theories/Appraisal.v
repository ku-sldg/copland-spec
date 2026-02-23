From Equations Require Import Equations.
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs_Core TypeSys
  Term_Defs_Core_Typeclasses Term_Defs.
From Stdlib Require Import Permutation.

Definition AppraisalSummary := (Map ASP_PARAMS RawEv).

Fixpoint flatten {A B} `{DecEq A} (m : Map A B) : list B :=
  match m with
  | [] => []
  | (k, v) :: rest => v :: flatten rest
  end.

Fixpoint appify {A B} `{DecEq A} (m : Map A (list B)) : list B :=
  match m with
  | [] => []
  | (k, v) :: rest => v ++ appify rest
  end.

Lemma appify_app : forall A B `{DecEq A} (m1 m2 : Map A (list B)),
  appify (m1 ++ m2) = appify m1 ++ appify m2.
Proof.
  induction m1; ff;
  erewrite <- app_assoc; ff.
Qed.

Definition flatten_appraisal_summary (s : AppraisalSummary) : RawEv :=
  appify s.

(* The correctness condition for the appraisal summary:
all the evidence that appears in the original raw evidence "r" must be
"accounted for" in the appraisal summary. This means essentially
that if we flattened the appraisal summary back into raw evidence,
it would be a permutation of the original input raw evidence "r".
*)
Definition appr_summary_correct (r : RawEv) (s : AppraisalSummary) 
    : Prop :=
  Permutation r (flatten_appraisal_summary s).

Equations? do_appraisal_summary (G : GlobalContext) (r : RawEv) 
    (p : Plc) (et:EvidenceT)
    ( Hty : { et' & typeof G p et' (asp APPR) et })
    ( Hsize : evt_stack_denotation G et (length r) )
    : { s : AppraisalSummary | appr_summary_correct r s } 
      by wf (EvidenceT_depth (normalize_ev G (projT1 Hty))) :=
  do_appraisal_summary G r p mt_evt Hty Hsize := 
    exist (appr_summary_correct r) [] _;
  do_appraisal_summary G r p (nonce_evt nid) Hty Hsize := _;
  do_appraisal_summary G r p (asp_evt p' asp_params et') Hty Hsize := _;
  do_appraisal_summary G r p (left_evt et') Hty Hsize := _;
  do_appraisal_summary G r p (right_evt et') Hty Hsize := _;
  do_appraisal_summary G r p (split_evt et1 et2) Hty Hsize := _.
Proof.
  all: subst; unfold appr_summary_correct.
  - invc Hsize.
    assert (r = []) by (destruct r; ff with l; fail).
    ff.
  - eapply no_tc_nonce in X as ?; ff.
  - inv X; (try (normer; fail)).
    * (* mt *)
      destruct asp_params; normer.
      invc Hsize; normer.
      invc X0.
      exists [].
      assert (r = []) by (destruct r; ff with l; fail).
      ff.
    * (* nonce *)
      invc Hsize; normer.
      exists ([((check_nonce_params), r)]).
      ff; rewrite app_nil_r; ff.
    * 
      eapply (typeof_norm_proper G _ _ e') in X0 as ? > [
        | eapply normalize_ev_done in H as ?; normer
      ].
      destruct X1 as [ evv Htyev Hnev ].
      eapply evt_stack_denotation_transfer in Hsize as ? > [
        | eapply Hnev
      ].
      eapply (do_appraisal_summary G r p evv (existT _ e' Htyev) X1).
      ff with l.
      assert (normalize_ev G e' = e'). {
        eapply normalize_ev_done in H as ?; normer.
      }
      eapply normalize_ev_measure_decrease in H as ?.
      ff with l.
    * 
      destruct fwd; ff.
      + (* outer is REPLACE *)
        invc Hsize; normer.
        exists ([((asp_paramsC aid args), r)]).
        ff; rewrite app_nil_r; ff.
      + (* outer is WRAP - equivalent to REPLACE - weird but okay? *)
        invc Hsize; normer.
        exists ([((asp_paramsC aid args), r)]).
        ff; rewrite app_nil_r; ff.
      + (* outer is extend, inner is replace! *)
        inv Hsize; normer.
        destruct (peel_n_rawev n_ext r) as [[l1 l2] |] eqn:Hpeel;
        try (  find_eapply_lem_hyp peel_n_rawev_none_spec; ff with l).
        eapply peel_n_rawev_result_spec in Hpeel; ff.
        rewrite length_app in *.
        assert (n1 = Datatypes.length l2) by (ff with l); ff.
        exists ([((asp_paramsC appr_id args), l1)] ++ [((asp_paramsC aid args), l2)]).
        ff.
        rewrite app_nil_r.
        pp Permutation_app.
        ff.
  - eapply no_tc_left in X as ?; normer.
    eapply equiv_preserves_denotation_size_fwd in Hsize.
    normer; invc Hsize.
    assert (r = []) by (destruct r; ff with l; fail).
    exists []; ff.
  - eapply no_tc_right in X as ?; normer.
    eapply equiv_preserves_denotation_size_fwd in Hsize.
    normer; invc Hsize.
    assert (r = []) by (destruct r; ff with l; fail).
    exists []; ff.
  - (* split_evt *)
    inv Hsize.
    eapply tc_split_eventually_resolves in X as HS.
    destruct HS as [e_inner [Hchain [Hextend | Hsplit]]].

    * (* EXTEND: recurse *)
      destruct Hextend as [[[[[[[[[[aid p'] args] e'] nv] isig] attrs'] appr_id] fwd] attrs] [[[[[[Hn Haty] Hcomp] Happty] Hfwd] Heveq] Htyv]].
      destruct (peel_n_rawev s1 r) as [[l1 l2] |] eqn:Hpeel;
      try (  find_eapply_lem_hyp peel_n_rawev_none_spec; ff with l).
      eapply peel_n_rawev_result_spec in Hpeel; ff.
      rewrite length_app in *.
      assert (s2 = Datatypes.length l2) by (ff with l); ff.

      assert ({ s : AppraisalSummary | appr_summary_correct l2 s }). {
        eapply (do_appraisal_summary G l2 p et2 (existT _ e' Htyv) X1).
        ff with l.
        eapply appr_unwrap_chain_measure_decreases in Hchain.
        eapply normalize_ev_measure_decrease in Hn as ?. 
        assert (normalize_ev G e' = e') by (eapply normalize_ev_done in Hn as ?; normer).
        ff with l.
      }
      unfold appr_summary_correct in *.
      destruct X2 as [l2rw Hl2].
      exists ([((asp_paramsC aid args), l1)] ++ l2rw).
      pp Permutation_app.
      ff.
    * 
    destruct Hsplit as [[el er] [[Hn Htyl] Htyr]].
    eapply appr_unwrap_chain_measure_decreases in Hchain as ?.
    destruct (peel_n_rawev s1 r) as [[l1 l2] |] eqn:Hpeel;
    try (  find_eapply_lem_hyp peel_n_rawev_none_spec; ff with l).
    eapply peel_n_rawev_result_spec in Hpeel; ff.
    rewrite length_app in *.
    assert (s2 = Datatypes.length l2) by (ff with l); ff.
    eapply normalize_ev_measure_decrease in Hn as ?; ff with l.
    destruct (do_appraisal_summary G _ p et1 (existT _ (left_evt e_inner) Htyl) X0) as [S1 Hsum1].
    ff with l; norm; ff with l.
    destruct (do_appraisal_summary G _ p et2 (existT _ (right_evt e_inner) Htyr) X1) as [S2 Hsum2].
    ff with l; norm; ff with l.
    exists (S1 ++ S2).
    unfold appr_summary_correct, flatten_appraisal_summary in *.
    erewrite appify_app in *.
    eapply Permutation_app; ff.
Defined.