From Equations Require Import Equations.
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs_Core TypeSys
  Term_Defs_Core_Typeclasses Term_Defs.
From Stdlib Require Import Permutation.

Definition AppraisalSummary := (Map (ASP_ID * ASP_ID * ASP_ARGS) (EvidenceT * RawEv)).

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
  appify (map (fun '(k, (e, r)) => (k, r)) s).

Definition heads_match G (e : EvidenceT) (aid appr_id : ASP_ID) : Prop :=
  match normalize_ev G e with
  | asp_evt p' (asp_paramsC appr_id_test args) (
      asp_evt p'' (asp_paramsC aid_test args') et''
    ) =>
    aid = aid_test /\ appr_id = appr_id_test
  | _ => False
  end.

(* This is meant to represent a nonce's creation (outside of copland, thats why we need this special definition) *)
Definition create_nonce_magic_aspid : ASP_ID := "nonce_creation"%string.

Fixpoint all_keys_provenance (G : GlobalContext) (s : AppraisalSummary) : Prop :=
  match s with
  | [] => True
  | (aid, appr_id, args, (e, r)) :: rest => 
    (* special case, it may be that it is nonce_evt *)
    match normalize_ev G e with
    | nonce_evt nid =>
      (* if it's a nonce, then we just check that the args are correct and that the evidence is a nonce *)
      aid = create_nonce_magic_aspid /\
      args = check_nonce_aspargs /\
      appr_id = check_nonce_aspid /\
      all_keys_provenance G rest
    | _ =>
      (* okay, all other cases it better be an asp case *)
      match ((asp_comps G) ![ aid ]) with
      | None => False
      | Some test_appr_id => 
        appr_id = test_appr_id /\
        heads_match G e aid appr_id /\
        all_keys_provenance G rest
      end
    end
  end.

Lemma all_keys_provenance_app : forall G s1 s2,
  all_keys_provenance G (s1 ++ s2) <-> all_keys_provenance G s1 /\ all_keys_provenance G s2.
Proof.
  split.
  - induction s1; ff with a.
  - induction s1; ff with a.
Qed.

(* The correctness condition for the appraisal summary:
all the evidence that appears in the original raw evidence "r" must be
"accounted for" in the appraisal summary. This means essentially
that if we flattened the appraisal summary back into raw evidence,
it would be a permutation of the original input raw evidence "r".
*)
Definition appr_summary_correct (G : GlobalContext) (r : RawEv) (s : AppraisalSummary) 
    : Prop :=
  Permutation r (flatten_appraisal_summary s) /\
  all_keys_provenance G s.

Equations? do_appraisal_summary_core (G : GlobalContext) (r : RawEv) 
    (p : Plc) (et:EvidenceT)
    ( Hty : { et' & typeof G p et' (asp APPR) et })
    ( Hsize : evt_stack_denotation G et (length r) )
    : { s : AppraisalSummary | appr_summary_correct G r s } 
      by wf (EvidenceT_depth (normalize_ev G (projT1 Hty))) :=
  do_appraisal_summary_core G r p mt_evt Hty Hsize := 
    exist (appr_summary_correct G r) [] _;
  do_appraisal_summary_core G r p (nonce_evt nid) Hty Hsize := _;
  do_appraisal_summary_core G r p (asp_evt p' asp_params et') Hty Hsize := _;
  do_appraisal_summary_core G r p (left_evt et') Hty Hsize := _;
  do_appraisal_summary_core G r p (right_evt et') Hty Hsize := _;
  do_appraisal_summary_core G r p (split_evt et1 et2) Hty Hsize := _.
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
      exists ([((create_nonce_magic_aspid, check_nonce_aspid, check_nonce_aspargs), (et', r))]).
      ff; rewrite app_nil_r; ff.
    * 
      eapply (typeof_norm_proper G _ _ e') in X1 as ? > [
        | eapply normalize_ev_done in H as ?; normer
      ].
      destruct X2 as [ evv Htyev Hnev ].
      eapply evt_stack_denotation_transfer in Hsize as ? > [
        | eapply Hnev
      ].
      eapply (do_appraisal_summary_core G r p evv (existT _ e' Htyev) X2).
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
        exists ([((aid, appr_id, args), (asp_evt p' (asp_paramsC appr_id args) et', r))]).
        split > [ ff; rewrite app_nil_r; ff | ].
        ff; try (normer; fail).
        unfold heads_match; normer.
      + (* outer is WRAP - equivalent to REPLACE - weird but okay? *)
        invc Hsize; normer.
        exists ([((aid, appr_id, args), (asp_evt p' (asp_paramsC appr_id args) et', r))]).
        split > [ ff; rewrite app_nil_r; ff | ].
        ff; try (normer; fail).
        unfold heads_match; normer.
      + (* outer is extend, inner is replace, but thats just the measurement!! *)
        inv Hsize; normer.
        exists ([((aid, appr_id, args), (asp_evt p' (asp_paramsC appr_id args) et', r))]).
        split > [ ff; rewrite app_nil_r; ff | ].
        ff; try (normer; fail).
        unfold heads_match; normer.
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
      destruct Hextend as [[[[[[[[[[aid p'] args] e'] nv] isig] attrs'] appr_id] fwd] attrs] Htyv [Hn [Haty [Hcomp [Happty [Hfwd Heveq]]]]]].
      destruct (peel_n_rawev s1 r) as [[l1 l2] |] eqn:Hpeel;
      try (  find_eapply_lem_hyp peel_n_rawev_none_spec; ff with l).
      eapply peel_n_rawev_result_spec in Hpeel; ff.
      rewrite length_app in *.
      assert (s2 = Datatypes.length l2) by (ff with l); ff.

      assert ({ s : AppraisalSummary | appr_summary_correct G l2 s }). {
        eapply (do_appraisal_summary_core G l2 p et2 (existT _ e' Htyv) X1).
        ff with l.
        eapply appr_unwrap_chain_measure_decreases in Hchain.
        eapply normalize_ev_measure_decrease in Hn as ?. 
        assert (normalize_ev G e' = e') by (eapply normalize_ev_done in Hn as ?; normer).
        ff with l.
      }
      unfold appr_summary_correct in *.
      destruct X2 as [l2rw Hl2].
      exists ([((aid, appr_id, args), (asp_evt p (asp_paramsC appr_id args) e_inner,  l1))] ++ l2rw).
      pp Permutation_app.
      split > [ ff | ].
      ff; try (normer; fail).
      unfold heads_match; normer.
    * 
    destruct Hsplit as [[el er] [Htyl Htyr] Hn].
    eapply appr_unwrap_chain_measure_decreases in Hchain as ?.
    destruct (peel_n_rawev s1 r) as [[l1 l2] |] eqn:Hpeel;
    try (  find_eapply_lem_hyp peel_n_rawev_none_spec; ff with l).
    eapply peel_n_rawev_result_spec in Hpeel; ff.
    rewrite length_app in *.
    assert (s2 = Datatypes.length l2) by (ff with l); ff.
    eapply normalize_ev_measure_decrease in Hn as ?; ff with l.
    destruct (do_appraisal_summary_core G _ p et1 (existT _ (left_evt e_inner) Htyl) X0) as [S1 [Hperm1 Hsum1]].
    ff with l; norm; ff with l.
    destruct (do_appraisal_summary_core G _ p et2 (existT _ (right_evt e_inner) Htyr) X1) as [S2 [Hperm2 Hsum2]].
    ff with l; norm; ff with l.
    exists (S1 ++ S2).
    split.
    + unfold appr_summary_correct, flatten_appraisal_summary in *.
      erewrite map_app.
      erewrite appify_app in *.
      eapply Permutation_app; ff.
    + erewrite all_keys_provenance_app.
      ff.
Defined.

Definition do_appraisal_summary (G : GlobalContext) (r : RawEv) (p : Plc) (et:EvidenceT)
    : { s : AppraisalSummary | appr_summary_correct G r s }
      (* if it fails, some evidence of failure *)
      + { forall e', typeof G p e' (asp APPR) et -> False }
      + { evt_stack_denotation G et (length r) -> False } :=
  match (typeof_appr_invertible G p et) with
  | inleft HtyGood =>
    match (evt_stack_denotation_size G et) with
    | inleft (existT _ n HevtGood) => 
      match (dec_eq n (length r)) with
      | left Hd => 
          eq_rect_r (fun n0 =>
              evt_stack_denotation G et n0 -> _ + {evt_stack_denotation G et (Datatypes.length r) -> False})
            (fun HevtGood0 : evt_stack_denotation G et (Datatypes.length r) =>
              inleft (inleft (do_appraisal_summary_core G r p et HtyGood HevtGood0)))
            Hd HevtGood
      | right Hnd => inright (fun HC => Hnd (evt_stack_denotation_deterministic G _ _ _ HevtGood HC))
      end
    | inright HevtFail => inright (fun HC => (HevtFail _ HC))
    end
  | inright HtyFail => inleft (inright HtyFail)
  end.
