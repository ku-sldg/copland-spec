(** * Agreement between the [typeof] type system and the [eval] reference semantics

    This file establishes the bridge that the type system [typeof] (TypeSys.v)
    is *sound* with respect to the Copland evidence reference semantics [eval]
    (Term_Defs.v): every output evidence predicted by the type system is the
    evidence actually computed by [eval].

    Note that the converse does NOT hold: [eval] is permissive (e.g. [eval_asp]
    produces a [SIG] node without checking the stack-denotation/[asp_types] side
    conditions that [typeof] requires), so [eval] succeeding does not imply
    well-typedness. Soundness (typeof -> eval) is the meaningful direction: it
    says the type checker never predicts an output the semantics would not
    produce. *)

From CoplandSpec Require Import
  Term_Defs_Core Term_Defs_Core_Typeclasses Event_System Term_Defs TypeSys.
From RocqCandy Require Import All.
From Equations Require Import Equations.
Import ResultNotation.

(** A term is [appr_free] when it contains no [APPR] primitive. For such terms
    the soundness proof is purely structural and does not depend on the
    appraisal-synthesis machinery. *)
Fixpoint appr_free (t : Term) : Prop :=
  match t with
  | asp APPR => False
  | asp _ => True
  | att _ t' => appr_free t'
  | lseq t1 t2 => appr_free t1 /\ appr_free t2
  | bseq _ t1 t2 => appr_free t1 /\ appr_free t2
  | bpar _ t1 t2 => appr_free t1 /\ appr_free t2
  end.

(** Soundness of the type system w.r.t. the reference semantics, for the
    appraisal-free fragment (the entire non-[APPR] Copland language). *)
Theorem typeof_sound_wrt_eval_appr_free : forall G p e t e',
  appr_free t ->
  typeof G p e t e' ->
  eval G p e t = res e'.
Proof.
  (* Worked in Ltac1 (this file is in Ltac2 mode by default): induct on the
     typing derivation; the APPR cases are vacuous (appr_free reduces to [False]),
     and the atomic/att/seq/branch cases reduce [eval], discharge the
     appr_free-conditioned IHs, and reduce each Result [bind] on its [res]. *)
  intros G p e t e' Hf H; revert Hf;
  induction H; intros Hf; cbn in Hf |- *;
  try (ltac1:(solve [ exfalso; assumption ]));
  repeat (match! goal with [ hH : _ /\ _ |- _ ] => let hv := Control.hyp hH in destruct $hv end);
  repeat (match! goal with
          | [ ih : (appr_free ?_x -> _), hp : appr_free ?_x |- _ ] => 
            let ihv := Control.hyp ih in
            let hpv := Control.hyp hp in
            specialize ($ihv $hpv)
          end);
  cbn;
  repeat (match! goal with
          | [ he : eval _ _ _ _ = res _ |- _ ] => 
            let hev := Control.hyp he in
            rewrite $hev
          end;
          cbv [bind]);
  try reflexivity.
Qed.

(** ** The APPR case

    Extending the bridge to [APPR] (where [eval (asp APPR) = appr_procedure])
    initially exposed a mismatch: [appr_procedure']'s [mt_evt] case returned the
    literal [mt_evt], discarding its [ev_out] accumulator, whereas the relational
    [tc_appr_mt] outputs the input evidence. They diverged when a split branch
    that merely *normalizes* to [mt_evt] is appraised through a projection
    (reachable via [tc_appr_split]). We aligned [appr_procedure']'s [mt_evt] case
    to thread [ev_out] (Term_Defs.v), consistent with its other cases, restoring
    an exact correspondence between the relational and executable appraisal. *)

(** *** The exact APPR bridge (now proved in full)

    Two changes made the APPR bridge exact and its proof tractable:

    1. [appr_procedure] was *corrected* to normalize its structural argument
       (Term_Defs.v: [appr_procedure G p e := appr_procedure' G p (normalize_ev G e) e]),
       so its recursion stays canonical and mirrors the relational [tc_appr_*]
       rules, while the raw [e] is threaded as the output accumulator so outputs
       are built from the raw input exactly as the rules prescribe.

    2. [appr_procedure']'s defensive [equiv_EvidenceT] size guard was *removed*
       (Term_Defs.v): the relational rules carry no such check, and for well-typed
       inputs it always passes, so it only obscured the correspondence. Removing it
       eliminates the [et_size]-invariance obligation entirely.

    With these, the bridge
    [[
    Theorem typeof_appr_sound : forall G p e e',
      typeof G p e (asp APPR) e' -> appr_procedure G p e = res e'.
    ]]
    holds for ALL inputs (no canonicity hypothesis needed, since [appr_procedure]
    normalizes) and reduces to the generalized lemma [appr_procedure'_sound] over
    the canonical structural argument. That lemma is proved below by structured
    induction on the [typeof] derivation: each [tc_appr_*] rule pins down the
    shape of the canonical argument, [appr_procedure'] reduces to exactly one
    branch (via the one-step unfolding equations), and the recursive cases close
    by the induction hypotheses with explicit [normalize_ev] side-conditions
    (subterm canonicity, split projection, WRAP/UNWRAP cancellation). No bare
    projection or stray top-level [UNWRAP] is reachable in a well-typed APPR
    derivation, so those executable branches never arise. *)

(** *** Empirical validation of the canonical-argument discipline

    [appr_procedure'] recurses over the *canonical* structural argument only.
    Take [e = SIG] (an [EXTEND]) over a projection
    [left_evt (split (nonce 1) (nonce 2))] that normalizes to [nonce 1]: fed the
    raw projection directly, the structural recursion is stuck and errs, while
    the normalizing wrapper [appr_procedure] appraises the canonical [nonce 1]
    -- exactly the output [tc_appr_extend] assigns (its right premise appraises
    the inner of [normalize_ev G e]). *)
Module CorrectionValidation.
  Example correction_matters : forall (G : GlobalContext) p appr_sig_id sig_attrs nlt,
    (asp_types G) ![ sig_aspid ] = Some (ev_arrow (EXTEND (exist _ 1 nlt) InAll) sig_attrs) ->
    (asp_comps G) ![ sig_aspid ] = Some appr_sig_id ->
    (* raw (non-canonical) structural argument: the stuck projection errs *)
    appr_procedure' G p
      (asp_evt p sig_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
      (asp_evt p sig_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
    = err err_str_no_evidence_below
    /\
    (* the normalizing [appr_procedure]: inner built from the CANONICAL nonce
       (matches tc_appr_extend) *)
    appr_procedure G p
      (asp_evt p sig_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
    = res (split_evt
             (asp_evt p (asp_paramsC appr_sig_id sig_aspargs)
                (asp_evt p sig_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2)))))
             (asp_evt p check_nonce_params (nonce_evt 1))).
  Proof.
    intros G p appr_sig_id sig_attrs nlt Ht Hc.
    split.
    - unfold sig_params.
      simpl.
      rewrite Ht.
      rewrite Hc.
      reflexivity.
    - unfold appr_procedure.
      assert (normalize_ev G (asp_evt p sig_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
              = asp_evt p sig_params (nonce_evt 1)) as Hn.
      { unfold sig_params; ltac1:(simp normalize_ev); reflexivity. }
      rewrite Hn; unfold sig_params;
      ff with a, r, u, l.
  Qed.
End CorrectionValidation.

(** ** Normalization facts used by the appraisal-soundness induction

    Each names a single computational property of [normalize_ev] and is proved
    by Equations simplification ([simp normalize_ev]) plus explicit rewriting. *)

(** The immediate argument of a canonical non-[UNWRAP] [asp_evt] is canonical. *)
Lemma canon_asp_inner : forall G e p' aid args e' fwd attrs,
  normalize_ev G e = asp_evt p' (asp_paramsC aid args) e' ->
  (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
  fwd <> UNWRAP ->
  normalize_ev G e' = e'.
Proof.
  intros G e p' aid args e' fwd attrs He Htype Hfwd.
  eapply normalize_ev_done in He as Hc.
  rewrite (normalize_asp_keep G p' aid args e' fwd attrs Htype Hfwd) in Hc.
  ltac1:(injection Hc; intros; assumption).
Qed.

(** Both immediate components of a canonical split are canonical. *)
Lemma canon_split : forall G e el er,
  normalize_ev G e = split_evt el er ->
  normalize_ev G el = el /\ normalize_ev G er = er.
Proof.
  intros G e el er He.
  eapply normalize_ev_done in He as Hc.
  ltac1:(simp normalize_ev in Hc).
  ltac1:(injection Hc; intros; split; assumption).
Qed.

(** Projecting a canonical split: [left_evt]/[right_evt] read off its components. *)
Lemma normalize_left_split : forall G e el er,
  normalize_ev G e = split_evt el er ->
  normalize_ev G (left_evt e) = el.
Proof.
  intros G e el er He.
  ltac1:(simp normalize_ev).
  rewrite He. reflexivity.
Qed.

Lemma normalize_right_split : forall G e el er,
  normalize_ev G e = split_evt el er ->
  normalize_ev G (right_evt e) = er.
Proof.
  intros G e el er He.
  ltac1:(simp normalize_ev).
  rewrite He. reflexivity.
Qed.

(** WRAP/UNWRAP cancellation: applying the dual [UNWRAP] ASP to evidence whose
    normal form is the matching [WRAP] reduces, under normalization, to the
    wrapped argument. This is the executable counterpart of the
    [tc_appr_asp_unwrap_wrap] rule recursing on the unwrapped evidence. *)
Lemma normalize_unwrap_cancel : forall G p p' appr_id aid args attrs nv attrs' e e',
  normalize_ev G e = asp_evt p' (asp_paramsC aid args) e' ->
  (asp_types G) ![ appr_id ] = Some (ev_arrow UNWRAP attrs) ->
  (asp_comps G) ![ aid ] = Some appr_id ->
  (asp_types G) ![ aid ] = Some (ev_arrow (WRAP nv) attrs') ->
  normalize_ev G (asp_evt p (asp_paramsC appr_id args) e) = e'.
Proof.
  intros G p p' appr_id aid args attrs nv attrs' e e' He Hunwrap Hcomp Hwrap.
  ltac1:(simp normalize_ev).
  rewrite He, Hunwrap.
  ltac1:(destruct nv as [nv_n nv_lt]).
  rewrite Hwrap, Hcomp.
  ltac1:(destruct (DecEq.dec_eq appr_id appr_id) as [_ | Hneq]).
  - reflexivity.
  - ltac1:(exfalso; apply Hneq; reflexivity).
Qed.

(** Generalized soundness of the executable appraisal: for a canonical
    structural argument [e_struct] sharing [ev_out]'s normal form,
    [appr_procedure'] reproduces exactly the output [typeof] assigns to
    appraising [ev_out]. Proved by induction on the [typeof] derivation
    (mirroring [CSA_appraisal_sound]); the [ev_out]-canonicity facts feed the
    induction hypotheses on the canonical direct subterms. *)
Lemma appr_procedure'_sound : forall G p ev_out e' e_struct,
  normalize_ev G e_struct = e_struct ->
  normalize_ev G e_struct = normalize_ev G ev_out ->
  typeof G p ev_out (asp APPR) e' ->
  appr_procedure' G p e_struct ev_out = res e'.
Proof.
  intros G p ev_out e' e_struct Hcanon Heq Htype.
  (* Induct on the typing derivation. The term is fixed as [asp APPR], so only
     the six [tc_appr_*] rules survive ([discriminate Heqt] kills the rest). In
     every surviving case the rule pins down [normalize_ev G ev_out], hence (via
     [Hcanon]/[Heq]) the shape of the canonical structural argument [e_struct],
     so [appr_procedure'] reduces to exactly one branch. *)
  ltac1:( generalize dependent e_struct ).
  prep_induction Htype.
  induction Htype; intros Heqt e_struct Hcanon Heq;
    try (ltac1:(discriminate Heqt)).
  - (* tc_appr_mt : e_struct = mt_evt, output is the input ev_out [= e] *)
    assert (Hes : e_struct = mt_evt) by (rewrite <- Hcanon; rewrite Heq; exact e0);
    subst e_struct; eauto.
  - (* tc_appr_nonce : e_struct = nonce_evt n, output checks the nonce *)
    assert (Hes : e_struct = nonce_evt n) by (rewrite <- Hcanon; rewrite Heq; exact e0);
    subst e_struct; eauto.
  - (* tc_appr_asp_unwrap_wrap : e_struct = asp_evt .. (WRAP aid) ..; the dual
       UNWRAP fires, recursing on the unwrapped evidence via IHHtype2 *)
    assert (Hes : e_struct = asp_evt p' (asp_paramsC aid args) e')
      by (rewrite <- Hcanon; rewrite Heq; exact e0);
    subst e_struct; cbn; rewrite e3; rewrite e2;
    cbn beta iota zeta; rewrite e1; cbn beta iota zeta;
    assert (Hin : normalize_ev G e' = e')
      by (eapply canon_asp_inner > [ exact e0 | exact e3 | discriminate ]);
    assert (Hcancel : normalize_ev G (asp_evt p (asp_paramsC appr_id args) e) = e')
      by (eapply normalize_unwrap_cancel > [ exact e0 | exact e1 | exact e2 | exact e3 ]);
    eapply IHHtype2 > [ reflexivity | exact Hin | rewrite Hcancel; exact Hin ].
  - (* tc_appr_asp_replace : e_struct = asp_evt .. (REPLACE aid) ..; dual applied once *)
    assert (Hes : e_struct = asp_evt p' (asp_paramsC aid args) e')
      by (rewrite <- Hcanon; rewrite Heq; exact e0);
    subst e_struct; cbn; rewrite e3; rewrite e2; reflexivity.
  - (* tc_appr_asp_extend : e_struct = asp_evt .. (EXTEND aid) ..; appraise the
       extension then recurse on the underlying via IHHtype *)
    assert (Hes : e_struct = asp_evt p' (asp_paramsC aid args) e')
      by (rewrite <- Hcanon; rewrite Heq; exact e0);
    subst e_struct; cbn; rewrite e3; rewrite e2; cbn;
    assert (Hin : normalize_ev G e' = e')
      by (eapply canon_asp_inner > [ exact e0 | exact e3 | discriminate ]);
    assert (Hrec : appr_procedure' G p e' e' = res e'')
      by (eapply IHHtype > [ reflexivity | exact Hin | reflexivity ]);
    rewrite Hrec; reflexivity.
  - (* tc_appr_split : e_struct = split_evt el er; appraise each projection *)
    assert (Hes : e_struct = split_evt el er)
      by (rewrite <- Hcanon; rewrite Heq; exact e0);
    subst e_struct; cbn;
    destruct (canon_split G e el er e0) as [Hcl Hcr];
    assert (Hrl : appr_procedure' G p el (left_evt e) = res el')
      by (eapply IHHtype1 >
          [ reflexivity | exact Hcl
          | rewrite Hcl; symmetry; eapply normalize_left_split; exact e0 ]);
    assert (Hrr : appr_procedure' G p er (right_evt e) = res er')
      by (eapply IHHtype2 >
          [ reflexivity | exact Hcr
          | rewrite Hcr; symmetry; eapply normalize_right_split; exact e0 ]);
    rewrite Hrl; rewrite Hrr; reflexivity.
Qed.

(** The exact APPR bridge: the corrected executable appraisal [appr_procedure]
    reproduces exactly the output the type system assigns to [APPR]. *)
Theorem typeof_appr_sound : forall G p e e',
  typeof G p e (asp APPR) e' ->
  appr_procedure G p e = res e'.
Proof.
  intros G p e e' Htype.
  eapply appr_procedure'_sound > [ 
    eapply normalize_ev_idempotent 
    | eapply normalize_ev_idempotent 
    | eapply Htype 
  ].
Qed.

(** The full bridge: the type system is sound w.r.t. the [eval] reference
    semantics for EVERY Copland phrase. The [appr_free] restriction of
    [typeof_sound_wrt_eval_appr_free] is now lifted -- the [asp APPR] cases are
    discharged by [typeof_appr_sound] (reconstructing the [typeof] derivation),
    the rest by reducing [eval] and threading the induction hypotheses. *)
Theorem typeof_sound_wrt_eval : forall G p e t e',
  typeof G p e t e' ->
  eval G p e t = res e'.
Proof.
  intros G p e t e' Htype.
  induction Htype.
  (* Non-[APPR] cases (atomic ASPs and the [att]/[lseq]/[bseq]/[bpar] operators):
     reduce [eval]/[eval_asp] to its branch and thread the evaluation IHs through
     the result-monad binds. On the [asp APPR] cases the final [reflexivity]
     fails, so [try] rolls the whole step back, leaving them untouched. *)
  all: try (ltac1:(cbn [eval eval_asp];
        repeat (match goal with
                | He : eval _ _ _ _ = res _ |- _ => rewrite He end;
                cbv [bind]);
        reflexivity)).
  (* The six [asp APPR] cases: [eval_asp APPR = appr_procedure]. [typeof_appr_sound]
     reduces each to rebuilding its [typeof .. (asp APPR) ..] derivation; the case
     still carries every premise of its rule, so re-applying that exact constructor
     and supplying the premises (by name, in order) finishes it. We name the
     hypotheses explicitly rather than search for them: [normalize_ev] takes a
     [Qed]-opaque [DecEq ASP_ID] instance, which conversion ([exact]) sees through
     but unification-keyed [assumption]/[eauto] does not. *)
  all: ltac1:(cbn [eval eval_asp]; eapply typeof_appr_sound).
  1: ltac1:(eapply tc_appr_mt; exact e0).
  1: ltac1:(eapply tc_appr_nonce; [ exact e0 | exact e1 ]).
  1: ltac1:(eapply tc_appr_asp_unwrap_wrap;
            [ exact Htype1 | exact Htype2 | exact e0 | exact e1 | exact e2 | exact e3 ]).
  1: ltac1:(eapply tc_appr_asp_replace;
            [ exact Htype | exact e0 | exact e1 | exact e2 | exact e3 | exact n0 ]).
  1: ltac1:(eapply tc_appr_asp_extend;
            [ exact Htype | exact e0 | exact e1 | exact e2 | exact e3 | exact n0 ]).
  1: ltac1:(eapply tc_appr_split; [ exact e0 | exact Htype1 | exact Htype2 ]).
Qed.

(** ** Grounding [ContextSupportsAppr] in the executable semantics

    [ContextSupportsAppr] (the precondition the [APPR] typing rules check) is not
    merely a static mirror of those rules: whenever it holds, the reference
    appraisal procedure [appr_procedure] actually *runs to a result*. This is the
    forward direction of "CSA = runtime appraisal is defined": it composes the
    existing [well_typed_appraisable] (CSA yields an [APPR] typing derivation)
    with the new exact bridge [typeof_appr_sound] (that derivation's output is the
    value [appr_procedure] computes). It turns CSA from an internal predicate into
    a guarantee about the operational semantics.

    As with [typeof]/[eval], only this direction holds: [appr_procedure] is
    permissive where CSA is strict. E.g. its [nonce_evt] case succeeds
    unconditionally (Term_Defs.v), never consulting [check_nonce_aspid]'s type,
    whereas [csa_nonce] demands that lookup -- so [appr_procedure G p e = res _]
    does NOT imply [ContextSupportsAppr G e]. CSA being a *sufficient* condition
    for runtime appraisal is the meaningful claim. *)
Theorem CSA_appraisal_runs : forall G p e,
  ContextSupportsAppr G e ->
  { e' & appr_procedure G p e = res e' }.
Proof.
  intros G p e Hcsa.
  (* CSA gives a well-typed appraisal with some output [e'']... *)
  destruct (well_typed_appraisable G e p Hcsa) as [e'' Htype].
  (* ...and the bridge says [appr_procedure] computes exactly that output. *)
  exists e''.
  apply typeof_appr_sound.
  exact Htype.
Qed.

(** * Value-level type safety: evaluation preserves well-formed [Evidence]

    [wf_Evidence G (evc ls et)] says a raw-byte evidence value [ls : RawEv] has
    the length its type [et] prescribes ([et_size G et = length ls]). It is the
    only place the byte-level [RawEv] meets the type [EvidenceT], and it was
    previously unused -- never tied to the type system. We close that gap for the
    whole non-[APPR] (structural) language: a well-typed phrase maps a well-formed
    input value to a type that again admits a well-formed value.

    The crux is that well-typed evaluation keeps [et_size] *defined*: the output
    type's size is computable whenever the input's is. (Raw [eval] does NOT
    guarantee this -- it is permissive, building e.g. a [SIG] node without
    checking [sig_aspid]'s type -- so this is genuinely a property of [typeof],
    not of [eval].) For the [APPR] fragment the output size additionally needs
    relating [et_size] to the typing-side size [evt_stack_denotation] (both now
    recurse over the [normalize_ev] canonical form); bridging those is the
    remaining self-contained development, so we scope these results to
    [appr_free] terms -- exactly as the soundness bridge
    [typeof_sound_wrt_eval_appr_free] is. *)

(** The branch projections feed an input of computable size to each sub-term:
    [proc_ev_path_*] yields either the original evidence or [mt_evt]. *)
Lemma et_size_proc_left_defined : forall G ep e sz,
  et_size G e = res sz ->
  { s & et_size G (proc_ev_path_left ep e) = res s }.
Proof.
  intros G ep e sz H; destruct ep; cbn [proc_ev_path_left]; eexists;
  first [ exact H | unfold et_size; ltac1:(simp normalize_ev); reflexivity ].
Qed.

Lemma et_size_proc_right_defined : forall G ep e sz,
  et_size G e = res sz ->
  { s & et_size G (proc_ev_path_right ep e) = res s }.
Proof.
  intros G ep e sz H; destruct ep; cbn [proc_ev_path_right]; eexists;
  first [ exact H | unfold et_size; ltac1:(simp normalize_ev); reflexivity ].
Qed.


(** Core: a well-typed [appr_free] phrase keeps [et_size] defined -- if the input
    type has a computable size, so does the output type. By induction on the
    typing derivation; the [asp APPR] rules are vacuous ([appr_free] reduces to
    [False]). Each ASP rule reads its output size off the rule's [asp_types]
    premise (threading the input size for [EXTEND]); operators thread the IHs. *)
Lemma typeof_appr_free_et_size_defined : forall G p e t e' sz,
  appr_free t ->
  typeof G p e t e' ->
  et_size G e = res sz ->
  { n' & et_size G e' = res n' }.
Proof.
  intros G p e t e' sz Hf Htype. revert sz. revert Hf.
  induction Htype; intros Hf sz Hsz; cbn in Hf; try (exfalso; exact Hf).
  - (* tc_sig : SIG extends by 1 *)
    eexists; unfold sig_params;
    erewrite et_size_asp_extend > [ rewrite Hsz; reflexivity | eassumption ].
  - (* tc_hsh : HSH replaces, fixed size *)
    eexists; unfold hsh_params;
    erewrite et_size_asp_replace > [ reflexivity | eassumption ].
  - (* tc_enc : ENC wraps, fixed size *)
    eexists; unfold enc_params;
    erewrite et_size_asp_wrap > [ reflexivity | eassumption ].
  - (* tc_extend_in_none : EXTEND by n *)
    eexists; erewrite et_size_asp_extend > [ rewrite Hsz; reflexivity | eassumption ].
  - (* tc_extend_in_all : EXTEND by n_ext *)
    eexists; erewrite et_size_asp_extend > [ rewrite Hsz; reflexivity | eassumption ].
  - (* tc_in_all : forward [fwd] is REPLACE / WRAP / EXTEND (never UNWRAP) *)
    destruct fwd as [ [nr ltr] | [nw ltw] | | [ne lte] isig ]
    > [ eexists; erewrite et_size_asp_replace > [ reflexivity | eassumption ]
      | eexists; erewrite et_size_asp_wrap > [ reflexivity | eassumption ]
      | congruence   (* UNWRAP excluded by the [fwd <> UNWRAP] premise *)
      | eexists; erewrite et_size_asp_extend > [ rewrite Hsz; reflexivity | eassumption ] ].
  - (* tc_att : evaluation at a remote place, same input/output types *)
    eapply IHHtype > [ exact Hf | exact Hsz ].
  - (* tc_lseq : sequence -- thread the intermediate size through both IHs *)
    destruct Hf as [Hf1 Hf2];
    destruct (IHHtype1 Hf1 sz Hsz) as [n1 Hn1];
    eapply IHHtype2 > [ exact Hf2 | exact Hn1 ].
  - (* tc_bseq : branch -- each side gets a defined-size projection of the input *)
    destruct Hf as [Hf1 Hf2];
    destruct (et_size_proc_left_defined G ep e sz Hsz) as [sl Hsl];
    destruct (et_size_proc_right_defined G ep e sz Hsz) as [sr Hsr];
    destruct (IHHtype1 Hf1 sl Hsl) as [n1 Hn1];
    destruct (IHHtype2 Hf2 sr Hsr) as [n2 Hn2];
    eexists; rewrite et_size_split; rewrite Hn1; rewrite Hn2; reflexivity.
  - (* tc_bpar : parallel branch -- identical evidence-size reasoning to bseq *)
    destruct Hf as [Hf1 Hf2];
    destruct (et_size_proc_left_defined G ep e sz Hsz) as [sl Hsl];
    destruct (et_size_proc_right_defined G ep e sz Hsz) as [sr Hsr];
    destruct (IHHtype1 Hf1 sl Hsl) as [n1 Hn1];
    destruct (IHHtype2 Hf2 sr Hsr) as [n2 Hn2];
    eexists; rewrite et_size_split; rewrite Hn1; rewrite Hn2; reflexivity.
Qed.

(** [wf_Evidence] pins the raw length to the type's [et_size] (extracted in [Prop]
    so it can feed the [Type]-sorted realizability goal below). *)
Lemma wf_Evidence_size : forall G ls e,
  wf_Evidence G (evc ls e) ->
  et_size G e = res (List.length ls).
Proof.
  intros G ls e H; inversion H; subst; congruence.
Qed.

(** Value-level type safety (structural fragment): running a well-typed
    [appr_free] phrase on a well-formed input [Evidence] value yields a type that
    again admits a well-formed value (one of the right raw length exists). This is
    the first link from the type system to the byte-level [wf_Evidence] -- the
    previously free-floating [RawEv]/[EvidenceT] consistency invariant. *)
Theorem typeof_appr_free_preserves_wf_Evidence : forall G p e t e' ls,
  appr_free t ->
  wf_Evidence G (evc ls e) ->
  typeof G p e t e' ->
  { ls' & wf_Evidence G (evc ls' e') }.
Proof.
  intros G p e t e' ls Hf Hwf Htype.
  (* read off [et_size G e = length ls] from input well-formedness *)
  apply wf_Evidence_size in Hwf.
  destruct (typeof_appr_free_et_size_defined _ _ _ _ _ _ Hf Htype Hwf)
    as [n' Hn'].
  (* any raw evidence of the prescribed length [n'] is well-formed *)
  exists (List.repeat passed_bs n').
  econstructor > [ apply List.repeat_length | exact Hn' ].
Qed.
