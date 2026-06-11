(** * Evidence normalization

    [normalize_ev] computes the canonical form of an evidence type by resolving
    projections of splits and canceling matched WRAP/UNWRAP pairs. It is defined
    here (upstream of [Term_Defs]) so that the reference semantics' appraisal
    function [appr_procedure] can normalize its input, matching the relational
    [tc_appr_*] typing rules. Its supporting lemmas and custom induction
    principles remain in [TypeSys.v]. *)

From CoplandSpec Require Import Term_Defs_Core Term_Defs_Core_Typeclasses.
From Equations Require Import Equations.
From RocqCandy Require Import All.

Equations? normalize_ev `{DecEq ASP_ID} (G : GlobalContext) (e : EvidenceT)
    : EvidenceT by wf (EvidenceT_depth e) :=
  normalize_ev G mt_evt := mt_evt;
  normalize_ev G (nonce_evt n) := nonce_evt n;
  normalize_ev G (left_evt e') :=
    match normalize_ev G e' with
    | split_evt l r => l
    | e'res => left_evt e'res
    end;
  normalize_ev G (right_evt e') :=
    match normalize_ev G e' with
    | split_evt l r => r
    | e'res => right_evt e'res
    end;
  normalize_ev G (split_evt l r) :=
    split_evt (normalize_ev G l) (normalize_ev G r);
  normalize_ev G (asp_evt p (asp_paramsC asp_id args) e') :=
    match normalize_ev G e' with
    | asp_evt p' (asp_paramsC asp_id' args') e'' =>
        match ((asp_types G) ![ asp_id ]) with
        | Some (ev_arrow UNWRAP attrs1) =>
            match ((asp_types G) ![ asp_id' ]) with
            | Some (ev_arrow (WRAP (exist _ n nlt)) attrs2) =>
                match ((asp_comps G) ![ asp_id' ]) with
                | Some test_unwrapping_id =>
                    if (DecEq.dec_eq test_unwrapping_id asp_id)
                    then e''
                    else asp_evt p (asp_paramsC asp_id args) (asp_evt p' (asp_paramsC asp_id' args') e'')
                | None => asp_evt p (asp_paramsC asp_id args) (asp_evt p' (asp_paramsC asp_id' args') e'')
                end
            | _ => asp_evt p (asp_paramsC asp_id args) (asp_evt p' (asp_paramsC asp_id' args') e'')
            end
        | _ => asp_evt p (asp_paramsC asp_id args) (asp_evt p' (asp_paramsC asp_id' args') e'')
        end
    | e'res => asp_evt p (asp_paramsC asp_id args) e'res
    end.
- ff with l.
- ff with l.
Defined.

(** A normalized [asp_evt] whose head ASP is not [UNWRAP] keeps its head and
    normalizes only its argument (no WRAP/UNWRAP cancellation fires). *)
Lemma normalize_asp_keep : forall G p aid args e fwd attrs,
  (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
  fwd <> UNWRAP ->
  normalize_ev G (asp_evt p (asp_paramsC aid args) e)
    = asp_evt p (asp_paramsC aid args) (normalize_ev G e).
Proof.
  intros G p aid args e fwd attrs Htype Hfwd.
  ltac1:(simp normalize_ev).
  destruct (normalize_ev G e) eqn:Hne; try reflexivity.
  (* only the inner-[asp_evt] case can trigger cancellation *)
  ltac1:(destruct a).
  rewrite Htype.
  destruct fwd; try reflexivity.
  ltac1:(exfalso; apply Hfwd; reflexivity).
Qed.

Import ResultNotation.
Local Open Scope string_scope.

(** Structural size of a *canonical* evidence type. [normalize_ev] has already
    resolved projections and matched WRAP/UNWRAP pairs, so a surviving
    [left_evt]/[right_evt] or a bare [UNWRAP] asp is a stuck/ill-formed projection
    and sizes to an error (these never arise for a normalized, well-typed
    evidence). *)
Definition et_size_canon `{DecEq ASP_ID} (G : GlobalContext)
    : EvidenceT -> Result nat string :=
  fix F e :=
  match e with
  | mt_evt => res 0
  | nonce_evt _ => res 1
  | asp_evt p par e' =>
    let '(asp_paramsC asp_id args) := par in
    match ((asp_types G) ![ asp_id ]) with
    | None => err err_str_asp_no_type_sig
    | Some (ev_arrow fwd attrs) =>
      match fwd with
      | REPLACE (exist _ n _) => res n
      | WRAP (exist _ n _) => res n
      | UNWRAP => err err_str_asp_at_bottom_not_wrap
      | EXTEND (exist _ n _) i_sig => n' <- F e' ;; res (n + n')
      end
    end
  | left_evt _ => err err_str_no_evidence_below
  | right_evt _ => err err_str_no_evidence_below
  | split_evt e1 e2 => s1 <- F e1 ;; s2 <- F e2 ;; res (s1 + s2)
  end.

(** Size of an evidence type, taken over its canonical ([normalize_ev]) form.
    Normalize-invariant by construction (see [et_size_normalize], TypeSys.v). *)
Definition et_size `{DecEq ASP_ID} (G : GlobalContext) (e : EvidenceT)
    : Result nat string :=
  et_size_canon G (normalize_ev G e).

(** Definitional unfolding of [et_size_canon] on an asp node, stated so the
    recursive call appears as [et_size_canon] itself (provable by conversion). *)
Lemma et_size_canon_asp_unfold : forall G p aid args e,
  et_size_canon G (asp_evt p (asp_paramsC aid args) e) =
  match (asp_types G) ![ aid ] with
  | None => err err_str_asp_no_type_sig
  | Some (ev_arrow fwd attrs) =>
    match fwd with
    | REPLACE (exist _ n _) => res n
    | WRAP (exist _ n _) => res n
    | UNWRAP => err err_str_asp_at_bottom_not_wrap
    | EXTEND (exist _ n _) i_sig => n' <- et_size_canon G e ;; res (n + n')
    end
  end.
Proof.
  reflexivity.
Qed.

Lemma et_size_canon_split_unfold : forall G e1 e2,
  et_size_canon G (split_evt e1 e2) =
  (s1 <- et_size_canon G e1 ;; s2 <- et_size_canon G e2 ;; res (s1 + s2)).
Proof.
  reflexivity.
Qed.

(** One-step computation laws for [et_size]: normalize, then read the size off
    the canonical form ([normalize_asp_keep] pushes [normalize_ev] under a
    non-[UNWRAP] asp). *)
Lemma et_size_mt : forall G, et_size G mt_evt = res 0.
Proof.
  intros G; unfold et_size; ltac1:(simp normalize_ev); reflexivity.
Qed.

Lemma et_size_nonce : forall G n, et_size G (nonce_evt n) = res 1.
Proof.
  intros G n; unfold et_size; ltac1:(simp normalize_ev); reflexivity.
Qed.

Lemma et_size_asp_extend : forall G p aid args e n nlt isig attrs,
  (asp_types G) ![ aid ] = Some (ev_arrow (EXTEND (exist _ n nlt) isig) attrs) ->
  et_size G (asp_evt p (asp_paramsC aid args) e) = (n' <- et_size G e ;; res (n + n')).
Proof.
  ltac1:(intros G p aid args e n nlt isig attrs Hl;
    unfold et_size; rewrite (normalize_asp_keep G p aid args e _ _ Hl) by discriminate;
    cbn [et_size_canon]; rewrite Hl; reflexivity).
Qed.

Lemma et_size_asp_replace : forall G p aid args e n nlt attrs,
  (asp_types G) ![ aid ] = Some (ev_arrow (REPLACE (exist _ n nlt)) attrs) ->
  et_size G (asp_evt p (asp_paramsC aid args) e) = res n.
Proof.
  ltac1:(intros G p aid args e n nlt attrs Hl;
    unfold et_size; rewrite (normalize_asp_keep G p aid args e _ _ Hl) by discriminate;
    cbn [et_size_canon]; rewrite Hl; reflexivity).
Qed.

Lemma et_size_asp_wrap : forall G p aid args e n nlt attrs,
  (asp_types G) ![ aid ] = Some (ev_arrow (WRAP (exist _ n nlt)) attrs) ->
  et_size G (asp_evt p (asp_paramsC aid args) e) = res n.
Proof.
  ltac1:(intros G p aid args e n nlt attrs Hl;
    unfold et_size; rewrite (normalize_asp_keep G p aid args e _ _ Hl) by discriminate;
    cbn [et_size_canon]; rewrite Hl; reflexivity).
Qed.

Lemma et_size_split : forall G e1 e2,
  et_size G (split_evt e1 e2)
    = (s1 <- et_size G e1 ;; s2 <- et_size G e2 ;; res (s1 + s2)).
Proof.
  ltac1:(intros G e1 e2; unfold et_size; simp normalize_ev;
    cbn [et_size_canon]; reflexivity).
Qed.

Close Scope string_scope.

(** A "well-formed" [Evidence] value: its raw byte length matches the size its
    type prescribes. *)
Inductive wf_Evidence : GlobalContext -> Evidence -> Prop :=
| wf_Evidence_c : forall (ls : RawEv) et G n,
    List.length ls = n ->
    et_size G et = res n ->
    wf_Evidence G (evc ls et).
