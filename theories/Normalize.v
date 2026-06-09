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
