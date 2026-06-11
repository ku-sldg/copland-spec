(** Basic definitions for Copland Terms, Core Terms, 
   EvidenceT, Remote Request/Response structures, Copland events (Ev). *)

(*
   These definitions have been adapted from an earlier version, archived 
   here:  https://ku-sldg.github.io/copland/resources/coplandcoq.tar.gz
*)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)
From CoplandSpec Require Export Term_Defs_Core Term_Defs_Core_Typeclasses Built_In_Params Normalize.
From Equations Require Import Equations.
From RocqCandy Require Import All.
Import ResultNotation.

Definition equiv_EvidenceT `{DecEq ASP_ID, DecEq nat} (G : GlobalContext) (e1 e2 : EvidenceT) : bool :=
  n1 <- et_size G e1 ;;
  n2 <- et_size G e2 ;;
  (if dec_eq n1 n2 then res true else res false) <?> false.

(** Helper function for EvidenceT type reference semantics *)

Definition appr_procedure' `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) 
    : EvidenceT -> EvidenceT -> Result EvidenceT string :=
  fix F (e ev_out : EvidenceT) : Result EvidenceT string :=
  (* The defensive [equiv_EvidenceT] size guard has been removed: the relational
     [tc_appr_*] rules carry no such check, and for well-typed inputs the guard
     always passes (so [appr_procedure] is unchanged on them). Removing it keeps
     the executable appraisal faithful to [tc_appr_*]. *)
  match e with
  (* Simple case, we do nothing on appraise of mt. We return [ev_out] (not the
     literal [mt_evt]) so this case threads its accumulator consistently with
     every other case; this keeps [appr_procedure] in exact agreement with the
     relational [tc_appr_mt] rule (whose output is the input evidence) even when
     [ev_out] is a projection that merely normalizes to [mt_evt]. *)
  | mt_evt => res ev_out
  (* Simple as well, we utilize primitive nonce checking procedure *)
  | nonce_evt n => res (asp_evt p check_nonce_params ev_out)
  (* In this case, it is a bit more complex.
    Basically we have 3 main "types" of ASPs:
    - "REPLACE": In the case of a replace, we can only use the asp's dual
      to convert the evidence to a new `appraised` type, but no recursion
      can be done, as the underlying evidence was replaced.
    - "WRAP": In the case of a wrap, we can uses the asp's dual to 
      essentially `invert` the asp's action. 
      This allows us to then recurse afterwards on the `wrapped` evidence
    - "EXTEND": In the case of an extend, we can use the asp's dual to 
      convert the evidence to a new `appraised` type, and then afterwards
      recurse on the underlying evidence that was not part of the extension.
  *)
  | asp_evt asp_top_plc ps e' => 
    let '(asp_paramsC asp_id args) := ps in
    match (asp_types G) ![ asp_id ] with
    | None => err err_str_asp_no_type_sig
    | Some (ev_arrow fwd attrs) =>
      match (asp_comps G) ![ asp_id ] with
      | None => err err_str_asp_no_compat_appr_asp
      | Some appr_id =>
        let dual_par := asp_paramsC appr_id args in
        match fwd with
        | REPLACE _ => (* just apply the dual once *)
          res (asp_evt p dual_par ev_out)
        | WRAP _ => 
          (* apply the dual to get a new evidence to operate on, then recurse *)
          match (asp_types G) ![ appr_id ] with
          | None => err err_str_asp_no_type_sig
          | Some (ev_arrow UNWRAP attrs) =>
            let ev_out' := asp_evt p dual_par ev_out in
            F e' ev_out'
          | _ => err err_str_appr_compute_evt_neq
          end
          (* let ev_out' := asp_evt p dual_par ev_out in
          F e' ev_out' *)
        | UNWRAP =>
          (* The recursion is over the *canonical* evidence form, where every
             matched WRAP/UNWRAP pair has been cancelled by [normalize_ev]; a
             surviving UNWRAP head is a stuck unwrap with nothing to appraise. *)
          err err_str_asp_at_bottom_not_wrap

        | EXTEND _ _ =>
          (* appraisal of an extend involves doing the appraisal of the extension
          and then separately the appraisal of the underlying *)
          ev_under <- F e' e' ;;
          res (split_evt (asp_evt p dual_par ev_out) ev_under)
        end
      end
    end
  (* As for UNWRAP: [normalize_ev] resolves projections of splits, so canonical
     [left_evt]/[right_evt] are stuck projections with no evidence below. *)
  | left_evt _ => err err_str_no_evidence_below
  | right_evt _ => err err_str_no_evidence_below

  | split_evt e1 e2 =>
    (* we now e ~ ev_out here, so we can continue on it *)
    e1' <- F e1 (left_evt ev_out) ;;
    e2' <- F e2 (right_evt ev_out) ;;
    res (split_evt e1' e2')
  end.

(** Appraise [e] by recursing over its canonical form [normalize_ev G e]
    (so the structural recursion stays canonical and mirrors the relational
    [tc_appr_*] rules exactly), while threading the *raw* [e] as the output
    accumulator (so outputs are built from the raw input, as the rules do). *)
Definition appr_procedure `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) (e : EvidenceT)
    : Result EvidenceT string :=
  appr_procedure' G p (normalize_ev G e) e.

Module Testing.

  Definition enc'_aspid : ASP_ID := "enc'_aspid"%string.

  Example appr_procedure_ex1 : forall G p,
    appr_procedure G p (nonce_evt 1) = res (asp_evt p check_nonce_params (nonce_evt 1)).
  Proof.
    ff.
  Qed.

  Example appr_procedure_ex2 : forall G p attrs,
    lookup enc_aspid (asp_types G) = Some (ev_arrow (WRAP (exist _ 1 Nat.lt_0_1)) attrs) ->
    lookup enc_aspid (asp_comps G) = Some enc'_aspid ->
    lookup enc'_aspid (asp_types G) = Some (ev_arrow UNWRAP attrs) ->
    appr_procedure G p (asp_evt p (enc_params p) (nonce_evt 1)) = 
    res (
      asp_evt p check_nonce_params (
      asp_evt p (asp_paramsC enc'_aspid (enc_aspargs p))
        (asp_evt p (enc_params p) (nonce_evt 1)))
    ).
  Proof.
    intros G p attrs H1 H2 H3.
    unfold appr_procedure.
    assert (normalize_ev G (asp_evt p (enc_params p) (nonce_evt 1))
            = asp_evt p (enc_params p) (nonce_evt 1)) as Hn.
    { unfold enc_params; ltac1:(simp normalize_ev); reflexivity. }
    rewrite Hn; ff with a, r, u, l; unfold equiv_EvidenceT in *; ff.
  Qed.

  Example appr_procedure_ex3 : forall G p,
    appr_procedure G p (split_evt (nonce_evt 1) (nonce_evt 2)) =
    res (
      split_evt 
        (asp_evt p check_nonce_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
        (asp_evt p check_nonce_params (right_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
    ).
  Proof.
    unfold appr_procedure; ltac1:(simp normalize_ev); reflexivity.
  Qed.

  Example appr_procedure_ex4 : forall G p attrs,
    lookup enc_aspid (asp_types G) = Some (ev_arrow (WRAP (exist _ 1 Nat.lt_0_1)) attrs) ->
    lookup enc_aspid (asp_comps G) = Some enc'_aspid ->
    lookup enc'_aspid (asp_types G) = Some (ev_arrow UNWRAP attrs) ->
    appr_procedure G p (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2))) = res (split_evt 
      (asp_evt p check_nonce_params 
        (left_evt 
          (asp_evt p (asp_paramsC enc'_aspid (enc_aspargs p)) 
            (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2)))
          )
        )
      )
      (asp_evt p check_nonce_params 
        (right_evt 
          (asp_evt p (asp_paramsC enc'_aspid (enc_aspargs p)) 
            (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2)))
          )
        )
      )
    ).
  Proof.
    intros G p attrs H1 H2 H3.
    unfold appr_procedure.
    assert (normalize_ev G (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2)))
            = asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2))) as Hn.
    { unfold enc_params; ltac1:(simp normalize_ev); reflexivity. }
    rewrite Hn; unfold equiv_EvidenceT in *; ff; unfold equiv_EvidenceT in *; ff.
  Qed.
End Testing.

(** Helper function for EvidenceT type reference semantics *)
Definition eval_asp `{DecEq ASP_ID} (G : GlobalContext) (a : ASP) 
    (p : Plc) (e : EvidenceT) : Result EvidenceT string :=
  match a with
  | NULL => res mt_evt
  | ASPC params =>
    let '(asp_paramsC asp_id args) := params in
    res (asp_evt p params e)
  | APPR => appr_procedure G p e
  | SIG => res (asp_evt p sig_params e)
  | HSH => res (asp_evt p hsh_params e)
  | ENC q => res (asp_evt p (enc_params q) e)
  end.

(** EvidenceT Type denotational reference semantics.
    The EvidenceT associated with a term, a place, and some initial EvidenceT. *)

Definition proc_ev_path_left (ep : ev_path) (e : EvidenceT) : EvidenceT :=
  match ep with
  | left_path => e
  | right_path => mt_evt
  | both_paths => e
  end.

Definition proc_ev_path_right (ep : ev_path) (e : EvidenceT) : EvidenceT :=
  match ep with
  | left_path => mt_evt
  | right_path => e
  | both_paths => e
  end.

Fixpoint eval `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term) 
    : Result EvidenceT string :=
  match t with
  | asp a => eval_asp G a p e
  | att q t1 => eval G q e t1
  | lseq t1 t2 => 
      e1 <- eval G p e t1 ;;
      eval G p e1 t2
  | bseq ep t1 t2 => 
    e1 <- eval G p (proc_ev_path_left ep e) t1 ;;
    e2 <- eval G p (proc_ev_path_right ep e) t2 ;;
    res (split_evt e1 e2)
  | bpar ep t1 t2 => 
    e1 <- eval G p (proc_ev_path_left ep e) t1 ;;
    e2 <- eval G p (proc_ev_path_right ep e) t2 ;;
    res (split_evt e1 e2)
  end.

(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  [req] and [rpy] 
    are communication events.  [cvm_thread_start] and [cvm_thread_end] are 
    parallel thread synchonization events, unique to CVM execution (not in 
    the reference semantics).  Each event is distinguished using a unique 
    natural number.
 *)

Inductive Ev :=
| null: nat -> Plc -> Ev
(* | copy:  nat -> Plc -> Ev  *)
| umeas: nat -> Plc -> ASP_PARAMS -> EvidenceT -> Ev
| req: nat -> Plc -> Plc -> EvidenceT -> Term -> Ev
| rpy: nat -> Plc -> Plc -> EvidenceT -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev
| cvm_thread_start: nat -> Loc -> Plc -> EvidenceT -> Term -> Ev
| cvm_thread_end: nat -> Loc -> Ev.

(** The natural number used to distinguish events. *)

Definition appr_events_size `{DecEq ASP_ID} (G : GlobalContext) 
    : EvidenceT -> Result nat string :=
  fix F e : Result nat string :=
  match e with
  | mt_evt => res 0
  | nonce_evt _ => res 1 (* [umeas check_nonce nonce] *)
  | asp_evt p par e' => 
    let '(asp_paramsC asp_id args) := par in
    match ((asp_types G) ![ asp_id ]) with
    | None => err err_str_asp_no_type_sig
    | Some (ev_arrow asp_fwd attrs) =>
      match asp_fwd with
      | REPLACE _ => res 1 (* Single dual appr asp for 1 *)
      | WRAP _ => 
        (* we need the size of recursing *)
        n <- F e' ;;
        res (1 + n) (* 1 for the unwrap, then n for rec case *)
      | UNWRAP =>
        (* stuck unwrap: cannot arise canonically (cf. [appr_procedure']) *)
        err err_str_asp_at_bottom_not_wrap
      | EXTEND _ _ =>
        (* we need the size of recursing *)
        n <- F e' ;;
        res (3 + n) (* split (1), extend dual (1), rec case (n), join (1) *)
      end
    end
  (* stuck projections: cannot arise canonically (cf. [appr_procedure']) *)
  | left_evt _ => err err_str_no_evidence_below
  | right_evt _ => err err_str_no_evidence_below

  | split_evt e1 e2 =>
    s1 <- F e1 ;;
    s2 <- F e2 ;;
    res (2 + s1 + s2) (* split (1) + s1 Result s2 evs Result join evs (1) *)
  end.

(* EvidenceT Type size *)
Fixpoint events_size `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term)
    : Result nat string :=
  match t with
  | asp a => 
    match a with
    | APPR => appr_events_size G (normalize_ev G e) (* # events over the canonical (appraised) ev type *)
    | _ => res 1 (* all other ASPs do 1 event for meas *)
    end
  | att p' t1 => 
    e' <- events_size G p' e t1 ;; (* remotely e' events are done *)
    res (2 + e') (* +1 for req, +e' for rem evs, +1 for rpy *)

  | lseq t1 t2 => 
    e1 <- events_size G p e t1 ;; (* first e1 events are done *)
    e' <- eval G p e t1 ;; (* we need a new evidence type for next step *)
    e2 <- events_size G p e' t2 ;; (* next e2 events are done *)
    res (e1 + e2) (* +e1 for first evs, +e2 for second evs *)
  
  | bseq ep t1 t2 => 
    (* +1 for split, +e1 for left evs, +e2 for right evs, +1 for join *)
    e1 <- events_size G p (proc_ev_path_left ep e) t1 ;; (* first e1 events are done *)
    e2 <- events_size G p (proc_ev_path_right ep e) t2 ;; (* next e2 events are done *)
    res (2 + e1 + e2) 
  | bpar ep t1 t2 => 
    (* + 1 for split, +1 for thread_start; +e1,+e2 for sides, +1 for thread_join, + 1 for join *)
    e1 <- events_size G p (proc_ev_path_left ep e) t1 ;; (* first e1 events are done *)
    e2 <- events_size G p (proc_ev_path_right ep e) t2 ;;
    res (4 + e1 + e2)
  end.


Definition ev x : nat :=
  match x with
  | null i _ => i
  | umeas i _ _ _ => i
  | req i _ _ _ _ => i
  | rpy i _ _ _ => i 
  | split i _ => i
  | join i _ => i
  | cvm_thread_start i _ _ _ _ => i
  | cvm_thread_end i _ => i
  end.

Definition appr_events' `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) 
    : EvidenceT -> EvidenceT -> nat -> Result (list Ev) string :=
  fix F (e ev_out : EvidenceT) (i : nat) : Result (list Ev) string :=
  match e with
  | mt_evt => res []
  | nonce_evt n => res [umeas i p check_nonce_params ev_out]
  (* (nonce_evt n)] *)
  | asp_evt p' ps e' => 
    let '(asp_paramsC asp_id args) := ps in
    match ((asp_comps G) ![ asp_id ]) with
    | None => err err_str_asp_no_compat_appr_asp
    | Some appr_id => 
      let dual_par := asp_paramsC appr_id args in
      match ((asp_types G) ![ asp_id ]) with
      | None => err err_str_asp_no_type_sig
      | Some (ev_arrow fwd attrs) =>
        match fwd with
        | REPLACE _ => (* single dual for replace *)
          res ([umeas i p dual_par ev_out])

        | WRAP _ => (* do the unwrap *)
          let unwrap_ev := umeas i p dual_par ev_out in
          let new_ev_out := asp_evt p dual_par ev_out in
          (* do recursive case *)
          ev' <- F e' new_ev_out (i + 1) ;;
          res (unwrap_ev :: ev')

        | UNWRAP => (* stuck unwrap: cannot arise canonically (cf. [appr_procedure']) *)
          err err_str_asp_at_bottom_not_wrap

        | EXTEND _ _ => (* do the extend dual *)
          (* ev_out does not change for the umeas event,
          but it is replaced by e' for the recursive call
          as the extend does not effect the underlying evidence! *)
          ev' <- F e' e' (i + 2) ;;
          res ([split i p] ++ 
            [umeas (i + 1) p dual_par ev_out] ++ 
            ev' ++ [join (i + 2 + List.length ev') p])
        end
      end
    end

  (* stuck projections: cannot arise canonically (cf. [appr_procedure']) *)
  | left_evt _ => err err_str_no_evidence_below
  | right_evt _ => err err_str_no_evidence_below

  | split_evt e1 e2 =>
    if (equiv_EvidenceT G e1 (left_evt ev_out))
    then if (equiv_EvidenceT G e2 (right_evt ev_out))
    then
      e1' <- F e1 (left_evt ev_out) (1 + i) ;;
      let next_i := (i + 1) + (List.length e1') in
      e2' <- F e2 (right_evt ev_out) next_i ;;
      let last_i := next_i + (List.length e2') in
      res ([split i p] ++ e1' ++ e2' ++ [join last_i p])
    else err err_str_appr_compute_evt_neq
    else err err_str_appr_compute_evt_neq
  end.

Lemma appr_events'_size_works : forall G p e ev_out i evs,
  appr_events' G p e ev_out i = res evs ->
  appr_events_size G e = res (List.length evs).
Proof.
  intros G p e.
  induction e as [ | n | p' par e' IH | e' IH | e' IH | e1 IH1 e2 IH2 ];
  intros ev_out i evs Hev; simpl in Hev; simpl.
  - (* mt: no events *)
    inversion Hev; subst.
    reflexivity.
  - (* nonce: one check-nonce event *)
    inversion Hev; subst.
    reflexivity.
  - (* asp *)
    destruct par as [aid args].
    destruct ((asp_comps G) ![ aid ]) as [dual | ] eqn:Hdual > [ | inversion Hev ].
    destruct ((asp_types G) ![ aid ]) as [ [fwd attrs] | ] eqn:Hlk > [ | inversion Hev ].
    destruct fwd as [ [n nlt] | [n nlt] | | [n nlt] isig ].
    + (* REPLACE: single dual event *)
      inversion Hev; subst.
      reflexivity.
    + (* WRAP: unwrap event, then the recursion *)
      destruct (appr_events' G p e' (asp_evt p (asp_paramsC dual args) ev_out) (i + 1))
        as [ev' | ] eqn:Hrec > [ | inversion Hev ].
      eapply IH in Hrec.
      inversion Hev; subst.
      rewrite Hrec.
      reflexivity.
    + (* UNWRAP: stuck, no events *)
      inversion Hev.
    + (* EXTEND: split, dual, recursion, join *)
      destruct (appr_events' G p e' e' (i + 2)) as [ev' | ] eqn:Hrec > [ | inversion Hev ].
      eapply IH in Hrec.
      inversion Hev; subst.
      rewrite Hrec.
      cbv beta iota delta [bind].
      simpl.
      f_equal.
      repeat (rewrite length_app).
      simpl.
      lia.
  - (* left_evt: stuck projection *)
    inversion Hev.
  - (* right_evt: stuck projection *)
    inversion Hev.
  - (* split: events of both sides, bracketed by split/join *)
    destruct (equiv_EvidenceT G e1 (left_evt ev_out)) eqn:Hq1 > [ | inversion Hev ].
    destruct (equiv_EvidenceT G e2 (right_evt ev_out)) eqn:Hq2 > [ | inversion Hev ].
    (destruct (appr_events' G p e1 (left_evt ev_out) (S i)) as [evs1 | ] eqn:H1;
     cbv beta iota delta [bind] in Hev) > [ | inversion Hev ].
    (destruct (appr_events' G p e2 (right_evt ev_out) (i + 1 + Datatypes.length evs1))
      as [evs2 | ] eqn:H2;
     cbv beta iota delta [bind] in Hev) > [ | inversion Hev ].
    eapply IH1 in H1.
    eapply IH2 in H2.
    inversion Hev; subst.
    rewrite H1.
    rewrite H2.
    cbv beta iota delta [bind].
    simpl.
    f_equal.
    repeat (rewrite length_app).
    simpl.
    lia.
Qed.

(* Appraise over the canonical (normalized) evidence structure, threading the
   raw [e] as the output accumulator -- mirrors [appr_procedure]. *)
Definition appr_events `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) (e : EvidenceT) (i : nat)
    : Result (list Ev) string :=
  appr_events' G p (normalize_ev G e) e i.

Lemma appr_events_size_works : forall G p e i evs,
  appr_events G p e i = res evs ->
  appr_events_size G (normalize_ev G e) = res (List.length evs).
Proof.
  intros G p e i evs H.
  unfold appr_events in H.
  eapply appr_events'_size_works.
  exact H.
Qed.

Definition asp_events `{DecEq ASP_ID} (G : GlobalContext) (p : Plc) (e : EvidenceT) 
    (a : ASP) (i : nat) : Result (list Ev) string :=
  match a with
  | NULL => res ([null i p])
  | ASPC ps => res ([umeas i p ps e])
  | APPR => appr_events G p e i
  | SIG => res ([umeas i p sig_params e])
  | HSH => res ([umeas i p hsh_params e])
  | ENC q => res ([umeas i p (enc_params q) e])
  end.

Lemma asp_appr_events_size_works : forall G p e i evs,
  asp_events G p e APPR i = res evs ->
  appr_events_size G (normalize_ev G e) = res (List.length evs).
Proof.
  unfold asp_events.
  eapply appr_events_size_works.
Qed.

Lemma asp_events_size_works : forall G p a e i evs,
  asp_events G p e a i = res evs ->
  events_size G p e (asp a) = res (List.length evs).
Proof.
  induction a; intros; simpl in *; 
  try (eapply asp_appr_events_size_works); eauto;
  simpl in *; intuition; destruct e; simpl in *;
  repeat find_injection; ff.
Qed.

Fixpoint true_last {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | h' :: t' => 
    match true_last t' with
    | None => Some h'
    | Some x => Some x
    end
  end.

Lemma true_last_none_iff_nil : forall A (l : list A),
  true_last l = None <-> l = nil.
Proof.
  induction l; ff.
Qed.

Lemma true_last_app : forall A (l1 l2 : list A),
  l2 <> nil ->
  true_last (l1 ++ l2) = true_last l2.
Proof.
  induction l1; ff;
  find_higher_order_rewrite; ff;
  find_eapply_lem_hyp true_last_none_iff_nil; ff.
Qed.

Lemma true_last_app_spec : forall A (l1 l2 : list A) x,
  true_last (l1 ++ l2) = Some x ->
  (true_last l1 = Some x /\ l2 = nil) \/ true_last l2 = Some x.
Proof.
  induction l1; ff with a, r;
  find_eapply_lem_hyp true_last_none_iff_nil; 
  find_eapply_lem_hyp app_eq_nil; ff.
Qed.

Lemma true_last_app_singleton : forall A (l : list A) x,
  true_last (l ++ [x]) = Some x.
Proof.
  intros A l x.
  rewrite true_last_app.
  - reflexivity.
  - intros Hc; inversion Hc.
Qed.

Lemma appr_events'_deterministic_index : forall G p e ev_out i evs,
  appr_events' G p e ev_out i = res evs ->
  forall v',
    true_last evs = Some v' ->
    ev v' = i + List.length evs - 1.
Proof.
  intros G p e.
  induction e as [ | n | p' par e' IH | e' IH | e' IH | e1 IH1 e2 IH2 ];
  intros ev_out i evs Hev v' Hlast; simpl in Hev.
  - (* mt: no events, so no last event *)
    inversion Hev; subst.
    inversion Hlast.
  - (* nonce: the single check-nonce event *)
    inversion Hev; subst.
    inversion Hlast; subst.
    simpl.
    lia.
  - (* asp *)
    destruct par as [aid args].
    destruct ((asp_comps G) ![ aid ]) as [dual | ] eqn:Hdual > [ | inversion Hev ].
    destruct ((asp_types G) ![ aid ]) as [ [fwd attrs] | ] eqn:Hlk > [ | inversion Hev ].
    destruct fwd as [ [n nlt] | [n nlt] | | [n nlt] isig ].
    + (* REPLACE: the single dual event *)
      inversion Hev; subst.
      inversion Hlast; subst.
      simpl.
      lia.
    + (* WRAP: unwrap event followed by the recursion's events *)
      destruct (appr_events' G p e' (asp_evt p (asp_paramsC dual args) ev_out) (i + 1))
        as [ev'' | ] eqn:Hrec > [ | inversion Hev ].
      inversion Hev; subst.
      simpl in Hlast.
      destruct (true_last ev'') as [x | ] eqn:Htl.
      * (* the recursion is nonempty: its last event is the last overall *)
        inversion Hlast; subst.
        pose proof (IH _ _ _ Hrec v' Htl) as Hidx.
        simpl.
        lia.
      * (* the recursion is empty: the unwrap event is last *)
        eapply true_last_none_iff_nil in Htl; subst.
        inversion Hlast; subst.
        simpl.
        lia.
    + (* UNWRAP: stuck *)
      inversion Hev.
    + (* EXTEND: the closing join event is last, and carries its own index *)
      destruct (appr_events' G p e' e' (i + 2)) as [ev'' | ] eqn:Hrec > [ | inversion Hev ].
      inversion Hev; subst.
      simpl in Hlast.
      rewrite true_last_app_singleton in Hlast.
      simpl in Hlast.
      inversion Hlast; subst.
      simpl.
      repeat (rewrite length_app).
      simpl.
      lia.
  - (* left_evt: stuck projection *)
    inversion Hev.
  - (* right_evt: stuck projection *)
    inversion Hev.
  - (* split: the closing join event is last, and carries its own index *)
    destruct (equiv_EvidenceT G e1 (left_evt ev_out)) eqn:Hq1 > [ | inversion Hev ].
    destruct (equiv_EvidenceT G e2 (right_evt ev_out)) eqn:Hq2 > [ | inversion Hev ].
    (destruct (appr_events' G p e1 (left_evt ev_out) (S i)) as [evs1 | ] eqn:H1;
     cbv beta iota delta [bind] in Hev) > [ | inversion Hev ].
    (destruct (appr_events' G p e2 (right_evt ev_out) (i + 1 + Datatypes.length evs1))
      as [evs2 | ] eqn:H2;
     cbv beta iota delta [bind] in Hev) > [ | inversion Hev ].
    inversion Hev; subst.
    repeat (rewrite app_assoc in Hlast).
    simpl in Hlast.
    rewrite true_last_app_singleton in Hlast.
    simpl in Hlast.
    inversion Hlast; subst.
    simpl.
    repeat (rewrite length_app).
    simpl.
    lia.
Qed.

Theorem asp_events_deterministic_index : forall G p a e i evs,
  asp_events G p e a i = res evs ->
  forall v',
    true_last evs = Some v' ->
    ev v' = i + List.length evs - 1.
Proof.
  induction a; ff with l, (eapply appr_events'_deterministic_index).
Qed.
