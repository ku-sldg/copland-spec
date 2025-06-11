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
From CoplandSpec Require Export Term_Defs_Core Term_Defs_Core_Typeclasses Built_In_Params.
From RocqCandy Require Import All.
Import ResultNotation.

Definition splitEv_T_l (sp:Split) (e:EvidenceT) : EvidenceT :=
  match sp with
  | (ALL,_) => e
  |  _ => mt_evt
  end.

Definition splitEv_T_r (sp:Split) (e:EvidenceT) : EvidenceT :=
  match sp with
  | (_,ALL) => e
  |  _ => mt_evt
  end.

Definition splitEv_l (sp:Split) (e:Evidence): Evidence :=
  match sp with
  | (ALL, _) => e
  | _ => mt_evc
  end.

Definition splitEv_r (sp:Split) (e:Evidence): Evidence :=
  match sp with
  | (_,ALL) => e
  | _ => mt_evc
  end.

Definition sp_ev (sp:SP) (e:EvidenceT) : EvidenceT :=
  match sp with
  | ALL => e
  | NONE => mt_evt
  end.

Definition equiv_EvidenceT (G : GlobalContext) (e1 e2 : EvidenceT) : bool :=
  n1 <- et_size G e1 ;;
  n2 <- et_size G e2 ;;
  (if dec_eq n1 n2 then res true else res false) <?> false.

(** Helper function for EvidenceT type reference semantics *)

Definition appr_procedure' (G : GlobalContext) (p : Plc) 
    : EvidenceT -> EvidenceT -> Result EvidenceT string :=
  fix F (e ev_out : EvidenceT) : Result EvidenceT string :=
  if (equiv_EvidenceT G e ev_out)
  then (match e with
  (* Simple case, we do nothing on appraise of mt *)
  | mt_evt => res mt_evt
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
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    match lookup asp_id (asp_types G) with
    | None => err err_str_asp_no_type_sig
    | Some (ev_arrow fwd in_sig out_sig) =>
      match lookup asp_id (asp_comps G) with
      | None => err err_str_asp_no_compat_appr_asp
      | Some appr_id =>
        let dual_par := asp_paramsC appr_id args targ_plc targ in
        match fwd with
        | REPLACE => (* just apply the dual once *)
          res (asp_evt p dual_par ev_out)
        | WRAP => 
          (* apply the dual to get a new evidence to operate on, then recurse *)
          match lookup appr_id (asp_types G) with
          | None => err err_str_asp_no_type_sig
          | Some (ev_arrow UNWRAP in_sig' out_sig') =>
            let ev_out' := asp_evt p dual_par ev_out in
            F e' ev_out'
          | _ => err err_str_appr_compute_evt_neq
          end
          (* let ev_out' := asp_evt p dual_par ev_out in
          F e' ev_out' *)
        | UNWRAP => 
          (* The appraisal of something that is unwrapped is just whatever is below its wrap *)
          (* NOTE: In practice this should nearly never happen as the appraisal procedure itself should be doing the UNWRAP and subsequent functions *)
          r <- apply_to_evidence_below G (fun e => F e ev_out) [Trail_UNWRAP asp_id] e' ;;
          r
          (* match e' with
          | asp_evt _ (asp_paramsC asp_id' args' targ_plc' targ') e'' => 
            match (lookup asp_id' (asp_types G)) with
            | None => errC err_str_asp_no_type_sig
            | Some (ev_arrow WRAP in_sig' out_sig') =>
              (* We are a well-typed (UNWRAP (WRAP e'')), so continue *)
              F e'' ev_out
            | _ => errC err_str_appr_not_originally_a_wrap
            end
          | _ => errC err_str_appr_only_allow_on_asp
          end *)

        | EXTEND => 
          (* appraisal of an extend involves doing the appraisal of the extension
          and then separately the appraisal of the underlying *)
          ev_under <- F e' e' ;;
          res (split_evt (asp_evt p dual_par ev_out) ev_under)
        end
      end
    end
  | left_evt e' => 
    r <- apply_to_evidence_below G (fun e' => F e' ev_out) [Trail_LEFT] e' ;; r
  | right_evt e' => 
    r <- apply_to_evidence_below G (fun e' => F e' ev_out) [Trail_RIGHT] e' ;; r

  | split_evt e1 e2 => 
    (* we now e ~ ev_out here, so we can continue on it *)
    e1' <- F e1 (left_evt ev_out) ;;
    e2' <- F e2 (right_evt ev_out) ;;
    res (split_evt e1' e2')
  end)
  else err err_str_appr_compute_evt_neq.

Definition appr_procedure (G : GlobalContext) (p : Plc) (e : EvidenceT) 
    : Result EvidenceT string :=
  appr_procedure' G p e e.

Module Testing.

  Definition enc'_aspid : ASP_ID := "enc'_aspid"%string.

  Example appr_procedure_ex1 : forall G p,
    appr_procedure G p (nonce_evt 1) = res (asp_evt p check_nonce_params (nonce_evt 1)).
  Proof.
    ff.
  Qed.

  Example appr_procedure_ex2 : forall G p,
    lookup enc_aspid (asp_types G) = Some (ev_arrow WRAP InAll (OutN 1)) ->
    lookup enc_aspid (asp_comps G) = Some enc'_aspid ->
    lookup enc'_aspid (asp_types G) = Some (ev_arrow UNWRAP InAll (OutUnwrap)) ->
    appr_procedure G p (asp_evt p (enc_params p) (nonce_evt 1)) = 
    res (
      asp_evt p check_nonce_params (
      asp_evt p (asp_paramsC enc'_aspid enc_aspargs p enc_targid)
        (asp_evt p (enc_params p) (nonce_evt 1)))
    ).
  Proof.
    unfold appr_procedure.
    ff a, r, u, l; unfold equiv_EvidenceT in *; ff.
  Qed.

  Example appr_procedure_ex3 : forall G p,
    appr_procedure G p (split_evt (nonce_evt 1) (nonce_evt 2)) =
    res (
      split_evt 
        (asp_evt p check_nonce_params (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
        (asp_evt p check_nonce_params (right_evt (split_evt (nonce_evt 1) (nonce_evt 2))))
    ).
  Proof.
    reflexivity.
  Qed.

  Example appr_procedure_ex4 : forall G p,
    lookup enc_aspid (asp_types G) = Some (ev_arrow WRAP InAll (OutN 1)) ->
    lookup enc_aspid (asp_comps G) = Some enc'_aspid ->
    lookup enc'_aspid (asp_types G) = Some (ev_arrow UNWRAP InAll (OutUnwrap)) ->
    appr_procedure G p (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2))) = res (split_evt 
      (asp_evt p check_nonce_params 
        (left_evt 
          (asp_evt p (asp_paramsC enc'_aspid enc_aspargs p enc_targid) 
            (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2)))
          )
        )
      )
      (asp_evt p check_nonce_params 
        (right_evt 
          (asp_evt p (asp_paramsC enc'_aspid enc_aspargs p enc_targid) 
            (asp_evt p (enc_params p) (split_evt (nonce_evt 1) (nonce_evt 2)))
          )
        )
      )
    ).
  Proof.
    intros;
    unfold appr_procedure, equiv_EvidenceT in *;
    ff; unfold equiv_EvidenceT in *; ff.
  Qed.
End Testing.

(** Helper function for EvidenceT type reference semantics *)
Definition eval_asp (G : GlobalContext) (a : ASP) 
    (p : Plc) (e : EvidenceT) : Result EvidenceT string :=
  match a with
  | NULL => res mt_evt
  | ASPC params =>
    let '(asp_paramsC asp_id args targ_plc targ) := params in
    res (asp_evt p params e)
  | APPR => appr_procedure G p e
  | SIG => res (asp_evt p sig_params e)
  | HSH => res (asp_evt p hsh_params e)
  | ENC q => res (asp_evt p (enc_params q) e)
  end.

(** EvidenceT Type denotational reference semantics.
    The EvidenceT associated with a term, a place, and some initial EvidenceT. *)

Definition asp_comp_map_supports_ev (G : GlobalContext) : EvidenceT -> Prop  :=
  fix F (e : EvidenceT) : Prop :=
  match e with
  | mt_evt => True
  | nonce_evt n => True
  | asp_evt asp_top_plc ps e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    lookup asp_id (asp_comps G) <> None /\
    (match (lookup asp_id (asp_types G)) with
    | None => False
    | Some (ev_arrow fwd in_sig out_sig) =>
      match fwd with
      | REPLACE => True
      | WRAP => F e'
      | UNWRAP => F e'
      | EXTEND => F e'
      end
    end)
  | left_evt e' => 
    apply_to_evidence_below G F [Trail_LEFT] e' <?> False
  | right_evt e' => 
    apply_to_evidence_below G F [Trail_RIGHT] e' <?> False
  | split_evt e1 e2 => 
      F e1 /\ F e2
  end.

(* 
Theorem asp_comp_map_supports_ev_iff_appr_procedure: 
  forall e eo p G,
  asp_comp_map_supports_ev G e <->
  exists e', appr_procedure' G p e eo = resultC e'.
Proof.
  induction e; simpl in *; intros; try (intuition; eauto; ffa; fail);
  ff; intuition; try congruence; break_exists; try congruence;
  result_monad_unfold; ff;
  try erewrite IHe1 in *;
  try erewrite IHe2 in *;
  break_exists; repeat find_rewrite; try congruence;
  try (eexists; repeat find_rewrite; eauto; fail);
  try (find_higher_order_rewrite; ff; fail).
  * eapply IHe; ff.
  * erewrite IHe in H0; ff. 
  * erewrite IHe; ff.
  * erewrite IHe; ff. 
  * 
    match goal with
    | H: appr_procedure ?g ?p ?e ?e0 = 
      IH : context[exists _ : _, appr_procedure _ _ ?e _ = _] |- _ => 
      assert (exists )
    end.
  * admit. 
  * admit. 
  Unshelve. all: eauto.
Qed.
*)

Fixpoint eval (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term) 
    : Result EvidenceT string :=
  match t with
  | asp a => eval_asp G a p e
  | att q t1 => eval G q e t1
  | lseq t1 t2 => 
      e1 <- eval G p e t1 ;;
      eval G p e1 t2
  | bseq s t1 t2 => 
      e1 <- eval G p (splitEv_T_l s e) t1 ;; 
      e2 <- eval G p (splitEv_T_r s e) t2 ;;
      res (split_evt e1 e2)
  | bpar s t1 t2 => 
      e1 <- eval G p (splitEv_T_l s e) t1 ;; 
      e2 <- eval G p (splitEv_T_r s e) t2 ;;
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

Definition appr_events_size (G : GlobalContext) : EvidenceT -> Result nat string :=
  fix F e : Result nat string :=
  match e with
  | mt_evt => res 0
  | nonce_evt _ => res 1 (* [umeas check_nonce nonce] *)
  | asp_evt p par e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (lookup asp_id (asp_types G)) with
    | None => err err_str_asp_no_type_sig
    | Some (ev_arrow asp_fwd in_sig out_sig) =>
      match asp_fwd with
      | REPLACE => res 1 (* Single dual appr asp for 1 *)
      | WRAP => 
        (* we need the size of recursing *)
        n <- F e' ;;
        res (1 + n) (* 1 for the unwrap, then n for rec case *)
      | UNWRAP => 
        (* we are just doing the recursion *)
        r <- apply_to_evidence_below G F [Trail_UNWRAP asp_id] e' ;; 
        r
      | EXTEND => 
        (* we need the size of recursing *)
        n <- F e' ;;
        res (3 + n) (* split (1), extend dual (1), rec case (n), join (1) *)
      end
    end
  | left_evt e' => 
    r <- apply_to_evidence_below G F [Trail_LEFT] e' ;; 
    r

  | right_evt e' => 
    r <- apply_to_evidence_below G F [Trail_RIGHT] e' ;; 
    r

  | split_evt e1 e2 =>
    s1 <- F e1 ;;
    s2 <- F e2 ;;
    res (2 + s1 + s2) (* split (1) + s1 Result s2 evs Result join evs (1) *)
  end.

(* EvidenceT Type size *)
Fixpoint events_size (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term)
    : Result nat string :=
  match t with
  | asp a => 
    match a with
    | APPR => appr_events_size G e (* appraisal does # of events based on ev type *)
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
  
  | bseq s t1 t2 => 
    e1 <- events_size G p (splitEv_T_l s e) t1 ;; (* left does e1 events *)
    e2 <- events_size G p (splitEv_T_r s e) t2 ;; (* right does e2 events *)
    res (2 + e1 + e2) (* +1 for split; +e1,+e2 for sides, +1 for join *)
  | bpar s t1 t2 => 
    e1 <- events_size G p (splitEv_T_l s e) t1 ;; (* left does e1 events *)
    e2 <- events_size G p (splitEv_T_r s e) t2 ;; (* right does e2 events *)
    (* + 1 for split, +1 for thread_start; +e1,+e2 for sides, +1 for thread_join, + 1 for join *)
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

Definition appr_events' (G : GlobalContext) (p : Plc) 
    : EvidenceT -> EvidenceT -> nat -> Result (list Ev) string :=
  fix F (e ev_out : EvidenceT) (i : nat) : Result (list Ev) string :=
  match e with
  | mt_evt => res []
  | nonce_evt n => res [umeas i p check_nonce_params ev_out]
  (* (nonce_evt n)] *)
  | asp_evt p' ps e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    match (lookup asp_id (asp_comps G)) with
    | None => err err_str_asp_no_compat_appr_asp
    | Some appr_id => 
      let dual_par := asp_paramsC appr_id args targ_plc targ in
      match (lookup asp_id (asp_types G)) with
      | None => err err_str_asp_no_type_sig
      | Some (ev_arrow fwd in_sig out_sig) =>
        match fwd with
        | REPLACE => (* single dual for replace *)
          res ([umeas i p dual_par ev_out])

        | WRAP => (* do the unwrap *)
          let unwrap_ev := umeas i p dual_par ev_out in
          let new_ev_out := asp_evt p dual_par ev_out in
          (* do recursive case *)
          ev' <- F e' new_ev_out (i + 1) ;;
          res (unwrap_ev :: ev')

        | UNWRAP => (* we are already unwrapped, just do below stuff *)
          r <- apply_to_evidence_below G (fun e' => F e' ev_out i) [Trail_UNWRAP asp_id] e' ;;
          r

        | EXTEND => (* do the extend dual *)
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

  | left_evt e' => 
    (* we only do stuff on the left, its a pass through *)
    r <- apply_to_evidence_below G (fun e' => F e' ev_out i) [Trail_LEFT] e' ;; r

  | right_evt e' =>
    (* we only do stuff on the right, its a pass through *)
    r <- apply_to_evidence_below G (fun e' => F e' ev_out i) [Trail_RIGHT] e' ;; r

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

Ltac2 esp_same () :=
  match! goal with
  | [ h1 : Evidence_Subterm_path _ _ _ _,
      h2 : Evidence_Subterm_path _ _ _ _ |- _ ] =>
    let h2 := Control.hyp h2 in
    eapply Evidence_Subterm_path_same in $h1 >
    [ | exact $h2 ]; subst
  end.

Ltac2 Notation "ateb_unpack" 
  h(ident) :=
  let h' := Control.hyp h in
  match! Constr.type h' with
  | apply_to_evidence_below _ ?_f _ _ = res _ =>
    let hesp1 := fresh_hyp "Hesp" in
    let hf1 := fresh_hyp "Hf" in
    eapply apply_to_evidence_below_res_spec in $h as [? [$hesp1 $hf1]]
  end.

Ltac2 Notation "ateb_diff" :=
  match! goal with
  | [ h1 : apply_to_evidence_below _ ?_f1 _ _ = res _,
      h2 : apply_to_evidence_below _ ?f2 _ _ = err _ |- _ ] =>
    let h' := fresh_hyp "H" in
    eapply apply_to_evidence_below_res with (fn2 := $f2) in $h1 as $h';
    let h' := Control.hyp h' in
    let h'' := fresh_hyp "H" in
    destruct $h' as [? $h''];
    let h'' := Control.hyp h'' in
    rewrite $h'' in $h2; 
    subst; clear h''; try congruence
  end.

Ltac2 Notation "ateb_errs_same" := 
  match! goal with
  | [ h1 : apply_to_evidence_below _ ?_f1 _ _ = err ?_r1,
      h2 : apply_to_evidence_below _ ?_f2 _ _ = err ?_r2 |- _ ] =>
    let h2 := Control.hyp h2 in
    eapply apply_to_evidence_below_errs_det in $h1 >
    [ | exact $h2 ]; subst
  end.

Ltac2 Notation "ateb_same" :=
  match! goal with
  | [ h1 : apply_to_evidence_below _ ?_f1 _ _ = res ?_r1,
      h2 : apply_to_evidence_below _ ?_f2 _ _ = res ?_r2 |- _ ] =>
    let hesp1 := fresh_hyp "Hesp" in
    let hf1 := fresh_hyp "Hf" in
    eapply apply_to_evidence_below_res_spec in $h1 as [? [$hesp1 $hf1]];
    let hesp2 := fresh_hyp "Hesp" in
    let hf2 := fresh_hyp "Hf" in
    eapply apply_to_evidence_below_res_spec in $h2 as [? [$hesp2 $hf2]];
    let hesp2 := Control.hyp hesp2 in
    eapply Evidence_Subterm_path_same in $hesp1 >
    [ | exact $hesp2]; subst
  end.

Ltac2 Notation "ateb_simp" :=
  try (ateb_same);
  try (ateb_diff);
  try (ateb_errs_same).

Lemma appr_events'_size_works : forall G p e ev_out i evs,
  appr_events' G p e ev_out i = res evs ->
  appr_events_size G e = res (List.length evs).
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G); 
  simpl in *; intros; intuition; ff u, a;
  ateb_simp; ff;
  try (repeat (rewrite length_app in *); simpl in *; f_equal; lia).
Qed.

Definition appr_events (G : GlobalContext) (p : Plc) (e : EvidenceT) (i : nat) 
    : Result (list Ev) string :=
  appr_events' G p e e i.

Definition asp_events (G : GlobalContext) (p : Plc) (e : EvidenceT) 
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
  appr_events_size G e = res (List.length evs).
Proof.
  induction e; ff;
  try (find_eapply_lem_hyp appr_events'_size_works; ff).
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
  induction l1; ff a, r;
  find_eapply_lem_hyp true_last_none_iff_nil; 
  find_eapply_lem_hyp app_eq_nil; ff.
Qed.

Ltac2 Notation "solve_true_last_app" :=
  repeat (find_eapply_lem_hyp true_last_app_spec; try (break_or_hyp > 
    [ ff; find_eapply_lem_hyp app_eq_nil; ff | ff ]));
  repeat (rewrite length_app in *); ff; try lia.

Ltac2 Notation "solve_true_last_none" :=
  find_eapply_lem_hyp true_last_none_iff_nil; 
  repeat (find_eapply_lem_hyp app_eq_nil); ff; try lia.

Lemma appr_events'_deterministic_index : forall G p e ev_out i evs,
  appr_events' G p e ev_out i = res evs ->
  forall v',
    true_last evs = Some v' ->
    ev v' = i + List.length evs - 1.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G); ff u, a, l;
  try (solve_true_last_app);
  try (solve_true_last_none);
  try (ateb_unpack Heqr); ff a, l.
  - find_eapply_lem_hyp IHe; ff l; lia.
  - find_eapply_lem_hyp app_eq_nil; ff.
Qed.

Theorem asp_events_deterministic_index : forall G p a e i evs,
  asp_events G p e a i = res evs ->
  forall v',
    true_last evs = Some v' ->
    ev v' = i + List.length evs - 1.
Proof.
  induction a; ff l;
  eapply appr_events'_deterministic_index; eauto.
Qed.
