From CoplandSpec Require Import Term_Defs_Core Term_Defs_Core_Typeclasses.
From Equations Require Import Equations.

(** EvidenceT equivalence relation *)
Inductive Evidence_Reduce (G : GlobalContext) : EvidenceT -> EvidenceT -> Prop :=
(* | ev_red_mt : Evidence_Reduce G mt_evt mt_evt
| ev_red_nonce : forall n, Evidence_Reduce G (nonce_evt n) (nonce_evt n) *)
| ev_red_left : forall e1 e2,
    Evidence_Reduce G e1 e2 ->
    Evidence_Reduce G (left_evt e1) (left_evt e2)
| ev_red_right : forall e1 e2,
    Evidence_Reduce G e1 e2 ->
    Evidence_Reduce G (right_evt e1) (right_evt e2)
| ev_red_split : forall e1 e2 e1' e2',
    Evidence_Reduce G e1 e1' ->
    Evidence_Reduce G e2 e2' ->
    Evidence_Reduce G (split_evt e1 e2) (split_evt e1' e2')
| ev_red_left_split : forall l r,
    Evidence_Reduce G (left_evt (split_evt l r)) l
| ev_red_right_split : forall l r,
    Evidence_Reduce G (right_evt (split_evt l r)) r
| ev_red_asp : forall p par e1 e2,
    Evidence_Reduce G e1 e2 ->
    Evidence_Reduce G (asp_evt p par e1) (asp_evt p par e2)
| ev_red_asp_unwrap_wrap : 
    forall p p' aid aid' args args' targp targp' targ targ' e' e'' n,
    Evidence_Reduce G e' (asp_evt p' (asp_paramsC aid' args' targp' targ') e'') ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP InAll OutUnwrap) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow WRAP InAll (OutN n)) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    Evidence_Reduce G (asp_evt p (asp_paramsC aid args targp targ) e') e''.

Lemma evidence_reduce_measure_decrease : forall G e1 e2,
  Evidence_Reduce G e1 e2 ->
  EvidenceT_depth e2 < EvidenceT_depth e1.
Proof.
  intros.
  induction H; simpl; ff l.
Qed.

Lemma lt_le_transfer {a b c} :
  b < c ->
  a <= b ->
  a <= c.
Proof.
  lia.
Qed.

Definition result_transfer_depth (e1 e2 : EvidenceT)
    (IHe1e2 : EvidenceT_depth e1 < EvidenceT_depth e2)
    (Re1 :Result {e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e1} string)
  : Result {e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e2} string :=
  match Re1 with
  | err s => err s
  | res (exist _ s Hs) => res (exist _ s (lt_le_transfer IHe1e2 Hs))
  end.

(* 
Fixpoint normalize_ev' `{DecEq ASP_ID} (G : GlobalContext) (e : EvidenceT) 
    : { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e }.
  ref (
    let F := normalize_ev' _ G in
    let ATEB := (apply_to_evidence_below_dep result_transfer_depth G F) in
    match e with
    | mt_evt => exist _ mt_evt (Nat.le_refl _)
    | nonce_evt n => exist _ (nonce_evt n) (Nat.le_refl _)
    | left_evt e' =>
      match ATEB [Trail_LEFT] e' with
      | err _ => (* couldn't reduce *)
        let '(exist _ e_norm He_norm) := F e' in
        match e_norm as enorm' return e_norm = enorm' -> _ with
        | split_evt l r => fun Henorm => exist _ l _
        | _ => fun Henorm => exist _ (left_evt e_norm) _
        end eq_refl
      | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
        exist _ e'res _
      end
    | right_evt e' =>
      match ATEB [Trail_RIGHT] e' with
      | err _ => (* couldn't reduce *)
        let '(exist _ e_norm He_norm) := F e' in
        match e_norm as enorm' return e_norm = enorm' -> _ with
        | split_evt l r => fun Henorm => exist _ r _
        | _ => fun Henorm => exist _ (right_evt e_norm) _
        end eq_refl
      | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
        exist _ e'res _
      end
    | split_evt l r =>
      let '(exist _ l_norm Hl_norm) := F l in
      let '(exist _ r_norm Hr_norm) := F r in
      exist _ (split_evt l_norm r_norm) _
    | asp_evt p (asp_paramsC asp_id args targ_plc targ) e' =>
      match ((asp_types G) ![ asp_id ]) with
      | None => (* couldn't top-level reduce anyways *)
        (* but still push down the effect *)
        let '(exist _ e_norm He_norm) := F e' in
        exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) e_norm) _
      | Some (ev_arrow asp_fwd in_sig out_sig) =>
        match asp_fwd with
        | UNWRAP => (* okay, we maybe can normalize *)
          match ATEB [Trail_UNWRAP asp_id] e' with
          | err _ => (* couldn't reduce *)
            let '(exist _ e_norm He_norm) := F e' in
            match e_norm as e_norm' 
              return e_norm = e_norm' -> _ 
            with
            | asp_evt p' (asp_paramsC asp_id' args' targp' targ' ) e'' =>
                fun He_norm =>
                match 
                  in_sig, out_sig,
                  (asp_types G) ![ asp_id' ], 
                  (asp_comps G) ![ asp_id' ] 
                with
                | InAll, OutUnwrap,
                  Some (ev_arrow WRAP InAll (OutN n)), 
                  Some asp_id_comp => 
                    exist _ e'' _
                | _, _, _, _ => exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) (proj1_sig (F e'))) _
                end
            | _ => 
              fun He_norm =>
              exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) (proj1_sig (F e'))) _
            end eq_refl
          | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
            exist _ e'res _
          end
        | _ => (* can't reduce at top-level, just push down *)
          let '(exist _ e_norm He_norm) := F e' in
          exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) e_norm) _
        end
      end
    end
  ).
Proof.
all: 
  assert (forall ev, EvidenceT_depth (proj1_sig (normalize_ev' _ G ev)) <= EvidenceT_depth ev) 
    by (intros ev; destruct (normalize_ev' _ G ev); ff);
  try (ff l; fail);
  try (ff; erewrite <- Nat.succ_le_mono; ff; lia).
Defined.
*)

Equations? normalize_ev `{DecEq ASP_ID} (G : GlobalContext) (e : EvidenceT) 
    : { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e } :=
  normalize_ev G e := 
    let F := normalize_ev G in
    let ATEB := (apply_to_evidence_below_dep result_transfer_depth G F) in
    match e with
    | mt_evt => exist _ mt_evt (Nat.le_refl _)
    | nonce_evt n => exist _ (nonce_evt n) (Nat.le_refl _)
    | left_evt e' =>
      match ATEB [Trail_LEFT] e' with
      | err _ => (* couldn't reduce *)
        let '(exist _ e_norm He_norm) := F e' in
        match e_norm as enorm' return e_norm = enorm' -> _ with
        | split_evt l r => fun Henorm => exist _ l _
        | _ => fun Henorm => exist _ (left_evt e_norm) _
        end eq_refl
      | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
        exist _ e'res _
      end
    | right_evt e' =>
      match ATEB [Trail_RIGHT] e' with
      | err _ => (* couldn't reduce *)
        let '(exist _ e_norm He_norm) := F e' in
        match e_norm as enorm' return e_norm = enorm' -> _ with
        | split_evt l r => fun Henorm => exist _ r _
        | _ => fun Henorm => exist _ (right_evt e_norm) _
        end eq_refl
      | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
        exist _ e'res _
      end
    | split_evt l r =>
      let '(exist _ l_norm Hl_norm) := F l in
      let '(exist _ r_norm Hr_norm) := F r in
      exist _ (split_evt l_norm r_norm) _
    | asp_evt p (asp_paramsC asp_id args targ_plc targ) e' =>
      match ((asp_types G) ![ asp_id ]) with
      | None => (* couldn't top-level reduce anyways *)
        (* but still push down the effect *)
        let '(exist _ e_norm He_norm) := F e' in
        exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) e_norm) _
      | Some (ev_arrow asp_fwd in_sig out_sig) =>
        match asp_fwd with
        | UNWRAP => (* okay, we maybe can normalize *)
          match ATEB [Trail_UNWRAP asp_id] e' with
          | err _ => (* couldn't reduce *)
            let '(exist _ e_norm He_norm) := F e' in
            match e_norm as e_norm' 
              return e_norm = e_norm' -> _ 
            with
            | asp_evt p' (asp_paramsC asp_id' args' targp' targ' ) e'' =>
                fun He_norm =>
                match 
                  in_sig, out_sig,
                  (asp_types G) ![ asp_id' ], 
                  (asp_comps G) ![ asp_id' ] 
                with
                | InAll, OutUnwrap,
                  Some (ev_arrow WRAP InAll (OutN n)), 
                  Some asp_id_comp => 
                    exist _ e'' _
                | _, _, _, _ => exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) (proj1_sig (F e'))) _
                end
            | _ => 
              fun He_norm =>
              exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) (proj1_sig (F e'))) _
            end eq_refl
          | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
            exist _ e'res _
          end
        | _ => (* can't reduce at top-level, just push down *)
          let '(exist _ e_norm He_norm) := F e' in
          exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) e_norm) _
        end
      end
    end.
Proof.
all: 
  try (clear F ATEB normalize_ev; lia);
  Control.enter (fun () => 
    subst F ATEB;
    set (ev_res := normalize_ev _ G e'); 
    clearbody ev_res; clear normalize_ev;
    destruct ev_res; simpl in *; try lia
  ).
Defined.
(* Qed.
- 
clear F ATEB normalize_ev.
all: 
  assert (forall ev, EvidenceT_depth (proj1_sig (normalize_ev _ G ev)) <= EvidenceT_depth ev) 
    by (intros ev; destruct (normalize_ev _ G ev); ff);
  try (ff l; fail);
  try (ff; erewrite <- Nat.succ_le_mono; ff; lia).
Defined. *)
Opaque normalize_ev.

(* 
Axiom hammer : False.

Equations? normalize_ev'' (HDA : DecEq ASP_ID) (G : GlobalContext) (e : EvidenceT) 
    : { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e } :=
  normalize_ev'' HDA G mt_evt := exist _ mt_evt (Nat.le_refl _);
  normalize_ev'' HDA G (nonce_evt n) := exist _ (nonce_evt n) (Nat.le_refl _);
  normalize_ev'' HDA G (left_evt e') := 
    match @apply_to_evidence_below_dep (fun e => { e'' : EvidenceT | EvidenceT_depth e'' <= EvidenceT_depth e }) _ result_transfer_depth G (normalize_ev'' HDA G) [Trail_LEFT] e' with
    | err _ => (* couldn't reduce *)
      let '(exist _ e_norm He_norm) := normalize_ev'' HDA G e' in
      match e_norm as enorm' return e_norm = enorm' -> _ with
      | split_evt l r => fun Henorm => exist _ l _
      | _ => fun Henorm => exist _ (left_evt e_norm) _
      end eq_refl
    | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
      exist _ e'res _
    end;
  normalize_ev'' HDA G (right_evt e') :=
    let F := @normalize_ev'' HDA G in
    let ATEB := @apply_to_evidence_below_dep (fun e => { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e }) _ result_transfer_depth G F in
    match ATEB [Trail_RIGHT] e' with
    | err _ => (* couldn't reduce *)
      let '(exist _ e_norm He_norm) := F e' in
      match e_norm as enorm' return e_norm = enorm' -> _ with
      | split_evt l r => fun Henorm => exist _ r _
      | _ => fun Henorm => exist _ (right_evt e_norm) _
      end eq_refl
    | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
      exist _ e'res _
    end;
  normalize_ev'' HDA G (split_evt l r) :=
    let F := @normalize_ev'' HDA G in
    let ATEB := @apply_to_evidence_below_dep (fun e => { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e }) _ result_transfer_depth G F in
    let '(exist _ l_norm Hl_norm) := F l in
    let '(exist _ r_norm Hr_norm) := F r in
    exist _ (split_evt l_norm r_norm) _;
  normalize_ev'' HDA G (asp_evt p (asp_paramsC asp_id args targ_plc targ) e') :=
    let F := normalize_ev'' HDA G in
    let ATEB := @apply_to_evidence_below_dep (fun e => { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e }) _ result_transfer_depth G F in
    match ((asp_types G) ![ asp_id ]) with
    | None => (* couldn't top-level reduce anyways *)
      (* but still push down the effect *)
      let '(exist _ e_norm He_norm) := F e' in
      exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) e_norm) _
    | Some (ev_arrow asp_fwd in_sig out_sig) =>
      match asp_fwd with
      | UNWRAP => (* okay, we maybe can normalize *)
        match ATEB [Trail_UNWRAP asp_id] e' with
        | err _ => (* couldn't reduce *)
          let '(exist _ e_norm He_norm) := F e' in
          match e_norm as e_norm' 
            return e_norm = e_norm' -> _ 
          with
          | asp_evt p' (asp_paramsC asp_id' args' targp' targ' ) e'' =>
              fun He_norm =>
              match 
                in_sig, out_sig,
                (asp_types G) ![ asp_id' ], 
                (asp_comps G) ![ asp_id' ] 
              with
              | InAll, OutUnwrap,
                Some (ev_arrow WRAP InAll (OutN n)), 
                Some asp_id_comp => 
                  exist _ e'' _
              | _, _, _, _ => exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) (proj1_sig (F e'))) _
              end
          | _ => 
            fun He_norm =>
            exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) (proj1_sig (F e'))) _
          end eq_refl
        | res (exist _ e'res He'res) => (* we did reduce some, now do top-level *)
          exist _ e'res _
        end
      | _ => (* can't reduce at top-level, just push down *)
        let '(exist _ e_norm He_norm) := F e' in
        exist _ (asp_evt p (asp_paramsC asp_id args targ_plc targ) e_norm) _
      end
    end.
Proof.
all: 
  assert (forall ev, EvidenceT_depth (proj1_sig (normalize_ev'' HDA G ev)) <= EvidenceT_depth ev) 
    by (intros ev; destruct (normalize_ev'' HDA G ev); ff);
  try (ff l; fail);
  try (ff; erewrite <- Nat.succ_le_mono; ff; lia).
Qed.

Equations? normalize_ev (G : GlobalContext) (e : EvidenceT) 
    : { e' : EvidenceT | EvidenceT_depth e' <= EvidenceT_depth e }
    by wf (EvidenceT_depth e) :=
  normalize_ev G mt_evt := exist _ mt_evt _;
  normalize_ev G (nonce_evt n) := exist _ (nonce_evt n) _;
  normalize_ev G (left_evt e') :=
    let '(exist _ e_norm He_norm) := normalize_ev G e' in
    exist _ 
    (match e_norm with
    | split_evt l r => l
    | _ => left_evt e_norm
    end) _;
  normalize_ev G (right_evt e') :=
    let '(exist _ e_norm He_norm) := normalize_ev G e' in
    exist _
    (match e_norm with
    | split_evt l r => r
    | _ => right_evt e_norm
    end) _;
  normalize_ev G (split_evt l r) :=
    let '(exist _ l_norm Hl_norm) := normalize_ev G l in
    let '(exist _ r_norm Hr_norm) := normalize_ev G r in
    exist _ (split_evt l_norm r_norm) _;
  normalize_ev G (asp_evt p par e') :=
    let '(exist _ e_norm He_norm) := normalize_ev G e' in
    match e_norm as e_norm' 
      return e_norm = e_norm' -> _ 
    with
    | asp_evt p' par' e'' =>
      fun He_norm =>
      match par, par' with
      | asp_paramsC aid args targp targ, asp_paramsC aid' args' targp' targ'' =>
        match 
          (asp_types G) ![ aid ], 
          (asp_types G) ![ aid' ], 
          (asp_comps G) ![ aid' ] 
        with
        | Some (ev_arrow UNWRAP InAll OutUnwrap), 
          Some (ev_arrow WRAP InAll (OutN n)), 
          Some aid_comp => 
            let '(exist _ n_e'' Hn_e'') := normalize_ev G e'' in
            exist _ n_e'' _
        | _, _, _ => exist _ (asp_evt p par e_norm) _
        end
      end
    | _ => fun _ => exist _ (asp_evt p par e_norm) _
    end eq_refl.
Proof.
all: try lia.
- destruct e_norm; ff l.
- destruct e_norm; ff l.
Qed.
*)

Module TestNormalizeEv.

  Parameter G : GlobalContext.

  Example test_normalize_ev1 : exists He, 
    normalize_ev G (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) = exist _ (nonce_evt 1) He.
  Proof.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.

  Example test_normalize_ev2 : exists He, 
    normalize_ev G (left_evt (left_evt (split_evt (split_evt (nonce_evt 0) (nonce_evt 1)) (nonce_evt 2)))) = exist _ (nonce_evt 0) He.
  Proof.
    intros.
    eexists.
    ltac1:(simp normalize_ev).
    reflexivity.
  Qed.

  Example test_normalize_ev3 : forall p1 p2 aid1 aid2 args1 args2 targp1 targp2 targ1 targ2,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP InAll OutUnwrap) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow WRAP InAll (OutN 42)) ->
    (asp_comps G) ![ aid2 ] = Some aid1 ->
    exists He, normalize_ev G (asp_evt p1 (asp_paramsC aid1 args1 targp1 targ1) (asp_evt p2 (asp_paramsC aid2 args2 targp2 targ2) mt_evt)) = exist _ mt_evt He.
  Proof.
    intros.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.

  (* Example test_normalize_ev'3 : forall p1 p2 aid1 aid2 args1 args2 targp1 targp2 targ1 targ2,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP InAll OutUnwrap) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow WRAP InAll (OutN 42)) ->
    (asp_comps G) ![ aid2 ] = Some aid1 ->
    exists He, normalize_ev' G (asp_evt p1 (asp_paramsC aid1 args1 targp1 targ1) (asp_evt p2 (asp_paramsC aid2 args2 targp2 targ2) mt_evt)) = exist _ mt_evt He.
  Proof.
    intros.
    eexists.
    unfold normalize_ev'.
    admit.
  Qed. *)

  Example test_normalize_ev4 : 
    forall p1 p2 p3 p4 aid1 aid2 aid3 aid4 args1 args2 args3 args4 targp1 targp2 targp3 targp4 targ1 targ2 targ3 targ4,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP InAll OutUnwrap) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow UNWRAP InAll OutUnwrap) ->
    (asp_types G) ![ aid3 ] = Some (ev_arrow WRAP InAll (OutN 1)) ->
    (asp_types G) ![ aid4 ] = Some (ev_arrow WRAP InAll (OutN 1)) ->
    (asp_comps G) ![ aid3 ] = Some aid2 ->
    (asp_comps G) ![ aid4 ] = Some aid1 ->
    exists He, normalize_ev G 
      (asp_evt p1 (asp_paramsC aid1 args1 targp1 targ1) 
        (asp_evt p2 (asp_paramsC aid2 args2 targp2 targ2) 
          (asp_evt p3 (asp_paramsC aid3 args3 targp3 targ3) 
            (asp_evt p4 (asp_paramsC aid4 args4 targp4 targ4) mt_evt)))) = exist _ mt_evt He.
  Proof.
    intros.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.
End TestNormalizeEv.

Definition Evidence_Equiv (G : GlobalContext) (e1 e2 : EvidenceT) : Prop :=
  proj1_sig (normalize_ev G e1) = proj1_sig (normalize_ev G e2).

Theorem Evidence_Equivalence : forall G,
  Equivalence (Evidence_Equiv G).
Proof.
  econstructor > [ unfold Reflexive | unfold Symmetric | unfold Transitive ]; ff.
Qed.

From RocqCandy Require Import All.

Definition Evidence_Equiv_dec `{DecEq EvidenceT} (G : GlobalContext) 
    (e1 e2 : EvidenceT) 
    : { Evidence_Equiv G e1 e2 } + { ~ Evidence_Equiv G e1 e2 } :=
  dec_eq (proj1_sig (normalize_ev G e1)) (proj1_sig (normalize_ev G e2)).

Definition canon_ev_rep (G : GlobalContext) (e : EvidenceT) : EvidenceT :=
  (* The evidence value that minimizes the measure is the canon ev rep *)
  proj1_sig (normalize_ev G e).

Lemma canon_ev_canonical : forall G e e',
  canon_ev_rep G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  unfold canon_ev_rep.
  intros.
  destruct (normalize_ev G e); ff.
Qed.

(* Key Theorem: Equivalence implies Equal Canonical Representatives *)
Lemma equiv_impl_canon_ev_rep : forall G e1 e2,
  Evidence_Equiv G e1 e2 ->
  canon_ev_rep G e1 = canon_ev_rep G e2.
Proof.
  intros.
  unfold Evidence_Equiv, canon_ev_rep in *.
  ff.
Qed.

(* Key Theorem: Unique Canonical Evidence Representative *)
Theorem canon_ev_rep_correct : forall G e,
  exists! e', canon_ev_rep G e = e'.
Proof.
  unfold canon_ev_rep, unique.
  eexists.
  ff.
Qed.

From CoplandSpec Require Import Event_System Term_Defs.

(* Well-formedness *)
(* We define well-defined under context Γ  *)

Lemma normalize_preserves_size : forall G e e',
  (proj1_sig (normalize_ev G e)) = e' ->
  et_size G e = et_size G e'.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G); 
  intros; try (ff; fail);
  ltac1:(simp normalize_ev in *).
  - ff; try (erewrite (IHe _ eq_refl); ff u, l).
  - ff.
    * ff u.
      + admit.
      + Search (apply_to_evidence_below).
      ff u.
      + ateb_simp.
    simpl in *; intros; intuition; ff u, a;
      ateb_simp; ff.
      ateb_simp.

    ; try (erewrite (IHe _ eq_refl); ff u, l).
  - admit.
  - subst.
    ltac
  - 
  induction e; try (ff; fail); intros.
  - ltac1:(simp normalize_ev in H).

(* Key Theorem: Equivalence preserves well-formedness *)
Theorem equiv_preserves_wf_ev : forall G e1 e2 bits,
  wf_Evidence G (evc bits e1) ->
  Evidence_Equiv G e1 e2 ->
  wf_Evidence G (evc bits e2).
Proof.
  intros.
  unfold Evidence_Equiv in *.
  invc H.
  pp (wf_Evidence_c).
  econstructor.
  destruct H as [bits Hwf].
  invc Hwf.
  induction Hwf.
  induction H0.
