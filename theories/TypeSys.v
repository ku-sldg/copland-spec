From CoplandSpec Require Import 
  Term_Defs_Core Term_Defs_Core_Typeclasses Event_System Term_Defs.
From Equations Require Import Equations.

(** EvidenceT equivalence relation *)
Inductive Evidence_Reduce (G : GlobalContext) : EvidenceT -> EvidenceT -> Prop :=
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
    forall p p' aid aid' args args' e' e'' n attrs1 attrs2,
    Evidence_Reduce G e' (asp_evt p' (asp_paramsC aid' args') e'') ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP attrs1 InAll OutUnwrap) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow WRAP attrs2 InAll (OutN n)) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    Evidence_Reduce G (asp_evt p (asp_paramsC aid args) e') e''.

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

Lemma sle_impl_les {a b} :
  S a <= b ->
  a <= S b.
Proof.
  lia.
Qed.

Lemma smax_le_seither {a b c} :
  S (max a b) <= c ->
  a <= S c /\ b <= S c.
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

Equations normalize_ev `{DecEq ASP_ID} (G : GlobalContext) (e : EvidenceT) 
    : EvidenceT :=
  normalize_ev G mt_evt := mt_evt;
  normalize_ev G (nonce_evt n) := nonce_evt n;
  normalize_ev G (left_evt e') :=
    match (apply_to_evidence_below G (normalize_ev G)) [Trail_LEFT] e' with
    | err _ => (* couldn't reduce *) left_evt e'
    | res e'res => e'res
    end;
  normalize_ev G (right_evt e') :=
    match (apply_to_evidence_below G (normalize_ev G)) [Trail_RIGHT] e' with
    | err _ => (* couldn't reduce *) right_evt e'
    | res e'res => e'res
    end;
  normalize_ev G (split_evt l r) := split_evt l r;
  normalize_ev G (asp_evt p (asp_paramsC asp_id args) e') :=
    match ((asp_types G) ![ asp_id ]) with
    | Some (ev_arrow UNWRAP attrs InAll OutUnwrap) =>
        match (apply_to_evidence_below G (normalize_ev G)) [Trail_UNWRAP asp_id] e' with
        | err _ => (* couldn't reduce *)
          asp_evt p (asp_paramsC asp_id args) e'
        | res e'res => e'res
        end
    | _ => (* can't reduce at top-level, just push down *)
      asp_evt p (asp_paramsC asp_id args) e'
    end.

Theorem normalize_ev_measure_decrease : forall G e e',
  normalize_ev G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  ff; ltac1:(simp normalize_ev in * ); ff l.
  - 
    find_eapply_lem_hyp @apply_to_evidence_below_res_spec; ff.
    pp (H0 _ _ H1 _ eq_refl).
    find_eapply_lem_hyp Evidence_Subterm_path_depth; ff l.
  - 
    find_eapply_lem_hyp @apply_to_evidence_below_res_spec; ff.
    pp (H _ _ H0 _ eq_refl).
    find_eapply_lem_hyp Evidence_Subterm_path_depth; ff l.
  - 
    find_eapply_lem_hyp @apply_to_evidence_below_res_spec; ff.
    pp (H _ _ H0 _ eq_refl).
    find_eapply_lem_hyp Evidence_Subterm_path_depth; ff l.
Qed.

Module TestNormalizeEv.

  Parameter G : GlobalContext.

  Example test_normalize_ev1 : 
    normalize_ev G (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) = (nonce_evt 1).
  Proof.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.

  Example test_normalize_ev2 : 
    normalize_ev G (left_evt (left_evt (split_evt (split_evt (nonce_evt 0) (nonce_evt 1)) (nonce_evt 2)))) = (nonce_evt 0).
  Proof.
    intros.
    eexists.
  Qed.

  Example test_normalize_ev3 : forall p1 p2 aid1 aid2 args1 args2 attrs1 attrs2,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP attrs1 InAll OutUnwrap) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow WRAP attrs2 InAll (OutN 42)) ->
    (asp_comps G) ![ aid2 ] = Some aid1 ->
    normalize_ev G (asp_evt p1 (asp_paramsC aid1 args1) (asp_evt p2 (asp_paramsC aid2 args2) mt_evt)) = (mt_evt).
  Proof.
    intros.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.

  Example test_normalize_ev4 : 
    forall p1 p2 p3 p4 aid1 aid2 aid3 aid4 args1 args2 args3 args4 attrs1 attrs2 attrs3 attrs4,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP attrs1 InAll OutUnwrap) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow UNWRAP attrs2 InAll OutUnwrap) ->
    (asp_types G) ![ aid3 ] = Some (ev_arrow WRAP attrs3 InAll (OutN 1)) ->
    (asp_types G) ![ aid4 ] = Some (ev_arrow WRAP attrs4 InAll (OutN 1)) ->
    (asp_comps G) ![ aid3 ] = Some aid2 ->
    (asp_comps G) ![ aid4 ] = Some aid1 ->
    normalize_ev G 
      (asp_evt p1 (asp_paramsC aid1 args1) 
        (asp_evt p2 (asp_paramsC aid2 args2) 
          (asp_evt p3 (asp_paramsC aid3 args3) 
            (asp_evt p4 (asp_paramsC aid4 args4) mt_evt)))) = (mt_evt).
  Proof.
    intros.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.
End TestNormalizeEv.

Definition Evidence_Equiv (G : GlobalContext) (e1 e2 : EvidenceT) : Prop :=
  normalize_ev G e1 = normalize_ev G e2.

Theorem Evidence_Equivalence : forall G,
  Equivalence (Evidence_Equiv G).
Proof.
  econstructor > [ unfold Reflexive | unfold Symmetric | unfold Transitive ]; ff.
Qed.

From RocqCandy Require Import All.

Definition Evidence_Equiv_dec `{DecEq EvidenceT} (G : GlobalContext) 
    (e1 e2 : EvidenceT) 
    : { Evidence_Equiv G e1 e2 } + { ~ Evidence_Equiv G e1 e2 } :=
  dec_eq (normalize_ev G e1) (normalize_ev G e2).

Definition canon_ev_rep (G : GlobalContext) (e : EvidenceT) : EvidenceT :=
  (* The evidence value that minimizes the measure is the canon ev rep *)
  normalize_ev G e.

Lemma canon_ev_canonical : forall G e e',
  canon_ev_rep G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  unfold canon_ev_rep.
  eapply normalize_ev_measure_decrease.
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

(* Well-formedness *)
(* We define well-defined under context Γ  *)

Lemma normalize_preserves_size : forall G e e',
  normalize_ev G e = e' ->
  et_size G e = et_size G e'.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G); 
  intros; try (ff; fail);
  ltac1:(simp normalize_ev in *);
  ff u, l; try (ateb_simp); ff.
Qed.

Corollary normalize_ev_preserves_size : forall G e,
  et_size G e = et_size G (normalize_ev G e).
Proof.
  intros.
  eapply normalize_preserves_size.
  reflexivity.
Qed.

(* Key Theorem: Equivalence preserves well-formedness *)
Theorem equiv_preserves_wf_ev : forall G e1 e2 bits,
  wf_Evidence G (evc bits e1) ->
  Evidence_Equiv G e1 e2 ->
  wf_Evidence G (evc bits e2).
Proof.
  intros.
  unfold Evidence_Equiv in *.
  invc H.
  econstructor.
  econstructor.
  erewrite normalize_ev_preserves_size.
  find_eapply_lem_hyp normalize_preserves_size.
  ff.
Qed.