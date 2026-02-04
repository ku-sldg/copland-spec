From CoplandSpec Require Import 
  Term_Defs_Core Term_Defs_Core_Typeclasses Event_System Term_Defs.
From Equations Require Import Equations.

(** EvidenceT equivalence relation *)
Inductive Evidence_Reduce (G : GlobalContext) : EvidenceT -> EvidenceT -> Prop :=
| ev_eq_left : forall e1 e2,
    Evidence_Reduce G e1 e2 ->
    Evidence_Reduce G (left_evt e1) (left_evt e2)
| ev_eq_right : forall e1 e2,
    Evidence_Reduce G e1 e2 ->
    Evidence_Reduce G (right_evt e1) (right_evt e2)
| ev_eq_split : forall e1 e2 e1' e2',
    Evidence_Reduce G e1 e1' ->
    Evidence_Reduce G e2 e2' ->
    Evidence_Reduce G (split_evt e1 e2) (split_evt e1' e2')
| ev_eq_left_split : forall l r e,
    Evidence_Reduce G e (split_evt l r) ->
    Evidence_Reduce G (left_evt e) l
| ev_eq_right_split : forall l r e,
    Evidence_Reduce G e (split_evt l r) ->
    Evidence_Reduce G (right_evt e) r
| ev_eq_asp : forall p par e1 e2,
    Evidence_Reduce G e1 e2 ->
    Evidence_Reduce G (asp_evt p par e1) (asp_evt p par e2)
| ev_eq_asp_unwrap_wrap : 
    forall p p' aid aid' args args' e' e'' n attrs1 attrs2,
    Evidence_Reduce G e' (asp_evt p' (asp_paramsC aid' args') e'') ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP attrs1 InAll) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP n) attrs2 InAll) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    Evidence_Reduce G (asp_evt p (asp_paramsC aid args) e') e''.

Lemma evidence_reduce_measure_decrease : forall G e1 e2,
  Evidence_Reduce G e1 e2 ->
  EvidenceT_depth e2 < EvidenceT_depth e1.
Proof.
  intros.
  induction H; simpl; ff l.
Qed.

Equations? normalize_ev (G : GlobalContext) (e : EvidenceT) 
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
        | Some (ev_arrow UNWRAP attrs1 in_sig) =>
            match ((asp_types G) ![ asp_id' ]) with
            | Some (ev_arrow (WRAP n) attrs2 in_sig) =>
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
ff l.
ff l.
Defined.

Theorem normalize_ev_measure_decrease : forall G e e',
  normalize_ev G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  intros.
  ltac1:( funelim (normalize_ev G e); simp normalize_ev in * ); ff l;
  try (pp (H _ eq_refl); ff l; fail).
  pp (H _ eq_refl); pp (H0 _ eq_refl); ff l.
Qed.

Module TestNormalizeEv.

  Parameter G : GlobalContext.

  Example test_normalize_ev1 : 
    normalize_ev G (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) = (nonce_evt 1).
  Proof.
    ff.
  Qed.

  Example test_normalize_ev2 : 
    normalize_ev G (left_evt (left_evt (split_evt (split_evt (nonce_evt 0) (nonce_evt 1)) (nonce_evt 2)))) = (nonce_evt 0).
  Proof.
    ff.
  Qed.

  Example test_normalize_ev3 : forall p1 p2 aid1 aid2 args1 args2 attrs1 attrs2,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP attrs1 InAll) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow (WRAP 42) attrs2 InAll) ->
    (asp_comps G) ![ aid2 ] = Some aid1 ->
    normalize_ev G (asp_evt p1 (asp_paramsC aid1 args1) (asp_evt p2 (asp_paramsC aid2 args2) mt_evt)) = (mt_evt).
  Proof.
    ff.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.

  Example test_normalize_ev4 : 
    forall p1 p2 p3 p4 aid1 aid2 aid3 aid4 args1 args2 args3 args4 attrs1 attrs2 attrs3 attrs4,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP attrs1 InAll) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow UNWRAP attrs2 InAll) ->
    (asp_types G) ![ aid3 ] = Some (ev_arrow (WRAP 1) attrs3 InAll) ->
    (asp_types G) ![ aid4 ] = Some (ev_arrow (WRAP 1) attrs4 InAll) ->
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

  Example test_normalize_ev5 : forall G,
    normalize_ev G (split_evt (left_evt (split_evt (nonce_evt 1) mt_evt)) (nonce_evt 2)) =
      split_evt (nonce_evt 1) (nonce_evt 2).
  Proof.
    ff.
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
  ff.
  eapply normalize_ev_measure_decrease; ff.
Qed.

(* Lemma normalize_ev_no_esp_path : forall G e t1 trails e',
  ~ (Evidence_Subterm_path G e' (t1 :: trails) (normalize_ev G e)).
Proof.
  intros.
  intros HC.
  find_eapply_lem_hyp Evidence_Subterm_path_depth_cons.
  pp (canon_ev_canonical G e e').
  unfold canon_ev_rep in *.
  lia.
Qed. *)

(* Key Theorem: Equivalence implies Equal Canonical Representatives *)
Lemma equiv_impl_canon_ev_rep : forall G e1 e2,
  Evidence_Equiv G e1 e2 ->
  canon_ev_rep G e1 = canon_ev_rep G e2.
Proof.
  intros.
  unfold Evidence_Equiv, canon_ev_rep in *.
  ff.
Qed.

Lemma canon_ev_min_depth : forall G e e',
  Evidence_Equiv G e e' ->
  EvidenceT_depth (canon_ev_rep G e) <= EvidenceT_depth e' .
Proof.
  intros.
  eapply (canon_ev_canonical G e' (canon_ev_rep G e)).
  eapply equiv_impl_canon_ev_rep; ff.
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

(* Lemma normalize_preserves_size : forall G e e',
  normalize_ev G e = e' ->
  et_size G e = et_size G e'.
Proof.
  intros.
  ltac1:( funelim (normalize_ev G e); simp normalize_ev in * ); ff u, l;
  try (pp (H _ eq_refl); ff u, l; fail).
  - unpack_atebs.
  pp (H _ eq_refl); pp (H0 _ eq_refl); ff l.

  intros G.
  induction e.

  induction e using (Evidence_subterm_path_Ind_special G); 
  intros; try (ff; fail);
  ltac1:(simp normalize_ev in * );
  ff u, l; ateb_simp; ff;
  try (pp (IHe _ eq_refl); ff l; fail);
  try (pp (IHe1 _ eq_refl); pp (IHe2 _ eq_refl); ff l; fail).
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
*)

(** The Evidence Type Denotational Semantics:

This differs from the paper's presentation, but essentially it just shows how
big the evidence stack is/should be for a given evidence type
*)
Inductive evt_stack_denotation (G : GlobalContext) : EvidenceT -> nat -> Prop :=
| interp_mt : evt_stack_denotation G mt_evt 0
| interp_nonce : forall n, evt_stack_denotation G (nonce_evt n) 1
| interp_split : forall l r s1 s2,
    evt_stack_denotation G l s1 ->
    evt_stack_denotation G r s2 ->
    evt_stack_denotation G (split_evt l r) (s1 + s2)
| interp_left : forall e' l r n,
    canon_ev_rep G e' = split_evt l r ->
    evt_stack_denotation G l n ->
    evt_stack_denotation G (left_evt e') n
| interp_right : forall e' l r n,
    canon_ev_rep G e' = split_evt l r ->
    evt_stack_denotation G r n ->
    evt_stack_denotation G (right_evt e') n
| interp_asp_replace : forall p aid attrs isig args e' n,
    (asp_types G) ![ aid ] = Some (ev_arrow (REPLACE n) attrs isig) ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') n
| interp_asp_extend : forall p aid attrs isig args e' n n_ext,
    (asp_types G) ![ aid ] = Some (ev_arrow (EXTEND n_ext) attrs isig) ->
    evt_stack_denotation G e' n ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') (n_ext + n)
| interp_asp_wrap : forall p aid attrs isig args e' n,
    (asp_types G) ![ aid ] = Some (ev_arrow (WRAP n) attrs isig) ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') n
| interp_asp_unwrap : forall p p' aid aid' attrs attrs' isig isig' args args' e' e'' n n_orig,
    canon_ev_rep G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP attrs' isig') ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP n) attrs isig) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    evt_stack_denotation G e'' n_orig ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') n_orig.

Ltac2 Notation "evter" := (ff (fun () => eauto using evt_stack_denotation)).

Definition wf_EvidenceT (G : GlobalContext) (e : EvidenceT) : Prop :=
  exists n, evt_stack_denotation G e n.

Lemma equiv_preserves_denotation_size_fwd : forall G e n,
  evt_stack_denotation G e n ->
  evt_stack_denotation G (normalize_ev G e) n.
Proof.
  intros.
  ltac1:( funelim (normalize_ev G e)).
  - eauto.
  - eauto.
  - invc H0.
    + rewrite H6 in *.
      ff; rewrite <- Heqcall; evter.
    + rewrite H6 in *.
      ff; rewrite <- Heqcall; evter.
    + rewrite H6 in *.
      ff; rewrite <- Heqcall; evter.
    + unfold canon_ev_rep in *.
      rewrite H5 in *.
      ff.
  - invc H0.
    unfold canon_ev_rep in *.
    rewrite H2 in *.
    eauto.
  - invc H0.
    unfold canon_ev_rep in *.
    rewrite H2 in *.
    eauto.
  - invc H1.
    ff a.
    erewrite <- Heqcall.
    evter.
Qed.

Lemma normalize_ev_done : forall G e e',
  normalize_ev G e = e' ->
  normalize_ev G e' = e'.
Proof.
  intros.
  subst.
  induction e;
  try (destruct a); 
  repeat (ltac1:( simp normalize_ev in * ); ff).
Qed.

Lemma equiv_preserves_denotation_size_rev : forall G e n,
  evt_stack_denotation G (normalize_ev G e) n ->
  evt_stack_denotation G e n.
Proof.
  intros.
  ltac1:( funelim (normalize_ev G e)).
  - eauto.
  - eauto.
  - ff;
    try (rewrite <- Heqcall in *;
      invc H0; evter;
      unfold canon_ev_rep in *;
      ltac1:( simp normalize_ev in * ); evter; fail).
    + ltac1:( simp normalize_ev in Heqe ).
      break_match; try congruence.
      break_match.
      injection Heqe; intros.
      ltac1:( simp normalize_ev in H0 ).
      erewrite Heqe0 in *.
      subst.
      rewrite Heqo in *.
      rewrite Heqo0 in *.
      rewrite Heqo1 in *.
      clear H1.
      break_match; try congruence.
      clean.
      evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      unfold canon_ev_rep in *;
      ltac1:( simp normalize_ev in * ); evter.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      unfold canon_ev_rep in *;
      ltac1:( simp normalize_ev in * ); evter.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      unfold canon_ev_rep in *;
      ltac1:( simp normalize_ev in * ); evter.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); evter.
  - ff.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); congruence.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); congruence.
    + rewrite <- Heqcall in *.
      (* clear Heqcall. *)
      invc H0.
      unfold canon_ev_rep in *.
      destruct a.
      ltac1:( simp normalize_ev in * ).
      ff.
      eapply interp_left; ff.
      unfold canon_ev_rep in *.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); ff.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); ff.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); ff.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); ff.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); ff.
    + invc H0.
      * ltac1:( simp normalize_ev in * ).
        rewrite <- H2 in *.
        evter.
      * ltac1:( simp normalize_ev in * ).
        rewrite <- H2 in *.
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
  - ff.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); congruence.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); congruence.
    + rewrite <- Heqcall in *.
      invc H0.
      unfold canon_ev_rep in *.
      ltac1:( simp normalize_ev in * ); ff.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); ff.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); ff.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); ff.
    + rewrite <- Heqcall in *.
      invc H0.
      ltac1:( simp normalize_ev in * ); ff.
      eapply normalize_ev_done in Heqe.
      ltac1:( simp normalize_ev in * ); ff.
    + invc H0.
      * ltac1:( simp normalize_ev in * ).
        rewrite <- H2 in *.
        evter.
      * ltac1:( simp normalize_ev in * ).
        rewrite <- H2 in *.
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
      * ltac1:( simp normalize_ev in * ).
        evter.
  - ff.
    rewrite <- Heqcall in *.
    invc H1.
    evter.
  Unshelve. eapply mt_evt.
Qed.

Theorem equiv_preserves_denotation_size : forall G e n,
  evt_stack_denotation G e n <-> evt_stack_denotation G (normalize_ev G e) n.
Proof.
  split.
  - eapply equiv_preserves_denotation_size_fwd.
  - eapply equiv_preserves_denotation_size_rev.
Qed.

Theorem equiv_preserves_wf_EvidenceT : forall G e,
  wf_EvidenceT G e ->
  forall e',
    Evidence_Equiv G e e' ->
    wf_EvidenceT G e'.
Proof.
  intros.
  unfold wf_EvidenceT in *.
  ff.
  eapply equiv_preserves_denotation_size in H.
  erewrite H0 in H.
  exists x.
  erewrite equiv_preserves_denotation_size.
  ff.
Qed.

(** Typechecking 

Here we actually introduce and utilize the typechecking rules
*)

(* Inductive typeof (G : GlobalContext) : CopPhrase -> EvidenceT -> Prop :=
| tc_null : forall p e,
    typeof G (cop_phrase p e (asp NULL)) mt_evt
| tc_sig : forall p e n attrs,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot sign empty evidence *)
    (asp_types G) ![ sig_aspid ] = Some (ev_arrow (EXTEND 1) attrs InAll) ->
    typeof G (cop_phrase p e (asp SIG)) (asp_evt p sig_params e)
| tc_hsh : forall p e n attrs,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot hash empty evidence *)
    (asp_types G) ![ hsh_aspid ] = Some (ev_arrow (REPLACE 1) attrs InAll) ->
    typeof G (cop_phrase p e (asp HSH)) (asp_evt p hsh_params e)
| tc_enc : forall p e n attrs p',
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot encrypt empty evidence *)
    (asp_types G) ![ enc_aspid ] = Some (ev_arrow (WRAP 1) attrs InAll) ->
    typeof G (cop_phrase p e (asp (ENC p'))) (asp_evt p (enc_params p') e)
| tc_in_none : forall p e fwd aid args attrs,
    evt_stack_denotation G e 0 -> (* must have empty evidence as input *)
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs InNone) ->
    typeof G 
      (cop_phrase p e (asp (ASPC (asp_paramsC aid args)))) 
      (asp_evt p (asp_paramsC aid args) e)
| tc_in_all : forall p e n fwd aid args attrs,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot have empty evidence as input *)
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs InAll) ->
    typeof G
      (cop_phrase p e (asp (ASPC (asp_paramsC aid args))))
      (asp_evt p (asp_paramsC aid args) e)
| tc_att : forall p q e t' e',
    typeof G (cop_phrase q e t') e' ->
    typeof G (cop_phrase p e (att q t')) e'
| tc_lseq : forall p e t1 t2 e1 e2,
    typeof G (cop_phrase p e t1) e1 ->
    typeof G (cop_phrase p e1 t2) e2 ->
    typeof G (cop_phrase p e (lseq t1 t2)) e2
| tc_bseq : forall p e t1 t2 e1 e2,
    typeof G (cop_phrase p e t1) e1 ->
    typeof G (cop_phrase p e t2) e2 ->
    typeof G (cop_phrase p e (bseq t1 t2)) (split_evt e1 e2)
| tc_par : forall p e t1 t2 e1 e2,
    typeof G (cop_phrase p e t1) e1 ->
    typeof G (cop_phrase p e t2) e2 ->
    typeof G (cop_phrase p e (par t1 t2)) (split_evt e1 e2). *)
