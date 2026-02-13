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
    forall p p' aid aid' args args' e' e'' n attrs1 attrs2 nlt,
    Evidence_Reduce G e' (asp_evt p' (asp_paramsC aid' args') e'') ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP attrs1) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP (exist _ n nlt)) attrs2) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    Evidence_Reduce G (asp_evt p (asp_paramsC aid args) e') e''.

Lemma evidence_reduce_measure_decrease : forall G e1 e2,
  Evidence_Reduce G e1 e2 ->
  EvidenceT_depth e2 < EvidenceT_depth e1.
Proof.
  intros.
  induction H; simpl; ff with l.
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

Theorem normalize_ev_measure_decrease : forall G e e',
  normalize_ev G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  intros.
  ltac1:( funelim (normalize_ev G e); simp normalize_ev in * ); ff with l;
  try (pp (H _ eq_refl); ff with l; fail).
  pp (H _ eq_refl); pp (H0 _ eq_refl); ff with l.
Qed.

(* --- Helper Definitions to keep the Type signature clean --- *)

Theorem normalize_ev_ind_custom (G : GlobalContext) (P : EvidenceT -> Prop)
  (* 1. Base Case: Mt *)
  (P_mt : P mt_evt)
  (* 2. Base Case: Nonce *)
  (P_nonce : forall n, P (nonce_evt n))
  (* 3. Left Case: Recursive result IS a split (Returns l) *)
  (P_left_split : forall e' l r,
      normalize_ev G e' = split_evt l r ->
      P l ->
      P (left_evt e'))
  (* 4. Left Case: Recursive result is NOT a split (Returns left_evt res) *)
  (P_left_keep : forall e',
      match normalize_ev G e' with
      | split_evt l r => False
      | _ => True
      end ->
      P e' ->
      P (left_evt e'))
  (* 5. Right Case: Recursive result IS a split (Returns r) *)
  (P_right_split : forall e' l r,
      normalize_ev G e' = split_evt l r ->
      P r ->
      P (right_evt e'))
  (* 6. Right Case: Recursive result is NOT a split (Returns right_evt res) *)
  (P_right_keep : forall e',
      match normalize_ev G e' with
      | split_evt l r => False
      | _ => True
      end ->
      P e' ->
      P (right_evt e'))
  (* 7. Split Case: Standard recursion (Always returns split) *)
  (P_split : forall l r,
      P l -> P r -> P (split_evt l r))
  (* 8. Asp Case: COLLAPSE (Inner is Asp + Types Match) *)
  (P_asp_unwrap_wrap : forall p aid args e' p' aid' args' e'',
      normalize_ev G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
      match (asp_types G) ![ aid ] with
      | Some (ev_arrow UNWRAP attrs1) =>
          match (asp_types G) ![ aid' ] with
          | Some (ev_arrow (WRAP (exist _ n nlt)) attrs2) =>
              match (asp_comps G) ![ aid' ] with
              | Some test_unwrapping_id =>
                  (* Using strict equality for Prop, user can decide with DecEq in proofs *)
                  test_unwrapping_id = aid 
              | None => False
              end
          | _ => False
          end
      | _ => False
      end ->
      P e'' ->
      P (asp_evt p (asp_paramsC aid args) e'))
  (* 9. Asp Case: MISMATCH (Inner is Asp + Types Fail) *)
  (P_asp_mis : forall p aid args e' p' aid' args' e'',
      normalize_ev G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
      match (asp_types G) ![ aid ] with
      | Some (ev_arrow UNWRAP attrs1) =>
          match (asp_types G) ![ aid' ] with
          | Some (ev_arrow (WRAP (exist _ n nlt)) attrs2) =>
              match (asp_comps G) ![ aid' ] with
              | Some test_unwrapping_id =>
                  (* Using strict equality for Prop, user can decide with DecEq in proofs *)
                  test_unwrapping_id <> aid 
              | None => True
              end
          | _ => True
          end
      | _ => True
      end ->
      P e' ->
      P (asp_evt p (asp_paramsC aid args) e'))

  (* 10. Asp Case: PRESERVE (Inner is NOT Asp) *)
  (P_asp_preserve : forall p aid args e' res,
      normalize_ev G e' = res ->
      (forall p' aid' args' e'', res <> asp_evt p' (asp_paramsC aid' args') e'') ->
      P res ->
      P (asp_evt p (asp_paramsC aid args) e'))
  : forall e, P e.
Proof.
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    intros x F.
    destruct x eqn:?; ff.
    - (* asp *)
      remember (normalize_ev G e) as res eqn:Heq.

      destruct a as [ aid args ].
      destruct res;
      (* 1. Case: res is NOT asp_evt (mt, nonce, left, right, split) *)
      (* All these map to Hasp_pre *)
      try (eapply P_asp_preserve; ff;
        symmetry in Heq;
        try (pp (normalize_ev_measure_decrease _ _ _ Heq);
        eapply F; ff with l); fail).
      destruct a as [ aid' args' ].
      (* 2. Case: res IS asp_evt. Now we must inspect the Collapse Logic. *)
      (* We define the condition locally to destruct it *)
      destruct ((asp_types G) ![ aid ]) eqn:Ht_outer;
      try (eapply P_asp_mis; ff; fail).
      destruct e0; (* ev_arrow *)
      try (eapply P_asp_mis; ff; fail).
      destruct e0; (* UNWRAP check *)
      try (eapply P_asp_mis; ff; fail).
        
      (* Inner Type Check *)
      destruct ((asp_types G) ![ aid' ]) eqn:Ht_inner;
      try (eapply P_asp_mis; ff; fail).

      destruct e0, e0; (* ev_arrow + WRAP check *)
      try (eapply P_asp_mis; ff; fail).
      destruct n. (* exist _ n nlt *)
      (* Comps Check *)
      destruct ((asp_comps G) ![ aid' ]) eqn:Hcomps;
      try (eapply P_asp_mis; ff; fail).
      
      (* Equality Check *)
      destruct (DecEq.dec_eq a aid); ff.
      + (* EQUAL: Collapse *)
        eapply P_asp_unwrap_wrap; ff.
        eapply F.
        symmetry in Heq.
        eapply normalize_ev_measure_decrease in Heq.
        ff with l.
      + (* NOT EQUAL: Mismatch *)
        eapply P_asp_mis; ff.
    - (* left *)
      (* We remember the result of normalization to trigger the correct hypothesis *)
      remember (normalize_ev G e) as res eqn:Heq.
      destruct res; ff;
      try (eapply P_left_keep; ff; fail).

      eapply P_left_split; ff.
      eapply F.
      symmetry in Heq.
      eapply normalize_ev_measure_decrease in Heq.
      ff with l.

    - (* right *)
      (* We remember the result of normalization to trigger the correct hypothesis *)
      remember (normalize_ev G e) as res eqn:Heq.
      destruct res; ff;
      try (eapply P_right_keep; ff; fail).

      eapply P_right_split; ff.
      eapply F.
      symmetry in Heq.
      eapply normalize_ev_measure_decrease in Heq.
      ff with l.
    - (* split *)
      apply P_split; eapply F; ff with l.
  }
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.

Ltac2 Notation "norm" := ltac1:( simp normalize_ev in * ).
Ltac2 Notation "normer" := (norm; ff).

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
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP attrs1) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow (WRAP (exist _ 1 Nat.lt_0_1)) attrs2) ->
    (asp_comps G) ![ aid2 ] = Some aid1 ->
    normalize_ev G (asp_evt p1 (asp_paramsC aid1 args1) (asp_evt p2 (asp_paramsC aid2 args2) mt_evt)) = (mt_evt).
  Proof.
    ff.
    repeat (ltac1:(simp normalize_ev in *); ff).
  Qed.

  Example test_normalize_ev4 : 
    forall p1 p2 p3 p4 aid1 aid2 aid3 aid4 args1 args2 args3 args4 attrs1 attrs2 attrs3 attrs4,
    (asp_types G) ![ aid1 ] = Some (ev_arrow UNWRAP attrs1) ->
    (asp_types G) ![ aid2 ] = Some (ev_arrow UNWRAP attrs2) ->
    (asp_types G) ![ aid3 ] = Some (ev_arrow (WRAP (exist _ 1 Nat.lt_0_1)) attrs3) ->
    (asp_types G) ![ aid4 ] = Some (ev_arrow (WRAP (exist _ 1 Nat.lt_0_1)) attrs4) ->
    (asp_comps G) ![ aid3 ] = Some aid2 ->
    (asp_comps G) ![ aid4 ] = Some aid1 ->
    normalize_ev G 
      (asp_evt p1 (asp_paramsC aid1 args1) 
        (asp_evt p2 (asp_paramsC aid2 args2) 
          (asp_evt p3 (asp_paramsC aid3 args3) 
            (asp_evt p4 (asp_paramsC aid4 args4) mt_evt)))) = (mt_evt).
  Proof.
    intros.
    normer.
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
Global Hint Unfold Evidence_Equiv : core.

Theorem Evidence_Equivalence : forall G,
  Equivalence (Evidence_Equiv G).
Proof.
  econstructor > [ unfold Reflexive | unfold Symmetric | unfold Transitive ]; 
  ff with u.
Qed.

From RocqCandy Require Import All.

Definition Evidence_Equiv_dec `{DecEq EvidenceT} (G : GlobalContext) 
    (e1 e2 : EvidenceT) 
    : { Evidence_Equiv G e1 e2 } + { ~ Evidence_Equiv G e1 e2 } :=
  dec_eq (normalize_ev G e1) (normalize_ev G e2).

Definition canon_ev_rep (G : GlobalContext) (e : EvidenceT) : EvidenceT :=
  (* The evidence value that minimizes the measure is the canon ev rep *)
  normalize_ev G e.
Global Hint Unfold canon_ev_rep : core.

Lemma canon_ev_canonical : forall G e e',
  canon_ev_rep G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  ff with u.
  eapply normalize_ev_measure_decrease; ff.
Qed.

(* Key Theorem: Equivalence implies Equal Canonical Representatives *)
Lemma equiv_impl_canon_ev_rep : forall G e1 e2,
  Evidence_Equiv G e1 e2 ->
  canon_ev_rep G e1 = canon_ev_rep G e2.
Proof.
  ff with u.
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

(** The Evidence Type Denotational Semantics:

This differs from the paper's presentation, but essentially it just shows how
big the evidence stack is/should be for a given evidence type
*)
Inductive wf_EvT (G : GlobalContext) : EvidenceT -> Prop :=
| wf_EvT_mt : wf_EvT G mt_evt
| wf_EvT_nonce : forall n, wf_EvT G (nonce_evt n)
| wf_EvT_split : forall l r,
    wf_EvT G l ->
    wf_EvT G r ->
    wf_EvT G (split_evt l r)
| wf_EvT_left : forall e' l r,
    normalize_ev G e' = split_evt l r ->
    wf_EvT G l ->
    wf_EvT G (left_evt e')
| wf_EvT_right : forall e' l r,
    normalize_ev G e' = split_evt l r ->
    wf_EvT G r ->
    wf_EvT G (right_evt e')
| wf_EvT_asp_replace : forall p aid attrs args e' n,
    wf_EvT G e' ->
    (asp_types G) ![ aid ] = Some (ev_arrow (REPLACE n) attrs) ->
    wf_EvT G (asp_evt p (asp_paramsC aid args) e')
| wf_EvT_asp_extend : forall p aid attrs isig args e' n_ext,
    (asp_types G) ![ aid ] = Some (ev_arrow (EXTEND n_ext isig) attrs) ->
    wf_EvT G e' ->
    wf_EvT G (asp_evt p (asp_paramsC aid args) e')
| wf_EvT_asp_wrap : forall p aid attrs args e' n,
    wf_EvT G e' ->
    (asp_types G) ![ aid ] = Some (ev_arrow (WRAP n) attrs) ->
    wf_EvT G (asp_evt p (asp_paramsC aid args) e')
| wf_EvT_asp_unwrap : forall p p' aid aid' attrs attrs' args args' e' e'' n,
    normalize_ev G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP attrs') ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP n) attrs) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    wf_EvT G e'' ->
    wf_EvT G (asp_evt p (asp_paramsC aid args) e').

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
    normalize_ev G e' = split_evt l r ->
    evt_stack_denotation G l n ->
    evt_stack_denotation G (left_evt e') n
| interp_right : forall e' l r n,
    normalize_ev G e' = split_evt l r ->
    evt_stack_denotation G r n ->
    evt_stack_denotation G (right_evt e') n
| interp_asp_replace : forall p aid attrs args e' n n' nlt,
    evt_stack_denotation G e' n' ->
    (asp_types G) ![ aid ] = Some (ev_arrow (REPLACE (exist _ n nlt)) attrs) ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') n
| interp_asp_extend : forall p aid attrs isig args e' n n_ext n_extlt,
    (asp_types G) ![ aid ] 
      = Some (ev_arrow (EXTEND (exist _ n_ext n_extlt) isig) attrs) ->
    evt_stack_denotation G e' n ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') (n_ext + n)
| interp_asp_wrap : forall p aid attrs args e' n n' nlt,
    evt_stack_denotation G e' n' ->
    (asp_types G) ![ aid ] = Some (ev_arrow (WRAP (exist _ n nlt)) attrs) ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') n
| interp_asp_unwrap : forall p p' aid aid' attrs attrs' args args' e' e'' n nlt n_orig,
    normalize_ev G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    (asp_types G) ![ aid ] = Some (ev_arrow UNWRAP attrs') ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP (exist _ n nlt)) attrs) ->
    (asp_comps G) ![ aid' ] = Some aid ->
    evt_stack_denotation G e'' n_orig ->
    evt_stack_denotation G (asp_evt p (asp_paramsC aid args) e') n_orig.

Ltac2 Notation "evter" := (ff with (eauto using evt_stack_denotation)).

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
    + find_rewrite.
      ff; rewrite <- Heqcall; evter.
    + find_rewrite.
      ff; rewrite <- Heqcall; evter.
    + find_rewrite.
      ff; rewrite <- Heqcall; evter.
    + find_rewrite.
      ff.
  - invc H0; ff.
  - invc H0; ff.
  - invc H1.
    ff with a.
    erewrite <- Heqcall.
    evter.
Qed.

Theorem evt_stack_denotation_iff_wf_EvT : forall G e,
  (exists n, evt_stack_denotation G e n) <-> wf_EvT G e.
Proof.
  ff.
  - induction Hex; eauto using wf_EvT.
  - induction H; ff with (eauto using evt_stack_denotation);
    Control.enter (fun () => match! goal with
    | [ n : pos_nat |- _ ] => 
      let n := Control.hyp n in
      destruct $n
    end); ff with (eauto using evt_stack_denotation).
Qed.

Lemma normalize_ev_done : forall G e e',
  normalize_ev G e = e' ->
  normalize_ev G e' = e'.
Proof.
  intros.
  subst.
  induction e;
  try (destruct a); 
  repeat (normer; ff).
Qed.

Theorem normalize_ev_idempotent : forall G e,
  normalize_ev G (normalize_ev G e) = normalize_ev G e.
Proof.
  intros.
  eapply normalize_ev_done.
  ff.
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
      normer; evter; fail).
    + ltac1:( simp normalize_ev in * ).
      evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      normer; evter.
      eapply normalize_ev_done in Heq5.
      ltac1:( simp normalize_ev in Heq5 ).
      ff.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      normer; evter.
      eapply normalize_ev_done in Heq1.
      normer; evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      normer; evter.
      eapply normalize_ev_done in Heq1.
      normer; evter.
  - ff.
    + rewrite <- Heqcall in *.
      invc H0.
      normer; congruence.
    + rewrite <- Heqcall in *.
      invc H0.
      normer; congruence.
    + rewrite <- Heqcall in *.
      (* clear Heqcall. *)
      invc H0.
      destruct a.
      normer.
      eapply interp_left; ff with u.
      eapply normalize_ev_done in Heq4.
      normer.
    + rewrite <- Heqcall in *.
      invc H0.
      normer; eapply normalize_ev_done in Heq1; normer.
    + rewrite <- Heqcall in *.
      invc H0.
      normer. 
      eapply normalize_ev_done in Heq1; normer.
    + invc H0; norm; try (rewrite <- H2 in *); evter.
  - ff.
    + rewrite <- Heqcall in *; invc H0; normer.
    + rewrite <- Heqcall in *; invc H0; normer.
    + rewrite <- Heqcall in *.
      invc H0.
      normer; eapply normalize_ev_done in Heq0; normer.
    + rewrite <- Heqcall in *.
      invc H0.
      normer; eapply normalize_ev_done in Heq1; normer.
    + rewrite <- Heqcall in *.
      invc H0.
      normer; eapply normalize_ev_done in Heq1; normer.
    + invc H0; norm; try (rewrite <- H2 in *); evter.
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
  find_eapply_lem_hyp equiv_preserves_denotation_size.
  ff with u.
  erewrite <- H0 in Hex.
  exists x.
  erewrite equiv_preserves_denotation_size.
  ff.
Qed.

(** Typechecking 

Here we actually introduce and utilize the typechecking rules
*)

Inductive typeof (G : GlobalContext) 
    : Plc -> EvidenceT -> Term -> EvidenceT -> Prop :=
(* Atomic ASP TC Rules *)
(* 

We outlaw NULL
- why? because allowing it will almost ASSUREDLY break provenance
  preservation, as NULL evidence will always discard the input "e"
  and return empty evidence, making it impossible to recover "e"

| tc_null : forall p e,
    typeof G (cop_phrase p e (asp NULL)) mt_evt 
*)
| tc_sig : forall p e n attrs nlt,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot sign empty evidence *)
    (asp_types G) ![ sig_aspid ] 
      = Some (ev_arrow (EXTEND (exist _ 1 nlt) InAll) attrs) ->
    typeof G p e (asp SIG) (asp_evt p sig_params e)
| tc_hsh : forall p e n attrs nlt,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot hash empty evidence *)
    (asp_types G) ![ hsh_aspid ] = Some (ev_arrow (REPLACE (exist _ 1 nlt)) attrs) ->
    typeof G p e (asp HSH) (asp_evt p hsh_params e)
| tc_enc : forall p e n attrs nlt p',
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot encrypt empty evidence *)
    (asp_types G) ![ enc_aspid ] = Some (ev_arrow (WRAP (exist _ 1 nlt)) attrs) ->
    typeof G p e (asp (ENC p')) (asp_evt p (enc_params p') e)
| tc_extend_in_none : forall p e aid args attrs n nlt,
    evt_stack_denotation G e 0 -> (* must have empty evidence as input *)
    (asp_types G) ![ aid ] 
      = Some (ev_arrow (EXTEND (exist _ n nlt) InNone) attrs) ->
    typeof G 
      p e (asp (ASPC (asp_paramsC aid args)))
      (asp_evt p (asp_paramsC aid args) e)
| tc_extend_in_all : forall p e aid args attrs n nlt,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot have empty evidence as input *)
    (asp_types G) ![ aid ] 
      = Some (ev_arrow (EXTEND (exist _ n nlt) InAll) attrs) ->
    typeof G 
      p e (asp (ASPC (asp_paramsC aid args)))
      (asp_evt p (asp_paramsC aid args) e)
| tc_in_all : forall p e n fwd aid args attrs,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot have empty evidence as input *)
    (forall n nlt, fwd <> EXTEND (exist _ n nlt) InNone) ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    typeof G
      p e (asp (ASPC (asp_paramsC aid args)))
      (asp_evt p (asp_paramsC aid args) e)
(* Operator TC Rules *)
| tc_att : forall p q e t' e',
    typeof G q e t' e' ->
    typeof G p e (att q t') e'
| tc_lseq : forall p e t1 t2 e1 e2,
    typeof G p e t1 e1 ->
    typeof G p e1 t2 e2 ->
    typeof G p e (lseq t1 t2) e2
| tc_bseq : forall p e t1 t2 e1 e2,
    typeof G p e t1 e1 ->
    typeof G p e t2 e2 ->
    typeof G p e (bseq t1 t2) (split_evt e1 e2)
| tc_bpar : forall p e t1 t2 e1 e2,
    typeof G p e t1 e1 ->
    typeof G p e t2 e2 ->
    typeof G p e (bpar t1 t2) (split_evt e1 e2)
(* Appraisal TC Rules *)
| tc_appr_mt : forall p e,
    normalize_ev G e = mt_evt ->
    typeof G p e (asp APPR) e
| tc_appr_nonce : forall p e n attrs nlt,
    normalize_ev G e = nonce_evt n ->
    (asp_types G) ![ check_nonce_aspid ] = Some (ev_arrow (REPLACE (exist _ 1 nlt)) attrs) ->
    typeof G p e (asp APPR) (asp_evt p check_nonce_params e)
| tc_appr_asp_unwrap_wrap : forall p p' e aid args e' appr_id attrs attrs' e'' nv,
    typeof G p e' (asp APPR) e'' ->
    normalize_ev G e = asp_evt p' (asp_paramsC aid args) e' ->
    (asp_types G) ![ appr_id ] = Some (ev_arrow UNWRAP attrs) ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    (asp_types G) ![ aid ] = Some (ev_arrow (WRAP nv) attrs') ->
    typeof G p e (asp APPR) (asp_evt p (asp_paramsC appr_id args) e)
| tc_appr_asp : forall p p' e aid args e' appr_id fwd fwd' attrs attrs' e'',
    typeof G p e' (asp APPR) e'' ->
    normalize_ev G e = asp_evt p' (asp_paramsC aid args) e' ->
    (asp_types G) ![ appr_id ] = Some (ev_arrow fwd attrs) ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd' attrs') ->
    fwd <> UNWRAP /\ (forall nv, fwd' <> WRAP nv) /\ fwd' <> UNWRAP ->
    typeof G p e (asp APPR) (asp_evt p (asp_paramsC appr_id args) e)
| tc_appr_split : forall p el er el' er' e,
    normalize_ev G e = split_evt el er ->
    typeof G p (left_evt e) (asp APPR) el' ->
    typeof G p (right_evt e) (asp APPR) er' ->
    typeof G p e (asp APPR) (split_evt el' er').

Inductive same_modulo_plc : EvidenceT -> EvidenceT -> Prop :=
| smp_mt : same_modulo_plc mt_evt mt_evt
| smp_nonce : forall n, same_modulo_plc (nonce_evt n) (nonce_evt n)
| smp_left : forall e1 e2,
    same_modulo_plc e1 e2 ->
    same_modulo_plc (left_evt e1) (left_evt e2)
| smp_right : forall e1 e2,
    same_modulo_plc e1 e2 ->
    same_modulo_plc (right_evt e1) (right_evt e2)
| smp_split : forall l1 r1 l2 r2,
    same_modulo_plc l1 l2 ->
    same_modulo_plc r1 r2 ->
    same_modulo_plc (split_evt l1 r1) (split_evt l2 r2)
| smp_asp : forall p1 p2 aid args1 args2 e1 e2,
    same_modulo_plc e1 e2 ->
    same_modulo_plc 
      (asp_evt p1 (asp_paramsC aid args1) e1) 
      (asp_evt p2 (asp_paramsC aid args2) e2).
Local Hint Constructors same_modulo_plc : smp.

Ltac2 Notation "smper" := (ff with (eauto with smp)).

Lemma same_modulo_plc_refl : forall e,
  same_modulo_plc e e.
Proof.
  induction e; try (destruct a); ff; smper.
Qed.
Local Hint Resolve same_modulo_plc_refl : smp.

Lemma same_modulo_plc_canon_ev : forall G e1 e2,
  same_modulo_plc e1 e2 ->
  same_modulo_plc (normalize_ev G e1) (normalize_ev G e2).
Proof.
  intros.
  induction H; smper.
  - normer; smper; invc IHsame_modulo_plc; smper.
  - normer; smper; invc IHsame_modulo_plc; smper.
  - normer; smper; invc IHsame_modulo_plc; smper.
  - invc IHsame_modulo_plc; norm;
    Control.enter (fun () => 
      repeat (match! goal with
      | [ h : _ = normalize_ev _ _ |- _ ] => 
        let hv := Control.hyp h in
        erewrite <- $hv
      end; smper)).
Qed.

Lemma same_modulo_plc_denotation_same : forall G e1 n,
  evt_stack_denotation G e1 n ->
  forall e2,
  same_modulo_plc e1 e2 ->
  evt_stack_denotation G e2 n.
Proof.
  intros G e1 n H.
  induction H; ff;
  Control.enter (fun () => 
    match! goal with
    | [ h : same_modulo_plc _ _ |- _ ] => invc $h; evter;
    Control.enter (fun () =>
      match! goal with
      | [ h' : same_modulo_plc _ _ ,
          hc : normalize_ev _ _ = _
          |- _ ] => 
        let h' := Control.hyp h' in
        let hn := fresh_hyp "Hn" in
        pp (same_modulo_plc_canon_ev G _ _ $h') as $hn;
        let hc := Control.hyp hc in
        erewrite $hc in *;
        invc $hn; evter
      end
    )
    end
  ).
Qed.

Lemma appr_canon_invariant : forall G p e1 e2 r,
  normalize_ev G e1 = normalize_ev G e2 ->
  typeof G p e1 (asp APPR) r ->
  exists r', typeof G p e2 (asp APPR) r'.
Proof.
  intros G p e1 e2 r Heq Htype.
  ltac1:( generalize dependent e2 ).
  (* We induct on the typing derivation of e1 *)
  prep_induction Htype.
  induction Htype; intros Heq e_target Hcanon_eq; ff.

  (* Case 1: tc_appr_mt *)
  - exists e_target.
    apply tc_appr_mt.
    ff.

  (* Case 2: tc_appr_nonce *)
  - exists (asp_evt p check_nonce_params e_target).
    eapply tc_appr_nonce; ff.

  (* Case 3: tc_appr_asp *)
  - exists (asp_evt p (asp_paramsC appr_id args) e_target).
    eapply tc_appr_asp_unwrap_wrap; ff.

  (* Case 3: tc_appr_asp *)
  - exists (asp_evt p (asp_paramsC appr_id args) e_target).
    eapply tc_appr_asp; ff.

  (* Case 4: tc_appr_split *)
  (* This is the hard case where your original proof got stuck *)
  - destruct (IHHtype1 eq_refl (left_evt e_target)) as [el'' Hl].
    + (* Proof that canon (left e) == canon (left e_target) *)
      (* We know canon e = split el er. 
         By def of normalize_ev, canon (left e) = el *)
      assert (Hnorm_l: normalize_ev G (left_evt e) = el) by normer.
      
      (* We know canon e_target = split el er (via Hcanon_eq).
         By def of normalize_ev, canon (left e_target) = el *)
      assert (Hnorm_target_l: normalize_ev G (left_evt e_target) = el) by normer.
      ff.
      
    + destruct (IHHtype2 eq_refl (right_evt e_target)) as [er'' Hr].
      * (* Proof that canon (right e) == canon (right e_target) *)
        assert (Hnorm_r: normalize_ev G (right_evt e) = er) by normer.
        
        assert (Hnorm_target_r: normalize_ev G (right_evt e_target) = er) by normer.
        ff.
      
      * (* Now we can construct the split evidence *)
        exists (split_evt el'' er'').
        eapply tc_appr_split.
        -- rewrite <- Hcanon_eq. ff.
        -- exact Hl.
        -- exact Hr.
Qed.

Lemma tc_left_split : forall G p el el' er,
  typeof G p el (asp APPR) el' ->
  exists e'', 
    typeof G p (left_evt (split_evt el er)) (asp APPR) e''.
Proof.
  intros G p el el' er Htype.
  eapply appr_canon_invariant in Htype; normer.
Qed.

Lemma tc_right_split : forall G p er er' el,
  typeof G p er (asp APPR) er' ->
  exists e'', 
    typeof G p (right_evt (split_evt el er)) (asp APPR) e''.
Proof.
  intros G p er er' el Htype.
  eapply appr_canon_invariant in Htype; normer.
Qed.

Lemma typeof_appr_place_irrel : forall G p e r, 
  typeof G p e (asp APPR) r -> 
  forall q, exists r', typeof G q e (asp APPR) r'.
Proof.
  intros G p e r H.
  prep_induction H.
  induction H; ff;
  try (eexists; eauto using typeof; fail).
  - (* tc_appr_asp *)
    invc H.
    * eexists; eauto using typeof.
    * eexists; eauto using typeof.
    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp_unwrap_wrap
      > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 ]; ff.

    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp_unwrap_wrap
      > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 ]; ff.

    * 
      edestruct (IHtypeof eq_refl q).
      assert (e' = split_evt el er) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp_unwrap_wrap 
      > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 ];
      ff.
  - (* tc_appr_asp *)
    invc H.
    * eexists; eauto using typeof.
    * eexists; eauto using typeof.
    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
        (* eapply canon_ev_canonical in H5; ff with l. *)
      }
      subst.
      eexists.
      eapply tc_appr_asp 
      > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 | ]; ff.

    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp 
      > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 | ]; ff.

    * 
      edestruct (IHtypeof eq_refl q).
      assert (e' = split_evt el er) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 | ];
      ff.
  - (* tc_appr_split *)
    destruct (IHtypeof1 eq_refl q);
    destruct (IHtypeof2 eq_refl q);
    eexists; eauto using typeof.
Qed.

Lemma typeof_place_irrel : forall G t e1 e1' p1,
  typeof G p1 e1 t e1' ->
  forall p2 e2,
    same_modulo_plc e1 e2 ->
    exists e2', typeof G p2 e2 t e2' /\ same_modulo_plc e1' e2'.
Proof.
  induction t; ff.
  - destruct a.
    * invc H.
    * invc H.
      + eexists.
        split.
        -- eapply tc_extend_in_none; 
          try (eapply same_modulo_plc_denotation_same); ff.
        -- smper.
      + eexists.
        split.
        -- eapply tc_extend_in_all;
          try (eapply same_modulo_plc_denotation_same); ff.
        -- smper.
      + eexists.
        split.
        -- eapply tc_in_all;
          try (eapply same_modulo_plc_denotation_same); ff;
          try (eauto using same_modulo_plc).
        -- smper.
    * invc H.
      eexists.
      split > [
        eapply tc_sig;
        try (eapply same_modulo_plc_denotation_same); ff
        | eauto using same_modulo_plc 
      ].
    * invc H.
      eexists.
      split > [
        eapply tc_hsh;
        try (eapply same_modulo_plc_denotation_same); ff
        | eauto using same_modulo_plc 
      ].
    * 
      prep_induction H.
      induction H; ff.
      + eexists; split > [ eapply tc_appr_mt | eauto using same_modulo_plc ].
        pp (same_modulo_plc_canon_ev G _ _ H0).
        erewrite H in *.
        invc H1.
        ff.
      + eexists; split > [ eapply tc_appr_nonce | eauto using same_modulo_plc ].
        -- pp (same_modulo_plc_canon_ev G _ _ H1).
          erewrite H in *.
          invc H2.
          ff.
        -- pp (same_modulo_plc_canon_ev G _ _ H1).
          erewrite H in *.
          invc H2.
          ff.
      + 
        pp (same_modulo_plc_canon_ev G _ _ H4).
        find_rewrite.
        invc H5.
        edestruct (IHtypeof p2 _ H7 eq_refl).
        eexists.
        split.
        ++ eapply tc_appr_asp_unwrap_wrap.
          -- ff.
          -- eauto.
          -- eapply H1.
          -- eapply H2.
          -- eapply H3.
        ++ eauto using same_modulo_plc.
      + 
        pp (same_modulo_plc_canon_ev G _ _ H4).
        find_rewrite.
        invc H5.
        edestruct (IHtypeof p2 _ H7 eq_refl).
        eexists.
        split.
        ++ eapply tc_appr_asp.
          -- ff.
          -- eauto.
          -- eapply H1.
          -- eapply H2.
          -- eapply H3.
          -- ff.
        ++ eauto using same_modulo_plc.
      + 
        pp (same_modulo_plc_canon_ev G _ _ H2).
        rewrite H in *.
        invc H3.
        edestruct (IHtypeof1 p2 (left_evt e2)) > [ | reflexivity | ff ].
        -- eauto using same_modulo_plc.
        -- 
          edestruct (IHtypeof2 p2 (right_evt e2)) > [ | reflexivity | ff ].
          ** eauto using same_modulo_plc.
          ** eexists.
          split.
          ++ eapply tc_appr_split.
            --- 
              rewrite <- H6.
              reflexivity.
            --- ff.
            --- ff.
          ++ eapply smp_split.
             --- ff.
             --- ff.
    * invc H.
      eexists.
      split > [
        eapply tc_enc;
        try (eapply same_modulo_plc_denotation_same); ff
        | eauto using same_modulo_plc 
      ].
  - invc H; ff.
    find_eapply_lem_hyp IHt; ff.
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
  - invc H; ff.
    pp (IHt1 _ _ _ H5 p2 _ H0).
    ff.
    pp (IHt2 _ _ _ H7 p2 _ Hand_r).
    ff.
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
  - invc H; ff.
    find_eapply_lem_hyp IHt1 > [ | eauto using same_modulo_plc ].
    find_eapply_lem_hyp IHt2 > [ | eauto using same_modulo_plc ].
    ff.
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
  - invc H; ff.
    find_eapply_lem_hyp IHt1 > [ | eauto using same_modulo_plc ].
    find_eapply_lem_hyp IHt2 > [ | eauto using same_modulo_plc ].
    ff.
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
Qed.

Theorem typeof_deterministic : forall G t p e e1 e2,
  typeof G p e t e1 ->
  typeof G p e t e2 ->
  e1 = e2.
Proof.
  induction t; try (destruct a); ff;
  try (Control.enter (fun () =>
    match! goal with
    | [ h1 : typeof _ _ _ _ _ , h2 : typeof _ _ _ _ _ |- _ ] =>
      invc $h1; invc $h2; ff
    end; 
    repeat (match! goal with
    | [ h1 : typeof _ _ _ ?_t1 _ , 
        h2 : typeof _ _ _ ?_t1 _ ,
        iht1 : context[ typeof _ _ _ ?_t1 _ -> _ ]
      |- _ ] =>
      (* printf "found %I %I %I" h1 h2 iht1; *)
      let iht1v := Control.hyp iht1 in
      let h2v := Control.hyp h2 in
      eapply $iht1v in $h1 as ? > [ | eapply $h2v ]; clear $h1 $h2 $iht1;
      ff
    end); fail
  )).
  prep_induction H.
  induction H; try congruence.
  - ff; invc H0; normer.
  - ff with u; invc H1; normer.
  - ff.
    invc H4; try (normer; fail).
  - ff.
    invc H4; try (normer; fail).
  - ff; invc H2; normer.
    find_eapply_lem_hyp IHtypeof1; ff.
    find_eapply_lem_hyp IHtypeof2; ff.
Qed.

Lemma evt_stack_denotation_transfer : forall G e1 e2 n,
  evt_stack_denotation G e1 n ->
  normalize_ev G e1 = normalize_ev G e2 ->
  evt_stack_denotation G e2 n.
Proof.
  intros.
  erewrite equiv_preserves_denotation_size.
  erewrite <- H0.
  erewrite <- equiv_preserves_denotation_size.
  eapply H.
Qed.

(* Helper Lemma: Typeof respects normalization equivalence *)
Lemma typeof_norm_proper : forall G p e1 e2 t e1',
  normalize_ev G e1 = normalize_ev G e2 ->
  typeof G p e1 t e1' ->
  exists e2', typeof G p e2 t e2' /\ normalize_ev G e1' = normalize_ev G e2'.
Proof.
  intros G p e1 e2 t e1' Heq Hty.
  ltac1:(generalize dependent e2).
  induction Hty; intros e_input Heq_input;
  try (
    eexists; split > [
      econstructor; ff with l; eapply evt_stack_denotation_transfer; ff
    | ff with u, (norm)
  ]; fail).
  
  (* Case: Operator Rules *)
  - (* tc_att *)
    edestruct IHHty as [e2' [Hty2 Heq2]]; eauto.
    eexists; split > [ eapply tc_att; eauto | assumption ].
    
  - (* tc_lseq - The Problem Child becomes easy *)
    edestruct IHHty1 as [e_mid' [Hty1' Heq_mid]]; eauto.
    edestruct IHHty2 as [e_final' [Hty2' Heq_final]]; eauto.
    eexists; split; ff; eapply tc_lseq; ff.

  - (* tc_bseq *)
    edestruct IHHty1 as [e1' [Hty1' Heq1]]; eauto.
    edestruct IHHty2 as [e2' [Hty2' Heq2]]; eauto.
    eexists; split.
    + eapply tc_bseq; ff.
    + normer.

  - (* tc_bpar *)
    edestruct IHHty1 as [e1' [Hty1' Heq1]]; eauto.
    edestruct IHHty2 as [e2' [Hty2' Heq2]]; eauto.
    eexists; split.
    + eapply tc_bpar; eauto.
    + normer.

  - (* tc_appr_asp *)
    eexists; split.
    + eapply tc_appr_asp > [ | | eapply H0 | | | ]; ff.
    + normer.

  - (* tc_appr_split *)
    edestruct (IHHty1 (left_evt e_input)).
    normer.
    edestruct (IHHty2 (right_evt e_input)).
    normer.

    eexists; split.
    + eapply tc_appr_split.
      * ff.
      * ff.
      * ff.
    + normer.
Qed.

Theorem typeof_canon_ev_can_type : forall G t p e e',
  typeof G p e t e' ->
  exists e'', typeof G p (normalize_ev G e) t e''.
Proof.
  intros.
  eapply (typeof_norm_proper G p e (normalize_ev G e)) in H.
  ff.
  symmetry.
  eapply normalize_ev_done.
  ff.
Qed.


Definition asp_supported (G : GlobalContext) aid : Prop :=
  match (asp_types G) ![ aid ] with
  | None => False
  | Some (ev_arrow (WRAP _) _) => 
    (* if unwrap, corresponding better be wrap *)
    match (asp_comps G) ![ aid ] with
    | None => False
    | Some appr_id =>
      match (asp_types G) ![ appr_id ] with
      | Some (ev_arrow (UNWRAP) _) => True
      | _ => False
      end
    end
  | Some (ev_arrow _ _) =>
    match (asp_comps G) ![ aid ] with
    | None => False
    | Some appr_id =>
      match (asp_types G) ![ appr_id ] with
      | Some (ev_arrow UNWRAP _) => False
      | Some (ev_arrow _ _) => True
      | _ => False
      end
    end
  end.

Inductive ContextSupportsAppr (G : GlobalContext) : EvidenceT -> Prop :=
| csa_mt : forall e,
  normalize_ev G e = mt_evt ->
  ContextSupportsAppr G e
| csa_nonce : forall e n nlt attrs,
  normalize_ev G e = nonce_evt n ->
  (asp_types G) ![ check_nonce_aspid ] = Some (ev_arrow (REPLACE (exist _ 1 nlt)) attrs) ->
  ContextSupportsAppr G e
| csa_left : forall e' l r,
    normalize_ev G e' = split_evt l r ->
    ContextSupportsAppr G l ->
    ContextSupportsAppr G (left_evt e')
| csa_right : forall e' l r,
    normalize_ev G e' = split_evt l r ->
    ContextSupportsAppr G r ->
    ContextSupportsAppr G (right_evt e')
| csa_split : forall e l r,
    normalize_ev G e = split_evt l r ->
    ContextSupportsAppr G l ->
    ContextSupportsAppr G r ->
    ContextSupportsAppr G e
| csa_asp_mt : forall p aid args e' fwd attrs,
    normalize_ev G e' = mt_evt ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    fwd <> UNWRAP ->
    asp_supported G aid ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_nonce : forall p aid args e' attrs'' n nlt fwd attrs,
    normalize_ev G e' = nonce_evt n ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    fwd <> UNWRAP ->
    asp_supported G aid ->
    (asp_types G) ![ check_nonce_aspid ] = Some (ev_arrow (REPLACE (exist _ 1 nlt)) attrs'') ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_split : forall p aid args e' l r fwd attrs,
    normalize_ev G e' = split_evt l r ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    fwd <> UNWRAP ->
    asp_supported G aid ->
    ContextSupportsAppr G l ->
    ContextSupportsAppr G r ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_asp_unwrap_wrap : 
    forall p p' aid aid' args args' n attrs attrs' e' e'',
    normalize_ev G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    (asp_types G) ![ aid  ] = Some (ev_arrow UNWRAP attrs) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP n) attrs') ->
    (asp_comps G) ![ aid' ] = Some aid ->
    ContextSupportsAppr G e'' ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_asp : forall p p' aid aid' args args' e' e'' fwd attrs fwd' attrs',
    normalize_ev G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    (asp_types G) ![ aid  ] = Some (ev_arrow fwd attrs) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow fwd' attrs') ->
    fwd <> UNWRAP ->
    asp_supported G aid ->
    ContextSupportsAppr G e' ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e').
Local Hint Constructors ContextSupportsAppr : csa.

(* 1. CSA Soundness: If CSA e, then CSA (norm e).
   This direction is usually easy because norm(e) is a "cleaner" version of e. *)
Lemma CSA_norm_sound : forall G e,
  ContextSupportsAppr G e ->
  ContextSupportsAppr G (normalize_ev G e).
Proof.
  intros G e H.
  induction H; try (normer; fail).
  - eapply csa_mt; normer.
  - normer; eapply csa_nonce; normer.
  
  - normer; eapply csa_split > [ normer | | ]; ff.

  - (* csa_asp_mt *)
    normer.
    eapply csa_asp_mt; normer.
  - (* csa_asp_nonce *)
    normer.
    eapply csa_asp_nonce; normer.
  - (* csa_asp_split *)
    normer.
    eapply csa_asp_split > [ normer | | | | | ]; ff.
  - normer;
    try (
      find_eapply_lem_hyp normalize_ev_done;
      eapply csa_asp_asp > [ normer | | | | | ]; ff;
      fail
    ).
(* 
    invc IHContextSupportsAppr; normer.
    * eapply csa_mt; normer.
    * eapply csa_nonce; normer.
    * eapply csa_split; normer. *)
Qed.

Lemma CSA_norm_complete : forall G e,
  ContextSupportsAppr G (normalize_ev G e) ->
  ContextSupportsAppr G e.
Proof.
  intros G e H.
  induction e using (normalize_ev_ind_custom G); eauto with csa.
  - normer; eapply csa_left; normer.
  - normer; find_eapply_lem_hyp normalize_ev_done; invc H; normer.

  - normer; eapply csa_right; normer.
  - normer; find_eapply_lem_hyp normalize_ev_done; invc H; normer.
  - normer.
    invc H; normer.
    erewrite normalize_ev_idempotent in *.
    (* ff with a. *)
    eapply csa_split > [ normer | | ]; ff.
  - normer.
    eapply csa_asp_asp_unwrap_wrap; normer.
  - normer;
    eapply normalize_ev_done in Heq as ?; invc H; try (normer; fail);
    ff with a; eauto with csa.
  - 
    normer.
    * invc H; normer; eapply csa_asp_mt; normer.
    * invc H; normer; eapply csa_asp_nonce; normer.
    * find_eapply_lem_hyp normalize_ev_done; invc H; normer.
    * find_eapply_lem_hyp normalize_ev_done; invc H; normer.
    * invc H; normer.
      eapply normalize_ev_done in Heq as ?.
      normer.
      eapply csa_asp_split; ff.
Qed.

Lemma CSA_norm_exact : forall G e,
  ContextSupportsAppr G e <-> ContextSupportsAppr G (normalize_ev G e).
Proof.
  split > [ eapply CSA_norm_sound | eapply CSA_norm_complete ].
Qed.

(* --- The Main Theorem --- *)
Theorem CSA_canon_invariant : forall G e1 e2,
  normalize_ev G e1 = normalize_ev G e2 ->
  ContextSupportsAppr G e1 ->
  ContextSupportsAppr G e2.
Proof.
  intros.
  rewrite CSA_norm_exact in *.
  ff.
Qed.

(* 

Equations? context_supports_appr_type (G : GlobalContext) (e : EvidenceT) 
    : Prop by wf (EvidenceT_depth e) :=
  context_supports_appr_type G mt_evt := True;
  context_supports_appr_type G (nonce_evt n) := 
    (exists attrs nlt, (asp_types G) ![ check_nonce_aspid ] = Some (ev_arrow (REPLACE (exist _ 1 nlt)) attrs))
    ;
  context_supports_appr_type G (left_evt e') := 
    match normalize_ev G e' as cer return normalize_ev G e' = cer -> _ with
    | split_evt l r => fun Hcer => context_supports_appr_type G l
    | _ => fun _ => False
    end eq_refl;
  context_supports_appr_type G (right_evt e') :=
    match normalize_ev G e' as cer return normalize_ev G e' = cer -> _ with
    | split_evt l r => fun Hcer => context_supports_appr_type G r
    | _ => fun _ => False
    end eq_refl;
  (* context_supports_appr_type G (left_evt e') := False;
  context_supports_appr_type G (right_evt e') := False; *)
  context_supports_appr_type G (split_evt l r) :=
    context_supports_appr_type G l /\ context_supports_appr_type G r;
  context_supports_appr_type G (asp_evt p (asp_paramsC aid args) e') :=
    match normalize_ev G e' as cer return normalize_ev G e' = cer -> _ with
    | mt_evt => fun Hcer => asp_supported G aid
        (* (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
        /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id
          /\ (exists fwd attrs, (asp_types G) ![ appr_id ] = Some (ev_arrow fwd attrs))) *)
    | nonce_evt n => fun Hcer => asp_supported G aid
        (* (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs))
        (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
        /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id
          /\ (exists fwd attrs, (asp_types G) ![ appr_id ] = Some (ev_arrow fwd attrs)))
          *)
        /\ (exists attrs nlt, (asp_types G) ![ check_nonce_aspid ] = Some (ev_arrow (REPLACE (exist _ 1 nlt)) attrs))
    | left_evt e'' => fun Hcer => False
    | right_evt e'' => fun Hcer => False
    | split_evt l r => 
      fun Hcer =>
        asp_supported G aid
        /\ context_supports_appr_type G l
        /\ context_supports_appr_type G r
    | asp_evt p' (asp_paramsC aid' args') e'' =>
      fun Hcer =>
        match (asp_types G) ![ aid  ] with
        | None => False
        | Some (ev_arrow UNWRAP attrs) =>
          (* if outer is UNWRAP, inner better be a WRAP *)
          match (asp_types G) ![ aid' ], (asp_comps G) ![ aid' ] with
          | Some (ev_arrow (WRAP _) attrs'), Some appr_id =>
            if dec_eq appr_id aid then context_supports_appr_type G e'' else False
          | _, _ => False
          end
        (* Always need types! *)
        | Some (ev_arrow _ _) =>
          match (asp_types G) ![ aid' ] with
          | None => False
          | Some (ev_arrow (WRAP _) _) => False
          | Some (ev_arrow _ _) =>
            asp_supported G aid
            /\ context_supports_appr_type G e'
          end
        end
    end eq_refl.
- eapply canon_ev_canonical in Hcer; ff with l.
- eapply canon_ev_canonical in Hcer; ff with l.
- eapply canon_ev_canonical in Hcer; ff with l.
- eapply canon_ev_canonical in Hcer; ff with l.
- eapply canon_ev_canonical in Hcer; ff with l.
- ff with l.
- ff with l.
Defined.

Theorem ContextSupportsAppr_impl_context_supports_appr_type : forall G e,
  ContextSupportsAppr G e <-> context_supports_appr_type G e.
Proof.
  split; intros.
  - intros. 

    induction e using (normalize_ev_ind_custom G); 
    try (
      invc H; normer;
      ltac1:( simp context_supports_appr_type in * ); 
      normer;
      fail
    ).
    * invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer).
    * invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer).
    * invc H; normer;
      repeat (find_eapply_lem_hyp CSA_norm_complete; ff);
      repeat (ltac1:( simp context_supports_appr_type in * ); normer).
    * 
      invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer).
      eapply IHe1.
      clear IHe1.
      erewrite CSA_norm_exact in *.
      ff.
      invc H8; normer; eauto with csa.
      + eapply csa_nonce; normer.
      + eapply csa_split > [ norm; ff | | ];
        erewrite <- CSA_norm_exact; ff.
      + 
        rewrite <- H2.
        erewrite <- CSA_norm_exact; ff.

    * 
      erewrite CSA_norm_exact in H.
      norm.
      ff.
      + repeat (ltac1:( simp context_supports_appr_type in * ); normer).

      invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer);
      ff with a.


    * invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer);
      ff with a.

      ltac1:( simp context_supports_appr_type in * ).
      find_rewrite.
      ff.

      invc H; normer;
      repeat (ltac1:( simp context_supports_appr_type in * ); normer).
      + 
        erewrite CSA_norm_exact in H8.
        ff.
        invc H8; normer;
        unfold asp_supported in *; ff.
    
    invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer).
      + 
        eapply IHe1 in H11 as ?.
        eapply CSA_norm_sound in H11.
        ff.
        eapply normalize_ev_done in H6 as ?.

        ff.
        ltac1:( simp context_supports_appr_type in * ).
        ff.

        unfold asp_supported in *; ff.

        invc H11; ff; unfold asp_supported in *; ff.
      + 
        eapply IHe1 in H11 as ?.
        eapply CSA_norm_sound in H11.
        ff.
        eapply normalize_ev_done in H6 as ?.

        ff.
        ltac1:( simp context_supports_appr_type in * ).
        ff.
        invc H11; ff; unfold asp_supported in *; ff.
      + 
        eapply IHe1 in H11 as ?.
        eapply CSA_norm_sound in H11.
        ff.
        eapply normalize_ev_done in H6 as ?.

        ff.
        ltac1:( simp context_supports_appr_type in * ).
        ff.
        invc H11; ff; unfold asp_supported in *; ff.
    * invc H; normer;
      try (assert (ContextSupportsAppr G (split_evt l r)) by (
        eapply csa_split > [ normer | | ]; eapply CSA_norm_sound; ff));
      repeat (ltac1:( simp context_supports_appr_type in * ); normer);
      ff with a.
  - 
    induction e using (normalize_ev_ind_custom G); eauto with csa;
    ltac1:( simp context_supports_appr_type in * );
    ff with (eauto with csa);
    try (eapply csa_asp_asp; ff with (eauto with csa); fail).
    * eapply csa_nonce; normer.
    * 
      ff with a.
      eapply csa_split > [ normer | | ];
      eapply CSA_norm_sound; ff.
    * 

    assert (context_supports_appr_type G (split_evt e3 e4)). {
      ltac1:( simp context_supports_appr_type in * ).
      ff.
    }
    ff with a.
    invc H; normer.
    eapply csa_asp_split; ff;
    eapply CSA_norm_complete; ff.
Qed.
Local Hint Rewrite <- ContextSupportsAppr_impl_context_supports_appr_type : csa.

Fixpoint context_supports_appr (G : GlobalContext) p e t : Prop :=
  match t with
  | asp APPR => context_supports_appr_type G e
  | asp (ASPC (asp_paramsC aid args)) =>
      context_supports_appr_type G e
      /\ (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
      /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id
        /\ (exists fwd attrs, (asp_types G) ![ appr_id ] = Some (ev_arrow fwd attrs)))
  | asp SIG => 
      context_supports_appr_type G e
      /\ (exists sig_appr_id, (asp_comps G) ![ sig_aspid ] = Some sig_appr_id
        /\ exists fwd attrs, (asp_types G) ![ sig_appr_id ] = Some (ev_arrow fwd attrs))
  | asp HSH => 
      context_supports_appr_type G e
      /\ (exists hsh_appr_id, (asp_comps G) ![ hsh_aspid ] = Some hsh_appr_id
        /\ exists fwd attrs, (asp_types G) ![ hsh_appr_id ] = Some (ev_arrow fwd attrs))
  | asp (ENC p') => 
      context_supports_appr_type G e
      /\ (exists enc_appr_id, (asp_comps G) ![ enc_aspid ] = Some enc_appr_id
        /\ exists fwd attrs, (asp_types G) ![ enc_appr_id ] = Some (ev_arrow fwd attrs))
  | asp NULL => 
      context_supports_appr_type G e 
      /\ True (* should not be used... maybe ever *)
  | att p' t' => context_supports_appr G p' e t'
  | lseq t1 t2 => 
    context_supports_appr_type G e /\ 
    context_supports_appr G p e t1 /\ 
    exists et', 
      typeof G p e t1 et' /\ 
      context_supports_appr G p et' t2
  | bseq t1 t2 => 
    context_supports_appr_type G e /\ 
    context_supports_appr G p e t1 
    /\ context_supports_appr G p e t2
  | bpar t1 t2 => 
    context_supports_appr_type G e /\ 
      context_supports_appr G p e t1 
    /\ context_supports_appr G p e t2
  end.
*)

Lemma CSA_appraisal_sound : forall G e,
  ContextSupportsAppr G e ->
  forall p,
    exists e'', typeof G p e (asp APPR) e''.
Proof.
  intros G e Hcsat.
  induction Hcsat; ff with (eauto using typeof).
  (* - eexists; eapply tc_appr_nonce; normer. *)
  - edestruct (IHHcsat p).
    eapply (appr_canon_invariant G p _ _ _ _ H0).
    Unshelve.
    normer; find_eapply_lem_hyp normalize_ev_done; normer.

  - edestruct (IHHcsat p).
    eapply (appr_canon_invariant G p _ _ _ _ H0).
    Unshelve.
    normer; find_eapply_lem_hyp normalize_ev_done; normer.

  - edestruct (IHHcsat1 p); find_eapply_lem_hyp tc_left_split; ff;
    edestruct (IHHcsat2 p); find_eapply_lem_hyp tc_right_split; ff.
    assert (normalize_ev G (left_evt (split_evt l r)) = normalize_ev G (left_evt e)). {
      ff.
      norm.
      ff.
      eapply normalize_ev_done in H.
      normer.
    }
    pp (appr_canon_invariant G p _ _ x0 H0 Hex).
    assert (normalize_ev G (right_evt (split_evt l r)) = normalize_ev G (right_evt e)). {
      ff.
      norm.
      ff.
      eapply normalize_ev_done in Heq.
      normer.
    }
    pp (appr_canon_invariant G p _ _ _ H2 Hex0).
    ff.
    eexists; eapply tc_appr_split; ff.
  - 
    unfold asp_supported in *; ff;
    try (eexists; eapply tc_appr_asp; normer; eauto using typeof; fail).

    eexists; eapply tc_appr_asp_unwrap_wrap; normer; eauto using typeof.

  - 
    unfold asp_supported in *; ff;
    try (
      eexists; eapply tc_appr_asp > [ | normer | eapply Heq1 | ff | ff | ff ];
      eapply tc_appr_nonce; normer; fail).

    eexists; eapply tc_appr_asp_unwrap_wrap; normer; eauto using typeof.
    eapply tc_appr_nonce; normer.

  - 
    edestruct (IHHcsat1 p0); find_eapply_lem_hyp tc_left_split; ff.
    edestruct (IHHcsat2 p0); find_eapply_lem_hyp tc_right_split; ff.
    unfold asp_supported in *; ff;
    try (
      eexists; eapply tc_appr_asp > [ | normer | | | | ]; ff;
      eapply tc_appr_split; ff;
      eapply normalize_ev_done; ff;
      fail
    ).

    eexists; eapply tc_appr_asp_unwrap_wrap > [ | normer | | | ]; ff;
    eapply tc_appr_split; ff;
    eapply normalize_ev_done; ff.
  - 
    edestruct (IHHcsat p0); ff; clear IHHcsat.

    assert (normalize_ev G e'' = normalize_ev G (asp_evt p (asp_paramsC aid args) e')) as Heq. {
      normer.
      eapply normalize_ev_done in H as ?.
      normer.
    }


    pp (appr_canon_invariant _ _ _ _ _ Heq H3).
    ff.
  - edestruct IHHcsat as [e_inner_res Htyp_inner].

    pose proof (normalize_ev_done G _ _ H) as Hnorm_fixed.
    eapply appr_canon_invariant in Htyp_inner > [| rewrite H; rewrite Hnorm_fixed; reflexivity].
    destruct Htyp_inner as [e_inner_norm_res Htyp_inner_norm].

    destruct fwd.

    * unfold asp_supported in H3;
      rewrite H0 in H3;
      destruct ((asp_comps G) ![ aid ]) as [appr_id|] eqn:Hcomp > [| ff];
      destruct ((asp_types G) ![ appr_id ]) as [[fwd_appr attrs_appr]|] eqn:Htype_appr > [| ff];
      destruct fwd_appr; try (ff; fail); 
      eexists;
      eapply tc_appr_asp >
      [ exact Htyp_inner_norm | norm; ff | ff | ff | ff | split; ff ].

    (* CASE 1: fwd = WRAP n *)
    * unfold asp_supported in H3.
      rewrite H0 in H3.
      destruct ((asp_comps G) ![ aid ]) as [appr_id|] eqn:Hcomp > [ | ff ].
      destruct ((asp_types G) ![ appr_id ]) as [[fwd_appr attrs_appr]|] eqn:Htype_appr
      > [| ff].
      destruct fwd_appr; try (ff; fail).
      (* The appraiser is UNWRAP, so we use the unwrap_wrap rule *)
      eexists.
      eapply tc_appr_asp_unwrap_wrap.
      + exact Htyp_inner_norm.
      + norm; ff.
      + exact Htype_appr. 
      + exact Hcomp.
      + exact H0. 

    * ff.

    * unfold asp_supported in H3;
      rewrite H0 in H3;
      destruct ((asp_comps G) ![ aid ]) as [appr_id|] eqn:Hcomp > [| ff];
      destruct ((asp_types G) ![ appr_id ]) as [[fwd_appr attrs_appr]|] eqn:Htype_appr > [| ff];
      destruct fwd_appr; try (ff; fail); 
      eexists;
      eapply tc_appr_asp >
      [ exact Htyp_inner_norm
      | norm; ff
      | exact Htype_appr
      | exact Hcomp
      | exact H0 (* aid type *)
      | split; ff
      ].
  Unshelve.
  all: try (eapply (exist _ 1 (Nat.lt_0_1))).
Qed.

(** Provenance Preserving *)
(* 
The provenance of evidence "e" is said to be preserved if future
operations or typechecking will always allow the recovery of "e" from
the resulting evidence type.

It is essentially just a subterm relation, but we define it here
*)

Inductive provenance (G : GlobalContext) : EvidenceT -> EvidenceT -> Prop :=
  | prov_refl : forall e, provenance G e e
  | prov_left_inj : forall e e',
      provenance G e e' ->
      provenance G (left_evt e) (left_evt e')
  | prov_left : forall e e',
      provenance G e e' ->
      provenance G e (left_evt e')
  | prov_right_inj : forall e e',
      provenance G e e' ->
      provenance G (right_evt e) (right_evt e')
  | prov_right : forall e e',
      provenance G e e' ->
      provenance G e (right_evt e')
  | prov_split_inj : forall l r el er,
      provenance G el l ->
      provenance G er r ->
      provenance G (split_evt el er) (split_evt l r)
  | prov_split_l : forall e l r,
      provenance G e l ->
      provenance G e (split_evt l r)
  | prov_split_r : forall e l r,
      provenance G e r ->
      provenance G e (split_evt l r)
  | prov_asp_inj : forall e p aid args e',
      provenance G e e' ->
      provenance G (asp_evt p (asp_paramsC aid args) e) (asp_evt p (asp_paramsC aid args) e')
  | prov_asp : forall e p aid args e',
      provenance G e e' ->
      provenance G e (asp_evt p (asp_paramsC aid args) e').
Local Hint Constructors provenance : prov.

Ltac2 Notation "prover" := (ff with (eauto with prov)).

Lemma provenance_trans : forall G e1 e2 e3,
  provenance G e1 e2 ->
  provenance G e2 e3 ->
  provenance G e1 e3.
Proof.
  intros.
  prep_induction H0.
  induction H0; ff; prover;
  invc H; prover.
Qed.
Local Hint Resolve provenance_trans : prov.

Example normalize_provenance :
  provenance (Build_GlobalContext _ [] []) (split_evt (nonce_evt 1) (nonce_evt 3)) 
    (split_evt (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) (nonce_evt 3)).
Proof.
  eauto with prov.
Qed.

Lemma normalize_ev_provenance : forall G e,
  provenance G (normalize_ev G e) e.
Proof.
  intros.
  induction e; norm; prover.

  destruct a; norm; prover.
Qed.

Theorem provenance_monotonic : forall G e e',
  provenance G e e' ->
  EvidenceT_depth e <= EvidenceT_depth e'.
Proof.
  intros.
  induction H; ff with l.
Qed.

Theorem provenance_antisym : forall G e e',
  provenance G e e' ->
  provenance G e' e ->
  e = e'.
Proof.
  intros.
  prep_induction H.
  induction H; ff;
  try (invc H0; ff with a;
    repeat (find_eapply_lem_hyp provenance_monotonic); ff with l; fail).
  invc H1; ff with a;
  repeat (find_eapply_lem_hyp provenance_monotonic); ff with l.
Qed.

Theorem typecheck_preserves_provenance : forall G t p e e',
  typeof G p e t e' ->
  provenance G e e'.
Proof.
  induction t; ff.
  - destruct a.
    * invc H.
    * invc H; eapply prov_asp; prover.
    * invc H; eapply prov_asp; prover.
    * invc H; eapply prov_asp; prover.
    * prep_induction H.
      induction H; try congruence; prover.
      eapply prov_asp; prover.
    * invc H; eapply prov_asp; prover.
  - invc H. ff.
  - invc H; ff with a;
    find_eapply_lem_hyp provenance_trans; ff.
  - invc H; ff with a; eauto using provenance.
  - invc H; ff with a; eauto using provenance.
Qed.

(*
Lemma csa_asp_step : forall G p e a args fwd attrs, 
  ContextSupportsAppr G e ->
  asp_supported G a ->
  fwd <> UNWRAP ->
  (asp_types G) ![ a ] = Some (ev_arrow fwd attrs) ->
  ContextSupportsAppr G (asp_evt p (asp_paramsC a args) e).
Proof.
  intros.
  erewrite CSA_norm_exact in *.
  norm.
  ff with (eauto with csa).
  - invc H; normer.
    eapply csa_asp_nonce; normer.
  - 
    invc H.
    + 
    eapply csa_asp_asp.
    * eapply normalize_ev_done in Heq as ?.
      ff.
    * ff.
    * admit.
    * admit.
    * 

  intros.
  prep_induction H.
  induction H; ff with (eauto with csa).
  - 




  intros.
  generalizeEverythingElse e.
  intros G.
  
  (* The Key Strategy: Destruct the normalization of e *)
  induction e using (normalize_ev_ind_custom G); intros.

  (* destruct (normalize_ev G e) eqn:Hnorm. *)
  
  - (* Case: mt_evt *)
    eapply csa_asp_mt; eauto.

  - (* Case: nonce_evt *)
    eapply CSA_norm_sound in Hcsa as ?.
    normer.
    invc H; normer.
    eapply csa_asp_nonce; eauto.
    normer.
  
  - 
    eapply CSA_norm_sound in Hcsa as ?.
    normer.
    ff with a.
    eapply CSA_norm_complete.
    normer.

  - 
    eapply CSA_norm_sound in Hcsa as ?.
    normer; 
    try ( find_eapply_lem_hyp normalize_ev_done; invc H0; normer; fail).

  - eapply CSA_norm_sound in Hcsa as ?.
    normer; 
    ff with a.
    eapply CSA_norm_complete.
    normer.
  - 
    eapply CSA_norm_sound in Hcsa as ?.
    normer; 
    try ( find_eapply_lem_hyp normalize_ev_done; invc H0; normer; fail).

  - (* true split *)
    invc Hcsa; normer.
    eapply csa_asp_split > [ normer | | | | | ]; ff.

  - (* Case: asp_evt *)
    normer.
    eapply CSA_norm_sound in Hcsa as ?.
    norm.
    ff with a.
    eapply CSA_norm_complete.
    norm.
    ff.

  - 
    eapply csa_asp_asp; normer.

  - eapply csa_asp_asp; normer.
Qed. *)

(* Major Theorem: Appraisability *)
Theorem well_typed_appraisable : forall G e p,
  ContextSupportsAppr G e ->
  exists e'', typeof G p e (asp APPR) e''.
Proof.
  intros.
  eapply CSA_appraisal_sound.
  ff.
Qed.

Print Assumptions well_typed_appraisable.

(* This justifies that the type system enforces the non-commutativity of evidence *)
Theorem evidence_non_commutative : forall p,
  (* NOTE: This could probably be strengthed, but it is at least good evidence *)
  exists G e t1 t2 e1 e2,
    typeof G p e (lseq t1 t2) e1 /\
    typeof G p e (lseq t2 t1) e2 /\
    e1 <> e2.
Proof.
  exists (Build_GlobalContext _ [
    (sig_aspid, ev_arrow (EXTEND (exist _ 1 Nat.lt_0_1) InAll) [])
    ; (hsh_aspid, ev_arrow (REPLACE (exist _ 1 Nat.lt_0_1)) [])
  ] []), (nonce_evt 1), (asp HSH), (asp SIG).
  repeat eexists.
  - repeat (econstructor; ff).
  - econstructor.
    * econstructor.
      + econstructor.
      + econstructor.
      + ff.
    * 
      (* econstructor. *)
      eapply tc_hsh.
      + eapply interp_asp_extend; ff.
        econstructor.
      + ff with l.
      + ff with l.
  - ff.
Qed.

Theorem CSA_appraisal_complete : forall G p e e',
  typeof G p e (asp APPR) e' ->
  ContextSupportsAppr G e.
Proof.
  intros G p e e' Htyp.
  remember (asp APPR) as t.
  induction Htyp; try (discriminate Heqt).

  -- eapply csa_mt. assumption.
  -- eapply csa_nonce; eassumption.
  -- apply CSA_norm_exact.

    rewrite H.

    (* 3. We must inspect the inner evidence e' to pick the right CSA rule.
          Note: 'e' is the outer WRAP evidence. 'e'' is what is inside it. *)
    destruct (normalize_ev G e') eqn:Heq_norm_inner.

    (* Case A: Inner is MT. Use csa_asp_mt *)
    - eapply csa_asp_mt.
      + exact Heq_norm_inner.
      + (* Show asp_supported for the outer WRAP *)
        unfold asp_supported. ff.
      + (* Show outer is NOT UNWRAP *)
        destruct nv; discriminate. (* WRAP <> UNWRAP *)
      + unfold asp_supported; ff.

    (* Case B: Inner is Nonce. Use csa_asp_nonce *)
    - 
      rewrite CSA_norm_exact in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp eq_refl); normer.
      eapply csa_asp_nonce.
      + exact Heq_norm_inner.
      + (* Outer is NOT UNWRAP *)
        ff.
      + ff.
      + (* asp_supported *)
        unfold asp_supported; ff.
      + (* Validity of checking nonce *)
        (* We need to extract the check_nonce property from CSA e' *)
        ff.

    (* Case D: Inner is ASP. Use csa_asp_asp *)
    - destruct a.
      rewrite CSA_norm_exact in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp eq_refl); normer;
      eapply csa_asp_asp > [ exact Heq_norm_inner | ff | ff | ff | unfold asp_supported; ff | rewrite CSA_norm_exact; ff ].
    - invc Htyp; normer.
    - invc Htyp; normer.

    (* Case C: Inner is Split. Use csa_asp_split *)
    - 
      pp (IHHtyp eq_refl).
      erewrite CSA_norm_exact in H3.
      ff.
      invc H3; normer.
      eapply csa_asp_split > [ exact Heq_norm_inner | ff | ff | unfold asp_supported; ff | | ];
      erewrite CSA_norm_exact; ff.

  -- apply CSA_norm_exact.

    rewrite H.

    (* 3. We must inspect the inner evidence e' to pick the right CSA rule.
          Note: 'e' is the outer WRAP evidence. 'e'' is what is inside it. *)
    destruct (normalize_ev G e') eqn:Heq_norm_inner.

    (* Case A: Inner is MT. Use csa_asp_mt *)
    - eapply csa_asp_mt; ff.
      unfold asp_supported; ff.

    (* Case B: Inner is Nonce. Use csa_asp_nonce *)
    - 
      rewrite CSA_norm_exact in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp eq_refl); normer.
      eapply csa_asp_nonce.
      + exact Heq_norm_inner.
      + (* Outer is NOT UNWRAP *)
        ff.
      + ff.
      + (* asp_supported *)
        unfold asp_supported; ff.
      + (* Validity of checking nonce *)
        (* We need to extract the check_nonce property from CSA e' *)
        ff.

    (* Case D: Inner is ASP. Use csa_asp_asp *)
    - destruct a.
      rewrite CSA_norm_exact in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp eq_refl); normer;
      eapply csa_asp_asp > [ exact Heq_norm_inner | ff | ff | ff | unfold asp_supported; ff with (congruence) | rewrite CSA_norm_exact; ff ].
    - invc Htyp; normer.
    - invc Htyp; normer.

    (* Case C: Inner is Split. Use csa_asp_split *)
    - 
      pp (IHHtyp eq_refl).
      erewrite CSA_norm_exact in H4.
      ff.
      invc H4; normer.
      eapply csa_asp_split > [ exact Heq_norm_inner | ff | ff | unfold asp_supported; ff | | ];
      erewrite CSA_norm_exact; ff.
  -- 
      pp (IHHtyp1 eq_refl).
      pp (IHHtyp2 eq_refl).
      erewrite CSA_norm_exact in *.
      norm.
      ff.
      eapply csa_split > [ norm; ff | | ]; 
      erewrite <- CSA_norm_exact; ff.
Qed.

Theorem CSA_appraisal_exact : forall G p e,
  (exists e', typeof G p e (asp APPR) e') <-> ContextSupportsAppr G e.
Proof.
  pp CSA_appraisal_complete.
  pp CSA_appraisal_sound.
  split; ff.
Qed.
