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

Theorem normalize_ev_rect_custom (G : GlobalContext) (P : EvidenceT -> Type)
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
  eapply well_founded_induction_type; eauto.
Qed.

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

Lemma evt_stack_denotation_deterministic : forall G e n1 n2,
  evt_stack_denotation G e n1 ->
  evt_stack_denotation G e n2 ->
  n1 = n2.
Proof.
  intros.
  prep_induction H.
  induction H; ff.
  - invc H0; ff.
  - invc H0; ff.
  - invc H1; ff.
  - invc H1; ff.
  - invc H1; ff.
  - invc H1; ff.
  - invc H1; ff.
  - invc H1; ff.
  - invc H4; ff.
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

Definition evt_stack_denotation_size (G : GlobalContext) (e : EvidenceT) 
    : { n | evt_stack_denotation G e n } + { forall n, ~ evt_stack_denotation G e n }.
Proof.
  induction e using (normalize_ev_rect_custom G).
  - ref (inleft (exist _ 0 (interp_mt _))).
  - ref (inleft (exist _ 1 (interp_nonce _ _))).
  - destruct IHe1 as [[n1 Hn1] | Hn1].
    + left; exists n1; evter.
    + right; intros n HC.
      eapply Hn1.
      erewrite equiv_preserves_denotation_size in HC.
      normer.
  - destruct IHe as [[n1 Hn1] | Hn1];
    right; intros n HC; invc HC; ff.
  - destruct IHe1 as [[n1 Hn1] | Hn1].
    + left; exists n1; evter.
    + right; intros n HC.
      eapply Hn1.
      erewrite equiv_preserves_denotation_size in HC.
      normer.
  - destruct IHe as [[n1 Hn1] | Hn1];
    right; intros n HC; invc HC; ff.
  - ff; try (Control.enter (fun () => 
      right;
      intros n HC;
      invc HC;
      try (eapply Hsumor_r; ff)
    ); fail).
    destruct Hsumor_l0 as [n1 Hn1];
    destruct Hsumor_l as [n2 Hn2].
    left; eexists; evter.
  - ff; try (Control.enter (fun () => 
      right;
      intros n HC;
      invc HC;
      try (eapply Hsumor_r; ff)
    ); fail).
    destruct Hsumor_l as [n1 Hn1].
    left; eexists; evter.
  - destruct IHe1;
    try (Control.enter (fun () => 
      right;
      intros ? HC;
      invc HC; ff;
      unfold not in *;
      ff
    ); fail).

    ff; destruct s as [n1 Hn1];
    Control.enter (fun () => repeat (match! goal with
    | [ n : pos_nat |- _ ] => 
      let n := Control.hyp n in
      destruct $n
    end));
    try (left; eexists; evter; fail);
    try (Control.enter (fun () => 
      right;
      intros ? HC;
      invc HC; ff;
      unfold not in *;
      ff
    ); fail).
  - destruct IHe1;
    try (Control.enter (fun () => 
      right; intros ? HC; invc HC;
      eapply n; erewrite <- equiv_preserves_denotation_size; ff
    ); fail).

    ff; destruct s as [n1 Hn1];
    Control.enter (fun () => repeat (match! goal with
    | [ n : pos_nat |- _ ] => 
      let n := Control.hyp n in
      destruct $n
    end)).

    destruct ((asp_types G) ![ aid ]) eqn:Ht;
    try (Control.enter (fun () => 
      right; intros ? HC; invc HC; ff
    ); fail);
    destruct e, e;
    try (Control.enter (fun () => 
      right; intros ? HC; invc HC; ff
    ); fail);
    erewrite <- equiv_preserves_denotation_size in * |-;
    Control.enter (fun () => repeat (match! goal with
    | [ n : pos_nat |- _ ] => 
      let n := Control.hyp n in
      destruct $n
    end));
    try (left; eexists; evter; fail).
    Unshelve.
    all: exact 0.
Qed.

(** Typechecking 

Here we actually introduce and utilize the typechecking rules
*)

Inductive typeof (G : GlobalContext) 
    : Plc -> EvidenceT -> Term -> EvidenceT -> Type :=
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
| tc_extend_in_all : forall p e aid args attrs n n_ext nlt,
    evt_stack_denotation G e n ->
    1 <= n -> (* cannot have empty evidence as input *)
    (asp_types G) ![ aid ] 
      = Some (ev_arrow (EXTEND (exist _ n_ext nlt) InAll) attrs) ->
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

Inductive same_modulo_plc : EvidenceT -> EvidenceT -> Type :=
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
  intros G e1 e2 H.
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
  { r' & typeof G p e2 (asp APPR) r' }.
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
  { e'' & typeof G p (left_evt (split_evt el er)) (asp APPR) e'' }.
Proof.
  intros G p el el' er Htype.
  eapply appr_canon_invariant in Htype; normer.
Qed.

Lemma tc_right_split : forall G p er er' el,
  typeof G p er (asp APPR) er' ->
  { e'' & typeof G p (right_evt (split_evt el er)) (asp APPR) e'' }.
Proof.
  intros G p er er' el Htype.
  eapply appr_canon_invariant in Htype; normer.
Qed.

Lemma typeof_appr_place_irrel : forall G p e r, 
  typeof G p e (asp APPR) r -> 
  forall q, { r' & typeof G q e (asp APPR) r' }.
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
        eapply normalize_ev_done in e0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp_unwrap_wrap
      > [ | eapply e0 | eapply e1 | eapply e2 | eapply e3 ]; ff.

    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in e0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp_unwrap_wrap
      > [ | eapply e0 | eapply e1 | eapply e2 | eapply e3 ]; ff.

    * 
      edestruct (IHtypeof eq_refl q).
      assert (e' = split_evt el er) as Heq.
      {
        eapply normalize_ev_done in e0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp_unwrap_wrap 
      > [ | eapply e0 | eapply e1 | eapply e2 | eapply e3 ];
      ff.
  - (* tc_appr_asp *)
    invc H.
    * eexists; eauto using typeof.
    * eexists; eauto using typeof.
    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in e0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
        (* eapply canon_ev_canonical in H5; ff with l. *)
      }
      subst.
      eexists.
      eapply tc_appr_asp 
      > [ | eapply e0 | eapply e1 | eapply e2 | eapply e3 | ]; ff.

    *
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in e0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp 
      > [ | eapply e0 | eapply e1 | eapply e2 | eapply e3 | ]; ff.

    * 
      edestruct (IHtypeof eq_refl q).
      assert (e' = split_evt el er) as Heq.
      {
        eapply normalize_ev_done in e0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
      }
      subst.
      eexists.
      eapply tc_appr_asp > [ | eapply e0 | eapply e1 | eapply e2 | eapply e3 | ];
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
    { e2' & ((typeof G p2 e2 t e2') * same_modulo_plc e1' e2')%type }.
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
        erewrite e0 in *.
        invc X.
        ff.
      + eexists; split > [ eapply tc_appr_nonce | eauto using same_modulo_plc ].
        -- pp (same_modulo_plc_canon_ev G _ _ H0).
          erewrite e0 in *.
          invc X; ff.
        -- pp (same_modulo_plc_canon_ev G _ _ H0).
          erewrite e1 in *.
          invc X; ff.
      + 
        pp (same_modulo_plc_canon_ev G _ _ H0).
        find_rewrite.
        invc X.
        edestruct (IHtypeof p2 _ X0 eq_refl).
        eexists.
        split.
        ++ eapply tc_appr_asp_unwrap_wrap.
          -- destruct p1; ff.
          -- eauto.
          -- eapply e1.
          -- eapply e2.
          -- eapply e3.
        ++ eauto using same_modulo_plc.
      + 
        pp (same_modulo_plc_canon_ev G _ _ H0).
        find_rewrite.
        invc X.
        edestruct (IHtypeof p2 _ X0 eq_refl).
        eexists.
        split.
        ++ eapply tc_appr_asp.
          -- destruct p1; ff.
          -- eauto.
          -- eapply e1.
          -- eapply e2.
          -- eapply e3.
          -- ff.
        ++ eauto using same_modulo_plc.
      + 
        pp (same_modulo_plc_canon_ev G _ _ H1).
        rewrite e0 in *.
        invc X.
        edestruct (IHtypeof1 p2 (left_evt e2)) > [ | reflexivity | ff ].
        -- eauto using same_modulo_plc.
        -- 
          edestruct (IHtypeof2 p2 (right_evt e2)) > [ | reflexivity | ff ].
          ** eauto using same_modulo_plc.
          ** eexists.
          split.
          ++ eapply tc_appr_split.
            --- 
              rewrite <- H5.
              reflexivity.
            --- destruct p0; ff.
            --- destruct p1; ff.
          ++ eapply smp_split.
            --- destruct p0; ff.
            --- destruct p1; ff.
    * invc H.
      eexists.
      split > [
        eapply tc_enc;
        try (eapply same_modulo_plc_denotation_same); ff
        | eauto using same_modulo_plc 
      ].
  - invc H; ff.
    find_eapply_lem_hyp IHt; ff.
    destruct X as [e2' [HTy Hsp]].
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
  - invc H; ff.
    destruct (IHt1 _ _ _ X p2 _ H0) as [e1'' [HTy1 Hsp1]].
    destruct (IHt2 _ _ _ X0 p2 _ Hsp1) as [e2'' [HTy2 Hsp2]].
    ff.
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
  - invc H; ff.
    find_eapply_lem_hyp IHt1 > [ | eauto using same_modulo_plc ].
    find_eapply_lem_hyp IHt2 > [ | eauto using same_modulo_plc ].
    destruct X as [e1'' [HTy1 Hsp1]].
    destruct X0 as [e2'' [HTy2 Hsp2]].
    ff.
    eexists.
    split.
    * eauto using typeof.
    * eauto using same_modulo_plc.
  - invc H; ff.
    find_eapply_lem_hyp IHt1 > [ | eauto using same_modulo_plc ].
    find_eapply_lem_hyp IHt2 > [ | eauto using same_modulo_plc ].
    destruct X as [e1'' [HTy1 Hsp1]].
    destruct X0 as [e2'' [HTy2 Hsp2]].
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
      let iht1v := Control.hyp iht1 in
      let h2v := Control.hyp h2 in
      eapply $iht1v in $h1 as ? > [ | eapply $h2v ]; clear $h1 $h2 $iht1;
      ff
    end); fail
  )).
  prep_induction H.
  induction H; try congruence.
  - ff; invc H0; normer.
  - ff with u; invc H0; normer.
  - ff.
    invc H0; try (normer; fail).
  - ff.
    invc H0; try (normer; fail).
  - ff; invc H1; normer.
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

#[universes(template)]
Inductive sigT_P (A:Type) (PT : A -> Type) (QP : A -> Prop) : Type :=
    existT_P : forall x:A, PT x -> QP x -> sigT_P A PT QP.

(* Helper Lemma: Typeof respects normalization equivalence *)
Lemma typeof_norm_proper : forall G p e1 e2 t e1',
  normalize_ev G e1 = normalize_ev G e2 ->
  typeof G p e1 t e1' ->
  sigT_P EvidenceT (fun e2' => typeof G p e2 t e2') (fun e2' => normalize_ev G e1' = normalize_ev G e2').
Proof.
  intros G p e1 e2 t e1' Heq Hty.
  ltac1:(generalize dependent e2).
  induction Hty; intros e_input Heq_input;
  try (
    eexists > [
      econstructor; ff with l; eapply evt_stack_denotation_transfer; ff
    | ff with u, (norm)
  ]; fail).
  
  (* Case: Operator Rules *)
  - (* tc_att *)
    edestruct IHHty; eauto.
    eexists > [ eapply tc_att; eauto | assumption ].
    
  - (* tc_lseq - The Problem Child becomes easy *)
    edestruct IHHty1; eauto;
    edestruct IHHty2; eauto.
    eexists; ff; eapply tc_lseq; ff.

  - (* tc_bseq *)
    edestruct IHHty1; eauto;
    edestruct IHHty2; eauto.
    eexists > [ eapply tc_bseq; ff | normer ].

  - (* tc_bpar *)
    edestruct IHHty1; eauto.
    edestruct IHHty2; eauto.
    eexists > [ eapply tc_bpar; eauto | normer ].

  - (* tc_appr_asp *)
    eexists.
    + eapply tc_appr_asp > [ | | eapply e1 | | | ]; ff.
    + normer.

  - (* tc_appr_split *)
    edestruct (IHHty1 (left_evt e_input)).
    normer.
    edestruct (IHHty2 (right_evt e_input)).
    normer.

    eexists.
    + eapply tc_appr_split.
      * ff.
      * ff.
      * ff.
    + normer.
Qed.

Theorem typeof_canon_ev_can_type : forall G t p e e',
  typeof G p e t e' ->
  { e'' & typeof G p (normalize_ev G e) t e'' }.
Proof.
  intros.
  eapply (typeof_norm_proper G p e (normalize_ev G e)) in X.
  destruct X.
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

Inductive ContextSupportsAppr (G : GlobalContext) : EvidenceT -> Type :=
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

Lemma CSA_asp_must_type_outer : forall G e a aid args,
  ContextSupportsAppr G (asp_evt a (asp_paramsC aid args) e) ->
  { '(fwd, attrs) | (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) }.
Proof.
  intros.
  prep_induction X.
  induction X; normer;
  Control.enter (fun () =>
    normer;
    try (
    match! goal with
    | [ |- {'(fwd, attrs) | Some (ev_arrow ?fwd ?attrs) = Some (ev_arrow fwd attrs) } ] =>
      solve [
        pp (exist (fun '(fwd, attrs) => (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) ($fwd, $attrs)) as Hsig; ff
        |
        pp (exist (fun '(fwd, attrs) => Some (ev_arrow $fwd $attrs) = Some (ev_arrow fwd attrs)) ($fwd, $attrs)) as Hsig; ff
      ]
    end)
  ).
Qed.

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
Qed.

Lemma CSA_norm_complete : forall G e,
  ContextSupportsAppr G (normalize_ev G e) ->
  ContextSupportsAppr G e.
Proof.
  intros G e H.
  induction e using (normalize_ev_rect_custom G); eauto with csa.
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

(* 
Lemma CSA_norm_exact : forall G e,
  ContextSupportsAppr G e <-> ContextSupportsAppr G (normalize_ev G e).
Proof.
  split > [ eapply CSA_norm_sound | eapply CSA_norm_complete ].
Qed.
*)

(* --- The Main Theorem --- *)
Theorem CSA_canon_invariant : forall G e1 e2,
  normalize_ev G e1 = normalize_ev G e2 ->
  ContextSupportsAppr G e1 ->
  ContextSupportsAppr G e2.
Proof.
  intros G e1 e2 Heq Hcsa.
  eapply CSA_norm_sound in Hcsa.
  eapply CSA_norm_complete.
  ff.
Qed.

(* Helper: Decidability of asp_supported *)
Lemma asp_supported_dec : forall G aid,
  {asp_supported G aid} + {~asp_supported G aid}.
Proof.
  unfold asp_supported; ff.
Qed.

Theorem CSA_dec : forall G e,
  ContextSupportsAppr G e + { ContextSupportsAppr G e -> False }.
Proof.
  intros.
  induction e using (normalize_ev_rect_custom G).
  - left; eapply csa_mt; normer.
  - 
    destruct ((asp_types G) ![ check_nonce_aspid ]) eqn:?;
    try (right; intros HC; invc HC; normer; fail).
    destruct e; try (right; intros HC; invc HC; normer; fail).
    destruct e; try (right; intros HC; invc HC; normer; fail).
    destruct n0; try (right; intros HC; invc HC; normer; fail).
    destruct x; try (right; intros HC; invc HC; normer; fail).
    destruct x; try (right; intros HC; invc HC; normer; fail).
    left; eapply csa_nonce with (n := n); ff.
  - 
    ff.
    + left.
      eapply CSA_norm_complete.
      norm; ff.
    + right.
      intros HC.
      invc HC; norm; ff.
      * eauto with csa.
      * eapply Hsumor_r.  
        eapply csa_nonce; normer.
      * eapply Hsumor_r.
        eapply csa_split > [ norm | | ]; ff;
        eapply CSA_norm_sound; ff.
  - ff; try (right; intros HC; invc HC; norm; ff; fail).
  - 
    ff.
    + left.
      eapply CSA_norm_complete.
      norm; ff.
    + right.
      intros HC.
      invc HC; norm; ff.
      * eauto with csa.
      * eapply Hsumor_r.  
        eapply csa_nonce; normer.
      * eapply Hsumor_r.
        eapply csa_split > [ norm | | ]; ff;
        eapply CSA_norm_sound; ff.
  - ff; try (right; intros HC; invc HC; norm; ff; fail).
  - destruct IHe1, IHe2;
    try (
      right; intros HC; invc HC; norm; ff;
      repeat (find_eapply_lem_hyp CSA_norm_complete); ff;
      fail
    ).
    left.
    eapply csa_split > [ norm | | ]; ff;
    eapply CSA_norm_sound; ff.
  - ff.
    + left.
      eapply CSA_norm_complete.
      norm; ff.
    + right.
      intros HC.      
      invc HC; norm; ff.
      * eauto with csa.
      * eapply Hsumor_r.  
        eapply csa_nonce; normer.
      * eapply Hsumor_r.
        eapply csa_split > [ norm | | ]; ff;
        eapply CSA_norm_sound; ff.
  -
    destruct (asp_supported_dec G aid), IHe1; ff;
    try (right; intros HC; invc HC; normer; ff with (eauto with csa); fail);
    Control.enter (fun () => 
    left; pp c; eapply CSA_norm_sound in c; find_rewrite;
    eapply CSA_asp_must_type_outer in c;
    destruct c as [ [ fwd attrs ] Hex ];
    try (eapply csa_asp_asp; ff; fail)).
  - destruct (asp_supported_dec G aid), IHe1; ff;
    try (right; intros HC; invc HC; normer; ff with (eauto with csa); fail).
    * 
      destruct (normalize_ev G e1) eqn:?; 
      try (destruct a0); normer;
      destruct ((asp_types G) ![ aid ]) as [[fwd attrs]|] eqn:Hasp; normer; 
      try (right; intros HC; invc HC; normer; ff with (eauto with csa); fail);
      destruct fwd; normer;
      try (right; intros HC; invc HC; normer; ff with (eauto with csa); fail);
      try (left; eapply csa_asp_mt; normer; fail);
      try (left; invc c; normer; eapply csa_asp_nonce; normer; fail);
      try (left; invc c; normer;
        eapply csa_asp_split; norm; ff; eapply CSA_norm_complete; ff; fail).
    
    * right.
      intros HC.
      invc HC; normer; ff with (eauto with csa).
      + eapply f; eapply csa_nonce; normer.
      + eapply f; eapply csa_split > [ norm | | ]; ff;
        eapply CSA_norm_sound; ff.
Qed.

Lemma CSA_appraisal_sound : forall G e,
  ContextSupportsAppr G e ->
  forall p, { e'' & typeof G p e (asp APPR) e''}.
Proof.
  intros G e Hcsat.
  induction Hcsat; ff with (eauto using typeof).
  (* - eexists; eapply tc_appr_nonce; normer. *)
  - destruct (IHHcsat p) as [e'' Htyp].
    eapply (appr_canon_invariant G p _ _ _ _ Htyp).
    Unshelve.
    normer; find_eapply_lem_hyp normalize_ev_done; normer.

  - destruct (IHHcsat p) as [e'' Htyp].
    eapply (appr_canon_invariant G p _ _ _ _ Htyp).
    Unshelve.
    normer; find_eapply_lem_hyp normalize_ev_done; normer.

  - destruct (IHHcsat1 p) as [e1'' Htyp1]; 
    find_eapply_lem_hyp tc_left_split; ff;
    destruct (IHHcsat2 p) as [e2'' Htyp2]; 
    find_eapply_lem_hyp tc_right_split; ff.
    assert (normalize_ev G (left_evt (split_evt l r)) = normalize_ev G (left_evt e)). {
      ff.
      norm.
      ff.
      eapply normalize_ev_done in e0.
      normer.
    }
    destruct Htyp1 as [e1_norm Htyp1_norm].
    pp (appr_canon_invariant G p _ _ _ H Htyp1_norm).
    assert (normalize_ev G (right_evt (split_evt l r)) = normalize_ev G (right_evt e)). {
      ff.
      norm.
      ff.
      eapply normalize_ev_done in Heq.
      normer.
    }
    destruct Htyp2 as [e2_norm Htyp2_norm].
    pp (appr_canon_invariant G p _ _ _ H0 Htyp2_norm).
    ff.
    destruct X, X0.
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
    unfold asp_supported in *; ff; destruct t, t0;
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
      eapply normalize_ev_done in e as ?.
      normer.
    }


    eapply (appr_canon_invariant _ _ _ _ _ Heq) in t.
    ff.
  - edestruct IHHcsat as [e_inner_res Htyp_inner].

    pose proof (normalize_ev_done G _ _ e) as Hnorm_fixed.
    eapply appr_canon_invariant in Htyp_inner > [| rewrite e; rewrite Hnorm_fixed; reflexivity].
    destruct Htyp_inner as [e_inner_norm_res Htyp_inner_norm].

    destruct fwd.

    * unfold asp_supported in *;
      find_rewrite.
      destruct ((asp_comps G) ![ aid ]) as [appr_id|] eqn:Hcomp > [| ff];
      destruct ((asp_types G) ![ appr_id ]) as [[fwd_appr attrs_appr]|] eqn:Htype_appr > [| ff];
      destruct fwd_appr; try (ff; fail); 
      eexists;
      eapply tc_appr_asp >
      [ exact Htyp_inner_norm | norm; ff | ff | ff | ff | split; ff ].

    (* CASE 1: fwd = WRAP n *)
    * unfold asp_supported in *; find_rewrite.
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
      + ff.

    * ff.

    * unfold asp_supported in *; find_rewrite.
      destruct ((asp_comps G) ![ aid ]) as [appr_id|] eqn:Hcomp > [| ff];
      destruct ((asp_types G) ![ appr_id ]) as [[fwd_appr attrs_appr]|] eqn:Htype_appr > [| ff];
      destruct fwd_appr; try (ff; fail); 
      eexists;
      eapply tc_appr_asp >
      [ exact Htyp_inner_norm
      | norm; ff
      | exact Htype_appr
      | exact Hcomp
      | ff
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
Inductive str_provenance (G : GlobalContext) : EvidenceT -> EvidenceT -> Prop :=
  | str_prov_refl : forall e, str_provenance G e e
  | str_prov_left : forall e e',
      str_provenance G e e' ->
      str_provenance G e (left_evt e')
  | str_prov_right : forall e e',
      str_provenance G e e' ->
      str_provenance G e (right_evt e')
  (* Split is unique:
    - we allow the duplication (in fact it is what happens in the left and right rules), 
      but we don't allow the "joining" of two different evidences into one split, 
      because that would lose provenance information.

      Thus, we only have the "injection" rule for split, but not the "left" and "right" rules for split.
  *)
  | str_prov_split_inj : forall l r e,
      str_provenance G e l ->
      str_provenance G e r ->
      str_provenance G e (split_evt l r)
  | str_prov_asp : forall e p aid args e',
      str_provenance G e e' ->
      str_provenance G e (asp_evt p (asp_paramsC aid args) e').

Theorem str_provenance_monotonic : forall G e e',
  str_provenance G e e' ->
  EvidenceT_depth e <= EvidenceT_depth e'.
Proof.
  intros.
  induction H; ff with l.
Qed.

Lemma str_provenance_trans : forall G e1 e2 e3,
  str_provenance G e1 e2 ->
  str_provenance G e2 e3 ->
  str_provenance G e1 e3.
Proof.
  intros.
  prep_induction H0.
  induction H0; ff; eauto using str_provenance.
Qed.

Theorem typecheck_preserves_str_provenance : forall G t p e e',
  typeof G p e t e' ->
  str_provenance G e e'.
Proof.
  intros.
  induction X; eauto using str_provenance.
  - eapply str_provenance_trans; ff.
  - eapply str_prov_split_inj;
    eapply str_provenance_trans > [ | eassumption ];
    eauto using str_provenance.
Qed.

(** Evidence Contextual Hole: 
  This forces explicit provenance (as evidence must be plugged into some hole)
  and relevance (as the hole must be plugged with the original evidence, not some other one)
  as well as contraction 
  (as the same evidence can be plugged into multiple holes (specifically in split), 
    but not different evidences into different holes).
*)
Inductive EvContext :=
  | Hole : EvContext
  (* Structural Wrappers *)
  | Ctx_Left : EvContext -> EvContext
  | Ctx_Right : EvContext -> EvContext
  (* The Contraction Constructor: 'e' is used in BOTH sub-trees *)
  | Ctx_Split_Branch : EvContext -> EvContext -> EvContext 
  (* ASP Wrapper: We can only ever wrap 1 deep!! *)
  | Ctx_Asp : Plc -> ASP_PARAMS -> EvContext -> EvContext.

(* The Plug Semantics *)
Fixpoint plug (c : EvContext) (e : EvidenceT) : EvidenceT :=
  match c with
  | Hole => e
  | Ctx_Left c' => left_evt (plug c' e)
  | Ctx_Right c' => right_evt (plug c' e)
  (* Contraction: Plug 'e' into both c1 and c2 *)
  | Ctx_Split_Branch c1 c2 => split_evt (plug c1 e) (plug c2 e)
  | Ctx_Asp p args c' => asp_evt p args (plug c' e)
  end.
  
(* Composition of Contexts: Essential for proving sequential operations (lseq) *)
Fixpoint compose (outer inner : EvContext) : EvContext :=
  match outer with
  | Hole => inner
  | Ctx_Left c' => Ctx_Left (compose c' inner)
  | Ctx_Right c' => Ctx_Right (compose c' inner)
  | Ctx_Split_Branch c1 c2 => Ctx_Split_Branch (compose c1 inner) (compose c2 inner)
  | Ctx_Asp p par c' => Ctx_Asp p par (compose c' inner)
  end.

Lemma plug_compose : forall outer inner e,
  plug (compose outer inner) e = plug outer (plug inner e).
Proof.
  induction outer; ff; congruence.
Qed.

Definition ordered_provenance (e e' : EvidenceT) := 
  { c : EvContext | plug c e = e' }.

Theorem typeof_ordered_provenance : forall G p e t e',
  typeof G p e t e' ->
  ordered_provenance e e'.
Proof.
  intros G p e t e' H.
  unfold ordered_provenance.
  induction H.
  (* ASPs & Single paths *)
  - exists (Ctx_Asp p sig_params Hole); reflexivity.
  - exists (Ctx_Asp p hsh_params Hole); reflexivity.
  - exists (Ctx_Asp p (enc_params p') Hole); reflexivity.
  - exists (Ctx_Asp p (asp_paramsC aid args) Hole); reflexivity.
  - exists (Ctx_Asp p (asp_paramsC aid args) Hole); reflexivity.
  - exists (Ctx_Asp p (asp_paramsC aid args) Hole); reflexivity.
  - destruct IHtypeof as [c Hplug]; exists c; assumption.
  - destruct IHtypeof1 as [c1 Hplug1]; 
    destruct IHtypeof2 as [c2 Hplug2].
    exists (compose c2 c1); rewrite plug_compose; congruence.
  (* --- The Parallel Cases (Contraction) --- *)
  - (* tc_bseq: e flows into BOTH t1 and t2 *)
    destruct IHtypeof1 as [c1 Hplug1].
    destruct IHtypeof2 as [c2 Hplug2].
    (* We use the Branching constructor! *)
    exists (Ctx_Split_Branch c1 c2); ff.
  - (* tc_bpar: Symmetric to bseq *)
    destruct IHtypeof1 as [c1 Hplug1].
    destruct IHtypeof2 as [c2 Hplug2].
    exists (Ctx_Split_Branch c1 c2); ff.
  (* --- Appraisal Cases --- *)
  - (* tc_appr_mt *) exists Hole; reflexivity.
  - (* tc_appr_nonce *) exists (Ctx_Asp p check_nonce_params Hole); reflexivity.
  - (* tc_appr_asp_unwrap *) exists (Ctx_Asp p (asp_paramsC appr_id args) Hole); reflexivity.
  - (* tc_appr_asp *) exists (Ctx_Asp p (asp_paramsC appr_id args) Hole); reflexivity.
  - (* tc_appr_split *)
    destruct IHtypeof1 as [c1 Hplug1].
    destruct IHtypeof2 as [c2 Hplug2].
    exists (Ctx_Split_Branch 
             (compose c1 (Ctx_Left Hole)) 
             (compose c2 (Ctx_Right Hole)));
    ff; repeat (rewrite plug_compose); ff.
Defined.

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

(* Major Theorem: Appraisability *)
Theorem well_typed_appraisable : forall G e p,
  ContextSupportsAppr G e ->
  { e'' & typeof G p e (asp APPR) e'' }.
Proof.
  intros.
  eapply CSA_appraisal_sound.
  ff.
Qed.

Print Assumptions well_typed_appraisable.

(* This justifies that the type system enforces the non-commutativity of evidence *)
Theorem evidence_non_commutative : forall p,
  (* NOTE: This could probably be strengthed, but it is at least good evidence *)
  sigT_P (GlobalContext * EvidenceT * Term * Term * EvidenceT * EvidenceT) 
    (fun '(G, e, t1, t2, e1, e2) =>
      (typeof G p e (lseq t1 t2) e1 * typeof G p e (lseq t2 t1) e2)%type)
    (fun '(G, e, t1, t2, e1, e2) => (e1 <> e2)%type).
Proof.
  intros p.
  ltac1:(evar (e1' : EvidenceT)).
  ltac1:(evar (e2' : EvidenceT)).
  eapply (
    existT_P 
      (GlobalContext * EvidenceT * Term * Term * EvidenceT * EvidenceT) 
      (fun '(G, e, t1, t2, e1, e2) =>
        (typeof G p e (lseq t1 t2) e1 * typeof G p e (lseq t2 t1) e2)%type)
      (fun '(G, e, t1, t2, e1, e2) => (e1 <> e2)%type)
      ((Build_GlobalContext _ [
            (sig_aspid, ev_arrow (EXTEND (exist _ 1 Nat.lt_0_1) InAll) [])
            ; (hsh_aspid, ev_arrow (REPLACE (exist _ 1 Nat.lt_0_1)) [])
          ] []), 
        (nonce_evt 1), 
        (asp HSH), 
        (asp SIG),
        e1',
        e2'
      )
  ).
  - split.
    * subst e1'.
      repeat (econstructor; ff).
    * subst e2'.
      eapply tc_lseq.
      repeat (econstructor; ff).
      econstructor.
      + eapply interp_asp_extend.
        -- ff.
        -- evter.
      + ff with l.
      + ff.
  - subst e1' e2'.
    ff.
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
  -- apply CSA_norm_complete.

    rewrite e0.

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
      eapply CSA_norm_sound in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp); normer.
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
      + ff.

    (* Case D: Inner is ASP. Use csa_asp_asp *)
    - destruct a.
      eapply CSA_norm_sound in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp); normer;
      eapply csa_asp_asp > [ exact Heq_norm_inner | ff | ff | ff | unfold asp_supported; ff | eapply CSA_norm_complete ; ff ]; ff.
      ff.
    - invc Htyp; normer.
    - invc Htyp; normer.

    (* Case C: Inner is Split. Use csa_asp_split *)
    - 
      pp (IHHtyp eq_refl).
      eapply CSA_norm_sound in X.
      ff.
      invc X; normer.
      eapply csa_asp_split > [ exact Heq_norm_inner | ff | ff | unfold asp_supported; ff | | ];
      eapply CSA_norm_complete; ff.

  -- 
    eapply CSA_norm_complete.

    rewrite e0.

    (* 3. We must inspect the inner evidence e' to pick the right CSA rule.
          Note: 'e' is the outer WRAP evidence. 'e'' is what is inside it. *)
    destruct (normalize_ev G e') eqn:Heq_norm_inner.

    (* Case A: Inner is MT. Use csa_asp_mt *)
    - eapply csa_asp_mt; ff.
      unfold asp_supported; ff.

    (* Case B: Inner is Nonce. Use csa_asp_nonce *)
    - 
      eapply CSA_norm_sound in IHHtyp.
      rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp); normer.
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
      + ff.

    (* Case D: Inner is ASP. Use csa_asp_asp *)
    - destruct a0.
      eapply CSA_norm_sound in IHHtyp. rewrite Heq_norm_inner in IHHtyp.
      inversion (IHHtyp); normer;
      eapply csa_asp_asp > [ exact Heq_norm_inner | ff | ff | ff | unfold asp_supported; ff with (congruence) | eapply CSA_norm_complete; ff ].
      ff.
    - invc Htyp; normer.
    - invc Htyp; normer.

    (* Case C: Inner is Split. Use csa_asp_split *)
    - 
      pp (IHHtyp eq_refl).
      eapply CSA_norm_sound in X.
      ff.
      invc X; normer.
      eapply csa_asp_split > [ exact Heq_norm_inner | ff | ff | unfold asp_supported; ff | | ];
      eapply CSA_norm_complete; ff.
  -- 
      pp (CSA_norm_sound _ _ (IHHtyp1 eq_refl)).
      pp (CSA_norm_sound _ _ (IHHtyp2 eq_refl)).
      norm.
      ff.
      eapply csa_split > [ norm; ff | | ]; ff.
Qed.

Theorem typeof_appr_decidable : forall G p e,
  ({ e' & typeof G p e (asp APPR) e' }) + {forall e', typeof G p e (asp APPR) e' -> False}.
Proof.
  intros.
  destruct (CSA_dec G e).
  - left.
    eapply CSA_appraisal_sound; assumption.
  - right.
    intros e' HC.
    eapply f.
    eapply CSA_appraisal_complete.
    ff.
Qed.

Fixpoint term_size (t : Term) : nat :=
  match t with
  | asp APPR => 0 (* this is handled outside *)
  | asp _ => 1
  | att _ t' => S (term_size t')
  | lseq t1 t2 => S (term_size t1 + term_size t2)
  | bseq t1 t2 => S (term_size t1 + term_size t2)
  | bpar t1 t2 => S (term_size t1 + term_size t2)
  end.

Fixpoint term_ev_size (e : EvidenceT) (t : Term) : nat :=
  match t with
  | asp APPR => EvidenceT_depth e
  | asp _ => 1
  | att _ t' => S (term_ev_size e t')
  | lseq t1 t2 => S (term_ev_size e t1 + term_ev_size e t2)
  | bseq t1 t2 => S (term_ev_size e t1 + term_ev_size e t2)
  | bpar t1 t2 => S (term_ev_size e t1 + term_ev_size e t2)
  end.

Equations? typeof_fix (G : GlobalContext) (p : Plc) (t : Term) (e : EvidenceT) 
  : { e' & typeof G p e t e' } + { forall e', typeof G p e t e' -> False } 
    by wf (term_size t) lt :=
  typeof_fix G p (asp APPR) e := typeof_appr_decidable G p e ;
  typeof_fix G p (asp NULL) e := (* always false *) inright (fun e' Htyp => _) ;
  typeof_fix G p (asp SIG) e := _;
  typeof_fix G p (asp HSH) e := _;
  typeof_fix G p (asp (ENC p')) e := _;
  typeof_fix G p (asp (ASPC (asp_paramsC aid args))) e := _;
  typeof_fix G p (att q t) e := 
    match typeof_fix G q t e with
    | inleft (existT _ e' Htyp) => 
        inleft (existT _ e' (tc_att _ _ _ _ _ _ Htyp))
    | inright Hnty => 
        inright (fun e' Htyp => Hnty _ _)
    end ;
  typeof_fix G p (lseq t1 t2) e := 
    match typeof_fix G p t1 e with
    | inleft (existT _ e1 Htyp1) => 
        match typeof_fix G p t2 e1 with
        | inleft (existT _ e2 Htyp2) => 
            inleft (existT _ _ (tc_lseq _ _ _ _ _ _ _ Htyp1 Htyp2))
        | inright Hnty2 => inright (fun e2 Htyp => _)
        end
    | inright Hnty1 => inright (fun e1 Htyp => _)
    end ;
  typeof_fix G p (bseq t1 t2) e := 
    match typeof_fix G p t1 e, typeof_fix G p t2 e with
    | inleft (existT _ e1 Htyp1), inleft (existT _ e2 Htyp2) => 
        inleft (existT _ (split_evt e1 e2) 
          (tc_bseq _ _ _ _ _ _ _ Htyp1 Htyp2)
        )
    | inright Hnty1, _ => inright (fun e1 Htyp => _)
    | _, inright Hnty2 => inright (fun e2 Htyp => _)
    end ;
  typeof_fix G p (bpar t1 t2) e := 
    match typeof_fix G p t1 e, typeof_fix G p t2 e with
    | inleft (existT _ e1 Htyp1), inleft (existT _ e2 Htyp2) => 
        inleft (existT _ (split_evt e1 e2) 
          (tc_bpar _ _ _ _ _ _ _ Htyp1 Htyp2)
        )
    | inright Hnty1, _ => inright (fun e1 Htyp => _)
    | _, inright Hnty2 => inright (fun e2 Htyp => _)
    end.
all: try (ff with l; fail).
all: try (invc Htyp; ff; fail).
- destruct ((asp_types G) ![ aid ]) eqn:?;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct e0, e0;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  + (* arbitrary ASP - replace *)
    destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
    try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
    destruct n as [n nlt].
    (* destruct (dec_eq n 1); ff; 
    try (right; intros e' Htyp; invc Htyp; try (unfold not in * ); ff; fail). *)
    destruct (le_dec 1 nden).
    * left; eexists; eapply tc_in_all; ff.
    * right.
      intros e' Htyp.
      invc Htyp;
      Control.enter (fun () =>
        match! goal with
        | [ h1 : evt_stack_denotation ?_g ?_e _ , 
            h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
          let h1v := Control.hyp h1 in
          let h2v := Control.hyp h2 in
          pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
        end
      ).
  + (* arbitrary ASP - wrap *)
    destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
    try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
    destruct n as [n nlt].
    (* destruct (dec_eq n 1); ff; 
    try (right; intros e' Htyp; invc Htyp; try (unfold not in * ); ff; fail). *)
    destruct (le_dec 1 nden).
    * left; eexists; eapply tc_in_all; ff.
    * right.
      intros e' Htyp.
      invc Htyp;
      Control.enter (fun () =>
        match! goal with
        | [ h1 : evt_stack_denotation ?_g ?_e _ , 
            h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
          let h1v := Control.hyp h1 in
          let h2v := Control.hyp h2 in
          pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
        end
      ).
  + (* arbitrary ASP - replace *)
    destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
    try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
    destruct (le_dec 1 nden).
    * left; eexists; eapply tc_in_all; ff.
    * right.
      intros e' Htyp.
      invc Htyp;
      Control.enter (fun () =>
        match! goal with
        | [ h1 : evt_stack_denotation ?_g ?_e _ , 
            h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
          let h1v := Control.hyp h1 in
          let h2v := Control.hyp h2 in
          pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
        end
      ).
  + destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
    try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
    destruct n as [n nlt].
    destruct (dec_eq nden 0); ff.
    -- (* 0 incoming, better be InNone  *)
      destruct e0; ff; try (
        right; intros e' Htyp;
        invc Htyp; ff;
        Control.enter (fun () =>
        match! goal with
        | [ h1 : evt_stack_denotation ?_g ?_e _ , 
            h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
          let h1v := Control.hyp h1 in
          let h2v := Control.hyp h2 in
          pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
        end; ff with l); fail).
      left; eexists; eapply tc_extend_in_none; ff.
    -- (* more than 1 incoming, better be InAll *)
      destruct e0; ff; try (
        right; intros e' Htyp;
        invc Htyp; ff;
        Control.enter (fun () =>
        match! goal with
        | [ h1 : evt_stack_denotation ?_g ?_e _ , 
            h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
          let h1v := Control.hyp h1 in
          let h2v := Control.hyp h2 in
          pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
        end; ff with l); fail).
      left; eexists; eapply tc_extend_in_all; ff with l.
- destruct ((asp_types G) ![ sig_aspid ]) eqn:?;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct e0, e0;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct e0;
  destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
  try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
  destruct n as [n nlt].
  destruct (dec_eq n 1); ff; 
  try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
  destruct (le_dec 1 nden).
  * left; eexists; eauto using typeof.
  * right.
    intros e' Htyp.
    invc Htyp.
    match! goal with
    | [ h1 : evt_stack_denotation ?_g ?_e _ , 
        h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
      let h1v := Control.hyp h1 in
      let h2v := Control.hyp h2 in
      pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
    end.
- destruct ((asp_types G) ![ hsh_aspid ]) eqn:?;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct e0, e0;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
  try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
  destruct n as [n nlt].
  destruct (dec_eq n 1); ff; 
  try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
  destruct (le_dec 1 nden).
  * left; eexists; eauto using typeof.
  * right.
    intros e' Htyp.
    invc Htyp.
    match! goal with
    | [ h1 : evt_stack_denotation ?_g ?_e _ , 
        h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
      let h1v := Control.hyp h1 in
      let h2v := Control.hyp h2 in
      pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
    end.
- destruct ((asp_types G) ![ enc_aspid ]) eqn:?;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct e0, e0;
  try (right; intros e' Htyp; invc Htyp; ff; fail).
  destruct (evt_stack_denotation_size G e) as [[nden Hnden] |];
  try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
  destruct n as [n nlt].
  destruct (dec_eq n 1); ff; 
  try (right; intros e' Htyp; invc Htyp; try (unfold not in *); ff; fail).
  destruct (le_dec 1 nden).
  * left; eexists; eauto using typeof.
  * right.
    intros e' Htyp.
    invc Htyp.
    match! goal with
    | [ h1 : evt_stack_denotation ?_g ?_e _ , 
        h2 : evt_stack_denotation ?_g ?_e _ |- _ ] =>
      let h1v := Control.hyp h1 in
      let h2v := Control.hyp h2 in
      pp (evt_stack_denotation_deterministic _ _ _ _ $h1v $h2v); ff
    end.
- invc Htyp.
  eapply typeof_deterministic in Htyp1; try (eapply X0); ff.
Defined.