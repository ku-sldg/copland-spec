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

Ltac2 Notation "norm" := ltac1:( simp normalize_ev in * ).
Ltac2 Notation "normer" := (norm; ff).

Theorem normalize_ev_measure_decrease : forall G e e',
  normalize_ev G e = e' ->
  EvidenceT_depth e' <= EvidenceT_depth e.
Proof.
  intros.
  ltac1:( funelim (normalize_ev G e); simp normalize_ev in * ); ff with l;
  try (pp (H _ eq_refl); ff with l; fail).
  pp (H _ eq_refl); pp (H0 _ eq_refl); ff with l.
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
Inductive wf_EvT (G : GlobalContext) : EvidenceT -> Prop :=
| wf_EvT_mt : wf_EvT G mt_evt
| wf_EvT_nonce : forall n, wf_EvT G (nonce_evt n)
| wf_EvT_split : forall l r,
    wf_EvT G l ->
    wf_EvT G r ->
    wf_EvT G (split_evt l r)
| wf_EvT_left : forall e' l r,
    canon_ev_rep G e' = split_evt l r ->
    wf_EvT G l ->
    wf_EvT G (left_evt e')
| wf_EvT_right : forall e' l r,
    canon_ev_rep G e' = split_evt l r ->
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
    canon_ev_rep G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
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
    canon_ev_rep G e' = split_evt l r ->
    evt_stack_denotation G l n ->
    evt_stack_denotation G (left_evt e') n
| interp_right : forall e' l r n,
    canon_ev_rep G e' = split_evt l r ->
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
    canon_ev_rep G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
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
    + unfold canon_ev_rep in *.
      find_rewrite.
      ff.
  - invc H0; unfold canon_ev_rep in *; ff.
  - invc H0; unfold canon_ev_rep in *; ff.
  - invc H1.
    ff with a.
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
  repeat (normer; ff).
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
      normer; evter; fail).
    + ltac1:( simp normalize_ev in * ).
      evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      unfold canon_ev_rep in *;
      normer; evter.
      eapply normalize_ev_done in Heq5.
      ltac1:( simp normalize_ev in Heq5 ).
      ff.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      unfold canon_ev_rep in *;
      normer; evter.
      eapply normalize_ev_done in Heq1.
      normer; evter.
    + erewrite <- Heqcall in *.
      invc H0; evter;
      unfold canon_ev_rep in *;
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
      unfold canon_ev_rep in *.
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
      unfold canon_ev_rep in *.
      normer; eapply normalize_ev_done in Heq0; normer.
    + rewrite <- Heqcall in *.
      invc H0.
      unfold canon_ev_rep in *.
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
    ~ (exists n nlt, fwd = EXTEND (exist _ n nlt) InNone) ->
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
    canon_ev_rep G e = mt_evt ->
    typeof G p e (asp APPR) e
| tc_appr_nonce : forall p e n,
    canon_ev_rep G e = nonce_evt n ->
    typeof G p e (asp APPR) (asp_evt p check_nonce_params e)
| tc_appr_asp : forall p p' e aid args e' appr_id fwd fwd' attrs attrs' e'',
    typeof G p e' (asp APPR) e'' ->
    canon_ev_rep G e = asp_evt p' (asp_paramsC aid args) e' ->
    (asp_types G) ![ appr_id ] = Some (ev_arrow fwd attrs) ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd' attrs') ->
    typeof G p e (asp APPR) (asp_evt p (asp_paramsC appr_id args) e)
| tc_appr_split : forall p el er el' er' e,
    canon_ev_rep G e = split_evt el er ->
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
  same_modulo_plc (canon_ev_rep G e1) (canon_ev_rep G e2).
Proof.
  intros.
  unfold canon_ev_rep.
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
          hc : canon_ev_rep _ _ = _
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
  canon_ev_rep G e1 = canon_ev_rep G e2 ->
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
    eapply tc_appr_nonce.
    ff.

  (* Case 3: tc_appr_asp *)
  - exists (asp_evt p (asp_paramsC appr_id args) e_target).
    eapply tc_appr_asp; ff.

  (* Case 4: tc_appr_split *)
  (* This is the hard case where your original proof got stuck *)
  - destruct (IHHtype1 eq_refl (left_evt e_target)) as [el'' Hl].
    + (* Proof that canon (left e) == canon (left e_target) *)
      unfold canon_ev_rep in *.
      (* We know canon e = split el er. 
         By def of normalize_ev, canon (left e) = el *)
      assert (Hnorm_l: normalize_ev G (left_evt e) = el) by normer.
      
      (* We know canon e_target = split el er (via Hcanon_eq).
         By def of normalize_ev, canon (left e_target) = el *)
      assert (Hnorm_target_l: normalize_ev G (left_evt e_target) = el) by normer.
      ff.
      
    + destruct (IHHtype2 eq_refl (right_evt e_target)) as [er'' Hr].
      * (* Proof that canon (right e) == canon (right e_target) *)
        unfold canon_ev_rep in *.
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
    * unfold canon_ev_rep in *.
      edestruct (IHtypeof eq_refl q).
      assert (e' = asp_evt p'0 (asp_paramsC aid0 args0) e'0) as Heq.
      {
        eapply normalize_ev_done in H0 as ?.
        norm.
        repeat find_rewrite.
        repeat break_match; ff.
        eapply canon_ev_canonical in H5; ff with l.
      }
      subst.
      eexists.
      eapply tc_appr_asp 
      > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 ].
      ff.

    * 
      unfold canon_ev_rep in *.
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
      eapply tc_appr_asp > [ | eapply H0 | eapply H1 | eapply H2 | eapply H3 ].
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
        pp (same_modulo_plc_canon_ev G _ _ H0).
        erewrite H in *.
        invc H1.
        ff.
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
  - ff; invc H0; normer.
  - ff.
    invc H4; try (normer; fail).
  - ff; invc H2; normer.
    find_eapply_lem_hyp IHtypeof1; ff.
    find_eapply_lem_hyp IHtypeof2; ff.
Qed.

(* Theorem typeof_canon_ev_can_type : forall G t p e e',
  typeof G (cop_phrase p e t) e' ->
  exists e'', 
    typeof G (cop_phrase p (canon_ev_rep G e) t) e''.
Proof.
  unfold canon_ev_rep in *.
  induction t; ff.
  - destruct a; try (
      invc H;
      try (erewrite equiv_preserves_denotation_size in * );
      normer; eauto using typeof; fail).
    
    

    prep_induction H.
    induction H; ff;
    unfold canon_ev_rep in *; ff.
    * eexists.
      eapply tc_appr_mt.
      ff.
    * eexists.
      eapply tc_appr_nonce.
      unfold canon_ev_rep in *.
      eapply normalize_ev_done.
      ff.
    * eexists.
      eapply tc_appr_asp.
      -- unfold canon_ev_rep in *.
        eapply normalize_ev_done.
        ff.
      -- ff.
    * 
      pp (IHtypeof1 _ _ eq_refl).
      pp (IHtypeof2 _ _ eq_refl).
      ff.
      norm.
      ff.
      eexists.
      eapply tc_appr_split.
      -- normer.
      -- 
      -- 


      invc H0; 
      invc H1;
      unfold canon_ev_rep in *; normer.
      + eexists;
        eapply tc_appr_split > [ 
          eapply normalize_ev_done; ff
          | eauto using typeof; normer
          | eauto using typeof; normer
        ].
      + eexists.
        eapply tc_appr_split > [ 
          eapply normalize_ev_done; ff 
          | 
          |
        ].
        -- eapply tc_appr_mt; normer.
        -- eapply tc_appr_nonce; normer.
      + admit.
      + 
      + 
        destruct (normalize_ev G e') eqn:?.
        ***
          eexists.
          eapply tc_appr_split.
          -- eapply normalize_ev_done.
            eauto.
          -- eapply tc_appr_mt; normer.
          -- eapply tc_appr_asp; normer.
        ***
          eexists.
          eapply tc_appr_split.
          -- eapply normalize_ev_done.
            eauto.
          -- eapply tc_appr_mt; normer.
          -- eapply tc_appr_asp; normer.
        ***
          eexists.
          eapply tc_appr_split.
          -- eapply normalize_ev_done.
            eauto.
          -- eapply tc_appr_mt; normer.
          -- eapply tc_appr_asp; normer.
            eapply normalize_ev_done in H; normer.
            admit.
        *** 
          eexists.
            ** normer.
      + eexists.
        eapply tc_app
        eapply tc_appr_split > [ 
          eapply normalize_ev_done; ff 
          | eauto using typeof; normer
          | eauto using typeof; normer
        ].
        eapply tc_appr_asp.
        unfold canon_ev_rep in *.
        normer.
      + 
      + 
      + normer.
        eapply normalize_ev_done in H5.

      destruct (normalize_ev G el) eqn:?.
      destruct (normalize_ev G er) eqn:?.
      ++ 
      eexists.
      eapply tc_appr_split;
      unfold canon_ev_rep in *.
      -- 
        eapply normalize_ev_done.
        ff.
      -- eapply tc_appr_mt.
          normer.
      -- eapply tc_appr_mt.
          normer.
      ++ 
      eexists.
      eapply tc_appr_split;
      unfold canon_ev_rep in *.
      -- eapply normalize_ev_done.
        ff.
      -- eapply tc_appr_mt.
        normer.
      -- eapply tc_appr_nonce.
         normer.
      ++ destruct a.
      eexists.
      eapply tc_appr_split;
      unfold canon_ev_rep in *.
      -- eapply normalize_ev_done.
        ff.
      -- eapply tc_appr_mt.
         normer.
      -- eapply tc_appr_asp.
        normer.
      -- 
        destruct a.
        ff.

        pp (IHtypeof1 _ _ eq_refl).
        ff.
        normer.
        ** eapply tc_appr_mt.
          normer.
        ** eapply tc_appr_nonce.
           normer.



        normer; eauto using typeof.
    * invc H; unfold sig_params in *.
      normer.
      eexists.
      eapply tc_sig.

    * invc H; unfold hsh_params in *.
      normer; eapply tc_hsh; admit.
    * admit.
    * invc H; unfold enc_params in *.
      normer; eapply tc_enc; admit.
  - invc H.
    find_eapply_lem_hyp IHt; ff.
    eapply tc_att.
    ff.
  - invc H.
    find_eapply_lem_hyp IHt1; ff.
    find_eapply_lem_hyp IHt2; ff.
    eapply tc_lseq; ff.
  - invc H.
    find_eapply_lem_hyp IHt1; ff.
    find_eapply_lem_hyp IHt2; ff.
    norm.
    eapply tc_bseq; ff.
  - invc H.
    find_eapply_lem_hyp IHt1; ff.
    find_eapply_lem_hyp IHt2; ff.
    norm.
    eapply tc_bpar; ff.
Qed. *)

Inductive ContextSupportsAppr (G : GlobalContext) : EvidenceT -> Prop :=
| csa_mt : ContextSupportsAppr G mt_evt
| csa_nonce : forall n, ContextSupportsAppr G (nonce_evt n)
| csa_left : forall e' l r,
    canon_ev_rep G e' = split_evt l r ->
    ContextSupportsAppr G l ->
    ContextSupportsAppr G (left_evt e')
| csa_right : forall e' l r,
    canon_ev_rep G e' = split_evt l r ->
    ContextSupportsAppr G r ->
    ContextSupportsAppr G (right_evt e')
| csa_split : forall l r,
    ContextSupportsAppr G l ->
    ContextSupportsAppr G r ->
    ContextSupportsAppr G (split_evt l r)
| csa_asp_mt : forall p aid args e' appr_id fwd attrs,
    canon_ev_rep G e' = mt_evt ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    ContextSupportsAppr G e' ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_nonce : forall p aid args e' appr_id fwd attrs n,
    canon_ev_rep G e' = nonce_evt n ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    ContextSupportsAppr G e' ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_split : 
    forall p aid args e' l r appr_id fwd attrs,
    canon_ev_rep G e' = split_evt l r ->
    (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs) ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    ContextSupportsAppr G l ->
    ContextSupportsAppr G r ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_asp_unwrap_wrap : 
    forall p p' aid aid' args args' n attrs attrs' e' e'' appr_id,
    canon_ev_rep G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    (asp_types G) ![ aid  ] = Some (ev_arrow UNWRAP attrs) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow (WRAP n) attrs') ->
    (asp_comps G) ![ aid' ] = Some aid ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    ContextSupportsAppr G e' ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e')
| csa_asp_asp : forall p p' aid aid' args args' fwd fwd' attrs attrs' e' e'' appr_id,
    canon_ev_rep G e' = asp_evt p' (asp_paramsC aid' args') e'' ->
    fwd <> UNWRAP ->
    (asp_types G) ![ aid  ] = Some (ev_arrow fwd attrs) ->
    (asp_types G) ![ aid' ] = Some (ev_arrow fwd' attrs') ->
    (asp_comps G) ![ aid ] = Some appr_id ->
    ContextSupportsAppr G e' ->
    ContextSupportsAppr G (asp_evt p (asp_paramsC aid args) e').
Local Hint Constructors ContextSupportsAppr : csa.

Equations? context_supports_appr_type (G : GlobalContext) (e : EvidenceT) 
    : Prop by wf (EvidenceT_depth e) :=
  context_supports_appr_type G mt_evt := True;
  context_supports_appr_type G (nonce_evt n) := True;
  context_supports_appr_type G (left_evt e') := 
    match canon_ev_rep G e' as cer return canon_ev_rep G e' = cer -> _ with
    | split_evt l r => fun Hcer => context_supports_appr_type G l
    | _ => fun _ => False
    end eq_refl;
  context_supports_appr_type G (right_evt e') :=
    match canon_ev_rep G e' as cer return canon_ev_rep G e' = cer -> _ with
    | split_evt l r => fun Hcer => context_supports_appr_type G r
    | _ => fun _ => False
    end eq_refl;
  context_supports_appr_type G (split_evt l r) :=
    context_supports_appr_type G l /\ context_supports_appr_type G r;
  context_supports_appr_type G (asp_evt p (asp_paramsC aid args) e') :=
    match canon_ev_rep G e' as cer return canon_ev_rep G e' = cer -> _ with
    | mt_evt => fun Hcer => 
        (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
        /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id)
    | nonce_evt n => fun Hcer => 
        (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
        /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id)
    | left_evt e'' => fun Hcer => False
    | right_evt e'' => fun Hcer => False
    | split_evt l r => 
      fun Hcer =>
        (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
        /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id)
        /\ context_supports_appr_type G l
        /\ context_supports_appr_type G r
    | asp_evt p' (asp_paramsC aid' args') e'' =>
      fun Hcer =>
        match 
          (asp_types G) ![ aid  ], 
          (asp_types G) ![ aid' ], 
          (asp_comps G) ![ aid' ] 
        with
        | Some (ev_arrow UNWRAP attrs), 
          Some (ev_arrow (WRAP _) attrs'),
          Some appr_id =>
          if dec_eq appr_id aid then
            context_supports_appr_type G e''
          else
            False
        | _, _, _ => (* this is just a generic ASP that we appraise *)
          (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
          /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id)
          /\ context_supports_appr_type G e'
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

Lemma context_support_impl_supports_canon_ev : forall G e,
  context_supports_appr_type G e ->
  context_supports_appr_type G (canon_ev_rep G e).
Proof.
  intros G e.
  induction e; ff.
  - destruct a.
    erewrite context_supports_appr_type_equation_3 in H;
    break_match;
    unfold canon_ev_rep in *; norm; erewrite Heqe0;
    try (
      erewrite context_supports_appr_type_equation_3;
      unfold canon_ev_rep in *;
      eapply normalize_ev_done in Heqe0;
      erewrite Heqe0;
      eauto
    ).
    repeat break_match; subst;
    try (eauto;
      erewrite context_supports_appr_type_equation_3;
      unfold canon_ev_rep in *;
      eapply normalize_ev_done in Heqe0;
      erewrite Heqe0;
      repeat (ff; split)
    ).

  - ff;
    ltac1:( simp context_supports_appr_type in * );
    unfold canon_ev_rep in *;
    break_match; try find_contra; try congruence;
    normer.

  - ff;
    ltac1:( simp context_supports_appr_type in * );
    unfold canon_ev_rep in *;
    break_match; try find_contra; try congruence;
    normer.

  - ff.

    ltac1:( simp context_supports_appr_type in * ).
    ff with a.
    normer.
    unfold canon_ev_rep in *.
    ltac1:( simp context_supports_appr_type in * ).
    ff.
Qed.

(*

Theorem ContextSupportsAppr_impl_context_supports_appr_type : forall G e,
  ContextSupportsAppr G e <-> context_supports_appr_type G e.
Proof.
  split; intros.
  - intros. 
    induction H;
    ltac1:( simp context_supports_appr_type in * ); 
    eauto; Control.enter (fun () => find_rewrite); eauto.
    * split; ff.
    * ff.
      find_eapply_lem_hyp context_support_impl_supports_canon_ev.

      ff.
      find_rewrite.
      erewrite context_supports_appr_type_equation_3 in IHContextSupportsAppr.
      ff; unfold canon_ev_rep in *;
      eapply normalize_ev_done in H;
      norm; Control.enter (fun () => 
        find_rewrite;
        find_injection;
        ltac1:( simp context_supports_appr_type in * );
        ff
      ).
    * repeat find_rewrite;
      destruct fwd; repeat (ff; split).
  - 
    generalizeEverythingElse e.
    induction e; ff.
    * eauto with csa.
    * eauto with csa.
    * ltac1:( simp context_supports_appr_type in * ).
Qed.



  (* match t with
  | mt_evt => True
  | nonce_evt n => True
  | left_evt e' => 
    exists l r, 
      canon_ev_rep G e' = split_evt l r /\
      context_supports_appr_type G l
  | right_evt e' => context_supports_appr_type G e'
  | split_evt l r => context_supports_appr_type G l /\ context_supports_appr_type G r
  | asp_evt p (asp_paramsC aid args) e' =>
      (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
      /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id)
      /\ context_supports_appr_type G e'
  end. *)

Fixpoint context_supports_appr (G : GlobalContext) p e t : Prop :=
  match t with
  | asp APPR => context_supports_appr_type G e
  | asp (ASPC (asp_paramsC aid args)) =>
      context_supports_appr_type G e
      /\ (exists fwd attrs, (asp_types G) ![ aid ] = Some (ev_arrow fwd attrs)) 
      /\ (exists appr_id, (asp_comps G) ![ aid ] = Some appr_id)
  | asp SIG => 
      context_supports_appr_type G e
      /\ (exists sig_appr_id, (asp_comps G) ![ sig_aspid ] = Some sig_appr_id)
  | asp HSH => 
      context_supports_appr_type G e
      /\ (exists hsh_appr_id, (asp_comps G) ![ hsh_aspid ] = Some hsh_appr_id)
  | asp (ENC p') => 
      context_supports_appr_type G e
      /\ (exists enc_appr_id, (asp_comps G) ![ enc_aspid ] = Some enc_appr_id)
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

Lemma supports_implies_appraisable_aux : forall G e,
  context_supports_appr_type G e ->
  forall p,
    exists e'', typeof G p e (asp APPR) e''.
Proof.
  intros G e Hcsat.

  induction e; ff.
  - admit.
  - admit.
  - admit.
  - 

    clear IHe.
    assert (IHe : forall G e',
      EvidenceT_depth e' < EvidenceT_depth e ->
      context_supports_appr_type G e' ->
forall p0 : Plc, exists e'' : EvidenceT, typeof G p0 e' (asp APPR) e''
    ). admit.
    erewrite context_supports_appr_type_equation_4 in Hcsat.
    break_match; try find_contra; try congruence.
    (* erewrite <- Heqcall in *; try find_contra; clear Heqcall. *)
    assert (EvidenceT_depth e0_1 < EvidenceT_depth e) by (
      find_eapply_lem_hyp canon_ev_canonical; ff l
    ).
    pp (IHe _ _ H Hcsat p).
    break_exists.
    eapply tc_left_split in H0.
    break_exists.
    eapply (appr_canon_invariant G p (left_evt (split_evt e0_1 e0_2)) (left_evt e)).
    * unfold canon_ev_rep in *.
      eapply normalize_ev_done in Heqe0 as ?.
      norm.
      find_rewrite.
      ff.
    * eauto.
      
  - 


  ltac1:( funelim (context_supports_appr_type G e) ); intros.
  - norm; eexists; eapply tc_appr_mt; normer.
  - norm; eexists; eapply tc_appr_nonce; normer.
  - break_match; erewrite <- Heqcall in *; clear Heqcall.
    * ff; eexists; eapply tc_appr_asp > [ | normer ];
      unfold canon_ev_rep in *; norm; find_rewrite; ff.
    * ff; eexists; eapply tc_appr_asp > [ | normer ];
      unfold canon_ev_rep in *; norm; find_rewrite; ff.
    * ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + admit.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
      + eexists; eapply tc_appr_asp > [ unfold canon_ev_rep in *; norm; find_rewrite | ]; ff.
    * ff; eexists; eapply tc_appr_asp > [ | normer ];
      Control.enter (fun () => unfold canon_ev_rep in *; norm; find_rewrite; ff).
    * ff; eexists; eapply tc_appr_asp > [ | normer ];
      Control.enter (fun () => unfold canon_ev_rep in *; norm; find_rewrite; ff).
    * ff; eexists; eapply tc_appr_asp > [ | normer ];
      Control.enter (fun () => unfold canon_ev_rep in *; norm; find_rewrite; ff).
  - erewrite <- Heqcall in Hcsat.
    clear Heqcall.
    break_match; try find_contra.
    pp tc_left_split.
    eapply (appr_canon_invariant G p (left_evt (split_evt e1 e2)) (left_evt e')).
    * admit.
    * pp tc_left_split.

    * ff; eexists; eapply tc_appr_mt; normer.
    * ff; eexists; eapply tc_appr_nonce; normer.


  admit.
  admit.

  induction e; intros Hsupp. 

  (* intros G e p Hsupp.
  eapply context_support_impl_supports_canon_ev in Hsupp.

  unfold canon_ev_rep in *.

  generalizeEverythingElse e.
  induction e; ff. *)
  - norm; eexists; eapply tc_appr_mt; normer.
  - norm; eexists; eapply tc_appr_nonce; normer.
  - destruct a.
    erewrite context_supports_appr_type_equation_3 in Hsupp.
    break_match; unfold canon_ev_rep in *;
    repeat break_and; repeat break_exists.
    * eexists; eapply tc_appr_asp; normer.
    * eexists; eapply tc_appr_asp; normer.
    * admit.
    * eexists; eapply tc_appr_asp; normer.
    * eexists; eapply tc_appr_asp; normer.
    * eexists; eapply tc_appr_asp; normer.
  - 
    erewrite context_supports_appr_type_equation_4 in Hsupp.
    break_match; unfold canon_ev_rep in *; try find_contra.

    (* ltac1:( funelim (normalize_ev G e0_1) ). *)
    destruct (normalize_ev G e0_1) eqn:?.
    * eexists; eapply tc_appr_mt; normer.
      eapply normalize_ev_done in Heqe0.
      norm; ff.
    * eexists; eapply tc_appr_nonce; normer.
      eapply normalize_ev_done in Heqe0.
      norm; ff.
    * admit.
    * eexists; eapply tc_appr_nonce; normer.
      eapply normalize_ev_done in Heqe0.
      norm; ff.
    * eexists; eapply tc_appr_nonce; normer.
      eapply normalize_ev_done in Heqe0.
      norm; ff.


    norm.
    break_match.
    * erewrite context_supports_appr_type_equation_3 in Hsupp.
      unfold canon_ev_rep in *.
      let hn := fresh_hyp "Hn" in
      eapply normalize_ev_done in Heqe0 as $hn;
      let hnv := Control.hyp hn in
      erewrite $hnv in Hsupp;
      repeat break_and; repeat break_exists; eexists;
      eapply tc_appr_asp; normer.
    * erewrite context_supports_appr_type_equation_3 in Hsupp.
      unfold canon_ev_rep in *.
      let hn := fresh_hyp "Hn" in
      eapply normalize_ev_done in Heqe0 as $hn;
      let hnv := Control.hyp hn in
      erewrite $hnv in Hsupp;
      repeat break_and; repeat break_exists; eexists;
      eapply tc_appr_asp; normer.
    * admit.
    * erewrite context_supports_appr_type_equation_3 in Hsupp.
      unfold canon_ev_rep in *.
      let hn := fresh_hyp "Hn" in
      eapply normalize_ev_done in Heqe0 as $hn;
      let hnv := Control.hyp hn in
      erewrite $hnv in Hsupp;
      repeat break_and; repeat break_exists; eexists;
      eapply tc_appr_asp; normer.
    * erewrite context_supports_appr_type_equation_3 in Hsupp.
      unfold canon_ev_rep in *.
      let hn := fresh_hyp "Hn" in
      eapply normalize_ev_done in Heqe0 as $hn;
      let hnv := Control.hyp hn in
      erewrite $hnv in Hsupp;
      repeat break_and; repeat break_exists; eexists;
      eapply tc_appr_asp; normer.
    * erewrite context_supports_appr_type_equation_3 in Hsupp.
      unfold canon_ev_rep in *.
      let hn := fresh_hyp "Hn" in
      eapply normalize_ev_done in Heqe0 as $hn;
      let hnv := Control.hyp hn in
      erewrite $hnv in Hsupp;
      repeat break_and; repeat break_exists; eexists;
      eapply tc_appr_asp; normer.
  - norm.
    break_match;
    try (
      erewrite context_supports_appr_type_equation_4 in Hsupp;
      unfold canon_ev_rep in *;
      let hn := fresh_hyp "Hn" in
      eapply normalize_ev_done in Heqe0 as $hn;
      let hnv := Control.hyp hn in
      erewrite $hnv in Hsupp;
      try find_contra
    ).

    destruct (normalize_ev G e0_1) eqn:?.
    * eapply normalize_ev_done in Heqe0 as ?; normer.
      eexists; eapply tc_appr_mt; normer.
    * eapply normalize_ev_done in Heqe0 as ?; normer.
      eexists; eapply tc_appr_nonce; normer.
    * destruct a. 

      eapply normalize_ev_done in Heqe0 as ?; normer.
      norm.
      break_match;
      try (
        find_injection;
        erewrite context_supports_appr_type_equation_3 in Hsupp;
        unfold canon_ev_rep in *;
        find_rewrite;
        repeat break_and; repeat break_exists;
        eexists; eapply tc_appr_asp; normer; fail
      ).
      + repeat break_match; subst;
        try (
          find_injection;
          erewrite context_supports_appr_type_equation_3 in Hsupp;
          unfold canon_ev_rep in *;
          repeat find_rewrite;
          repeat break_and; repeat break_exists;
          eexists; eapply tc_appr_asp; normer
        ).

        eapply canon_ev_canonical in Heqe2.
        ff l.
    * eapply normalize_ev_done in Heqe0 as ?; normer.
      erewrite context_supports_appr_type_equation_4 in Hsupp.
      unfold canon_ev_rep in *.
      ff.

      norm.
      find_rewrite.
      subst.
      repeat (find_eapply_lem_hyp canon_ev_canonical).
      ff l.
    * eapply normalize_ev_done in Heqe0 as ?; normer.
      erewrite context_supports_appr_type_equation_5 in Hsupp.
      unfold canon_ev_rep in *.
      ff.

      norm.
      find_rewrite.
      subst.
      repeat (find_eapply_lem_hyp canon_ev_canonical).
      ff l.
    * 
      eapply normalize_ev_done in Heqe0 as ?; normer.
      erewrite context_supports_appr_type_equation_6 in Hsupp.
      unfold canon_ev_rep in *.
      ff.
      eexists.
      eapply tc_appr_split.
      normer.


      norm.
      find_rewrite.
      subst.
      repeat (find_eapply_lem_hyp canon_ev_canonical).
      ff l.
    * 

      normer.
      eapply normalize_ev_done in Heqe0 as ?.
      norm.
      find_rewrite.
      admit.
    * admit.
    * admit.
  - admit.
  - norm.
    ltac1:( simp context_supports_appr_type in * ).
    break_and.
    find_eapply_lem_hyp IHe1; ff.
    find_eapply_lem_hyp IHe2; ff.
    edestruct (tc_left_split _ _ _ _ e2 H).
    edestruct (tc_right_split _ _ _ _ e1 H0).
    eexists.
    eapply tc_appr_split; normer.
Admitted.

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

(* Compute (normalize_ev (Build_GlobalContext _ [] []) (split_evt (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) (nonce_evt 3))). *)

Example normalize_provenance :
  provenance (Build_GlobalContext _ [] []) (split_evt (nonce_evt 1) (nonce_evt 3)) 
    (split_evt (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) (nonce_evt 3)).
Proof.
  eauto with prov.
Qed.

Lemma canon_ev_rep_provenance : forall G e,
  provenance G (canon_ev_rep G e) e.
Proof.
  intros.
  unfold canon_ev_rep.
  induction e; norm; prover.

  destruct a; norm; prover.
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
  - invc H; ff a;
    find_eapply_lem_hyp provenance_trans; ff.
  - invc H; ff a; eauto using provenance.
  - invc H; ff a; eauto using provenance.
Qed.

(* Lemma context_supports_appr_type_iff_wf_EvidenceT : forall G e,
  context_supports_appr_type G e <-> wf_EvidenceT G e.
Proof.
  unfold wf_EvidenceT.
  split; intros.
  - admit.
  - destruct H.
    induction H.
    * ltac1:( simp context_supports_appr_type in * ); ff.
    * ltac1:( simp context_supports_appr_type in * ); ff.
    * ltac1:( simp context_supports_appr_type in * ); ff.
    * ltac1:( simp context_supports_appr_type in * ); ff.
    * ltac1:( simp context_supports_appr_type in * ); ff.
    * ltac1:( simp context_supports_appr_type in * ).
      find_rewrite.
      normer.
      split; ff.
      eauto.
    * 
      normer.
    induction H. *)

(*

(* Major Theorem: Appraisability *)
Theorem well_typed_appraisable : forall G t e e' p,
  typeof G p e t e' ->
  context_supports_appr G p e t ->
  exists e'', typeof G p e' (asp APPR) e''.
Proof.
  induction t; intros.
  - destruct a; normer.
    * invc H.
    * inv H.
      + find_rewrite.
        find_injection.
        admit.
      + find_rewrite.
        find_injection.
        admit.
      + admit.
    * inv H.
      eexists.
      eapply tc_appr_asp; normer.
      + 
      destruct (normalize_ev G e) eqn:?.
      try ( eexists; eapply tc_appr_asp; normer; fail ).
      ff.
      eexists.
      eapply tc_appr_asp.
      normer.
      + 
        erewrite equiv_preserves_denotation_size in *.
        erewrite Heqe0 in *.
        invc H6; ff.
        ** admit.
        ** admit.
        ** admit.
        ** 
          unfold canon_ev_rep in *.
          eapply normalize_ev_done in Heqe0.
          normer.

        destruct (normalize_ev G (asp_evt p (asp_paramsC a0 a1) e)) eqn:?.
        ** eexists; eapply tc_appr_mt; normer.
        ** eexists; eapply tc_appr_nonce; normer.
        ** 
          eexists; eapply tc_appr_nonce; normer.
        eexists.
        eapply tc_appr_asp; normer.
        admit.
      eexists.
        eapply tc_appr_asp; normer.
        admit.
      + admit.
    * invc H.
      unfold sig_params in *.
      destruct (normalize_ev G e) eqn:?;
      eexists; eapply tc_appr_asp; normer.
    * invc H.
      unfold hsh_params in *.
      destruct (normalize_ev G e) eqn:?;
      eexists; eapply tc_appr_asp; normer.
    * admit.
    * invc H.
      unfold enc_params in *.
      destruct (normalize_ev G e) eqn:?;
      eexists; eapply tc_appr_asp; normer.
  - invc H.
    ff.
    eapply IHt in H6; ff.
    find_eapply_lem_hyp typeof_place_irrel.
    ff.
    smper.
  - invc H; ff.
    pp (typeof_deterministic _ _ _ _ _ _ H0 H5); ff.
  - invc H; ff.
    find_eapply_lem_hyp IHt1; ff.
    find_eapply_lem_hyp IHt2; ff.
    clear IHt1 IHt2 t1 t2 e H H0.
    ff.
    eapply tc_left_split in H1; ff.
    eapply tc_right_split in H2; ff.
    eexists.
    eapply tc_appr_split; normer.
  - invc H; ff.
    find_eapply_lem_hyp IHt1; ff.
    find_eapply_lem_hyp IHt2; ff.
    clear IHt1 IHt2 t1 t2 e H H0.
    ff.
    eapply tc_left_split in H1; ff.
    eapply tc_right_split in H2; ff.
    eexists.
    eapply tc_appr_split; normer. *)

*)