From CoplandSpec Require Import Term_Defs_Core Term_Defs_Core_Typeclasses.
From Equations Require Import Equations.

Fixpoint evidence_measure (e : EvidenceT) : nat :=
  match e with
  | mt_evt => 0
  | nonce_evt _ => 1
  | asp_evt _ _ e' => 1 + evidence_measure e'
  | left_evt e' => 1 + evidence_measure e'
  | right_evt e' => 1 + evidence_measure e'
  | split_evt e1 e2 => 1 + max (evidence_measure e1) (evidence_measure e2)
  end.

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
  evidence_measure e2 < evidence_measure e1.
Proof.
  intros.
  induction H; simpl; ff l.
Qed.

Equations? normalize_ev (G : GlobalContext) (e : EvidenceT) 
    : { e' : EvidenceT | evidence_measure e' <= evidence_measure e }
    by wf (evidence_measure e) :=
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

Example test_normalize_ev : forall G,
  exists He, normalize_ev G (left_evt (split_evt (nonce_evt 1) (nonce_evt 2))) = exist _ (nonce_evt 1) He.
Proof.
  intros.
  eexists.
  ltac1:(simp normalize_ev).
  reflexivity.
Qed.

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
  evidence_measure e' <= evidence_measure e.
Proof.
  unfold canon_ev_rep.
  intros.
  destruct (normalize_ev G e); ff.
Qed.

Lemma equiv_impl_canon_ev_rep : forall G e1 e2,
  Evidence_Equiv G e1 e2 ->
  canon_ev_rep G e1 = canon_ev_rep G e2.
Proof.
  intros.
  unfold Evidence_Equiv, canon_ev_rep in *.
  ff.
Qed.

Theorem canon_ev_rep_correct : forall G e,
  exists! e', canon_ev_rep G e = e'.
Proof.
  unfold canon_ev_rep, unique.
  eexists.
  ff.
Qed.


