(** Basic definitions for Copland terms, Core terms, 
   EvidenceT Types, and Copland events. *)

(*
   These definitions have been adapted from an earlier version, archived 
   here:  https://ku-sldg.github.io/copland/resources/coplandcoq.tar.gz 

   with License:

LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)


From RocqJSON Require Export JSON.
From CoplandSpec Require Export BS ID_Type ErrorMessages.
From RocqCandy Require Import ResultMonad Maps.
Import ResultNotation.

(** * Terms and EvidenceT *)

(** [Plc] represents a place (or attestation domain). *)
Definition Plc: Set := ID_Type.
(** [N_ID] represents a nonce identifier.  *)
Definition N_ID: Set := nat.
(** [Event_ID] represents Event identifiers *)
Definition Event_ID: Set := nat.

(** [ASP_ID], [TARG_ID], and [Arg] are all identifiers and parameters to ASP terms
    [ASP_ID] identifies the procedure invoked.
    [TARG_ID] identifies the target (when a target makes sense).
    [Arg] represents a custom argument for a given ASP 
          (defined and interpreted per-scenario/implementaiton).
*)
Definition ASP_ID: Set := ID_Type.
Definition ASP_Compat_MapT := Map ASP_ID ASP_ID.
Definition ASP_ARGS := JSON. (* Map string string. *)

Definition TARG_ID: Set := ID_Type.

(** Grouping ASP parameters into one constructor *)
Inductive ASP_PARAMS: Type :=
| asp_paramsC: ASP_ID -> ASP_ARGS -> Plc -> TARG_ID -> ASP_PARAMS.

(* Definition eqb_ASP_PARAMS `{EqClass ASP_ID, EqClass ASP_ARGS, EqClass Plc, EqClass TARG_ID}
    (a1 a2 : ASP_PARAMS) : bool :=
  let '(asp_paramsC a1 la1 p1 t1) := a1 in
  let '(asp_paramsC a2 la2 p2 t2) := a2 in
  (eqb a1 a2) && (eqb la1 la2) && (eqb p1 p2) && (eqb t1 t2).

Global Instance  EqClass_ASP_PARAMS `{EqClass ASP_ID, EqClass ASP_ARGS, EqClass Plc, EqClass TARG_ID} : EqClass ASP_PARAMS.
eapply Build_EqClass with (eqb := eqb_ASP_PARAMS).
induction x; destruct y; ff;
repeat rewrite Bool.andb_true_iff in *; ff;
repeat rewrite eqb_eq in *; ff.
Defined. *)

Inductive FWD :=
| REPLACE
| WRAP
| UNWRAP
| EXTEND.

Inductive EvInSig :=
| InAll : EvInSig
| InNone : EvInSig.

Inductive EvOutSig :=
| OutN : nat -> EvOutSig
| OutUnwrap : EvOutSig.

Inductive EvSig :=
| ev_arrow : FWD -> EvInSig -> EvOutSig -> EvSig.

(** The structure of EvidenceT. 

    mt_evt:  Empty EvidenceT 
    nn:  Nonce EvidenceT (with an ID)
    uu:  ASP EvidenceT bundle
    ss:  EvidenceT pairing (composition)
*)
Inductive EvidenceT :=
| mt_evt      : EvidenceT
| nonce_evt   : N_ID -> EvidenceT
| asp_evt     : Plc -> ASP_PARAMS -> EvidenceT -> EvidenceT
| left_evt    : EvidenceT -> EvidenceT
| right_evt   : EvidenceT -> EvidenceT
| split_evt   : EvidenceT -> EvidenceT -> EvidenceT.

(** Evidene routing types:  
      ALL:   pass through all EvidenceT
      NONE   pass through empty EvidenceT
*)
Inductive SP: Set :=
| ALL
| NONE.

(** Primitive Copland phases 

    NULL:    Empty out EvidenceT (optionally with a strong "zeroize" effect)
    ASPC sp fwd ps:    
        Arbitrary ASPs:
          sp indicates passing ALL or NONE as input EvidenceT.
          fwd indicates how to extend output EvidenceT.
          ps indicates the asp parameters structure
    SIG:     Signature primitive
    HSH:     Hash primitive 
    APPR:    Appraisal primitive
    ENC q:   Encryption primitive using public key associated with place q.
*)
Inductive ASP :=
| NULL: ASP
| ASPC: ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP
| APPR : ASP
| ENC: Plc -> ASP.

Definition ASP_Type_Env := Map ASP_ID EvSig.

Record GlobalContext := {
  asp_types: ASP_Type_Env;
  asp_comps: ASP_Compat_MapT
}.

(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)
Definition Split: Set := (SP * SP).

(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)

(** Main Copland phrase datatype definition.
        A term is either an atomic ASP (Attestation Service Provider), 
        a remote call (att), a sequence of terms with data a dependency (lseq),
        a sequence of terms with no data dependency, or parallel terms. *)
Inductive Term :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

Definition EvidenceT_depth : EvidenceT -> nat :=
  fix F e :=
  match e with
  | mt_evt => 0
  | nonce_evt _ => 0
  | asp_evt _ _ e' => 1 + F e'
  | left_evt e' => 1 + F e'
  | right_evt e' => 1 + F e'
  | split_evt e1 e2 => 1 + max (F e1) (F e2)
  end.


Inductive EvTrails :=
| Trail_UNWRAP : ASP_ID -> EvTrails
| Trail_LEFT  : EvTrails
| Trail_RIGHT : EvTrails.

Definition apply_to_evidence_below {A} `{DecEq ASP_ID} (G : GlobalContext) (f : EvidenceT -> A)
    : list EvTrails -> EvidenceT -> Result A string :=
  fix F trails e :=
  match trails with
  | nil => (* no further trail to follow! *)
    res (f e)
  | trail :: trails' =>
    match e with
    | mt_evt => err err_str_no_evidence_below
    | nonce_evt _ => err err_str_no_evidence_below

    | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
      match (lookup top_id (asp_types G)) with
      | None => err err_str_asp_no_type_sig
      | Some (ev_arrow UNWRAP in_sig out_sig) =>
        (* we are UNWRAP, so add to trail and continue *)
        F ((Trail_UNWRAP top_id) :: trails) et'

      | Some (ev_arrow WRAP in_sig out_sig) =>
        (* we are a WRAP, better be the case we are looking for one *)
        match trail with
        | Trail_UNWRAP unwrap_id => 
          match (lookup top_id (asp_comps G)) with
          | None => err err_str_asp_no_compat_appr_asp
          | Some test_unwrapping_id =>
            if (dec_eq test_unwrapping_id unwrap_id) 
            then (* they are compatible so we can continue on smaller *)
              F trails' et'
            else (* they are not compatible, this is a massive error *)
              err err_str_wrap_asp_not_duals
          end
        | _ => err err_str_trail_mismatch
        end

      | Some (ev_arrow _ in_sig out_sig) =>
        (* we are neither WRAP or UNWRAP, so this is an error *)
        err err_str_asp_at_bottom_not_wrap
      end
    | left_evt et' => 
      (* we are pushing on a new left *)
      F (Trail_LEFT :: trails) et'

    | right_evt et' => 
      (* we are pushing on a new right *)
      F (Trail_RIGHT :: trails) et'

    | split_evt e1 e2 => 
      (* we are a split, depending on trail we will either go 
      left or right and continue *)
      match trail with
      | Trail_LEFT => F trails' e1
      | Trail_RIGHT => F trails' e2
      | _ => err err_str_trail_mismatch
      end
    end
  end.

Inductive Evidence_Subterm_path G e' : list EvTrails -> EvidenceT -> Prop :=
| esp_empty_trail : Evidence_Subterm_path G e' nil e'

| esp_unwrap : forall p in_sig out_sig e'' trails aid args targp targ,
  lookup aid (asp_types G) = Some (ev_arrow UNWRAP in_sig out_sig) ->
  Evidence_Subterm_path G e' ((Trail_UNWRAP aid) :: trails) e'' ->
  trails <> nil ->
  Evidence_Subterm_path G e' trails (asp_evt p (asp_paramsC aid args targp targ) e'')

| esp_wrap : forall p in_sig out_sig e'' trails aid args targp targ aid',
  lookup aid (asp_types G) = Some (ev_arrow WRAP in_sig out_sig) ->
  lookup aid (asp_comps G) = Some aid' ->
  Evidence_Subterm_path G e' trails e'' ->
  Evidence_Subterm_path G e' ((Trail_UNWRAP aid') :: trails) (asp_evt p (asp_paramsC aid args targp targ) e'')

| esp_left : forall e'' trails,
  Evidence_Subterm_path G e' (Trail_LEFT :: trails) e'' ->
  trails <> nil ->
  Evidence_Subterm_path G e' trails (left_evt e'')

| esp_right : forall e'' trails,
  Evidence_Subterm_path G e' (Trail_RIGHT :: trails) e'' ->
  trails <> nil ->
  Evidence_Subterm_path G e' trails (right_evt e'')

| esp_split_l : forall e1 e2 trails,
  Evidence_Subterm_path G e' trails e1 ->
  Evidence_Subterm_path G e' (Trail_LEFT :: trails) (split_evt e1 e2)

| esp_split_r : forall e1 e2 trails,
  Evidence_Subterm_path G e' trails e2 ->
  Evidence_Subterm_path G e' (Trail_RIGHT :: trails) (split_evt e1 e2).

Definition Evidence_Subterm_path_fix G e' : list EvTrails -> EvidenceT -> Prop :=
  fix F trails e :=
  match trails with
  | nil => e' = e
  | trail :: trails' =>
    match e with
    | mt_evt => False
    | nonce_evt _ => False

    | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
      match (lookup top_id (asp_types G)) with
      | None => False
      | Some (ev_arrow UNWRAP in_sig out_sig) =>
        (* we are UNWRAP, so add to trail and continue *)
        F ((Trail_UNWRAP top_id) :: trails) et'

      | Some (ev_arrow WRAP in_sig out_sig) =>
        (* we are a WRAP, better be the case we are looking for one *)
        match trail with
        | Trail_UNWRAP unwrap_id => 
          match (lookup top_id (asp_comps G)) with
          | None => False
          | Some test_unwrapping_id =>
            if (dec_eq test_unwrapping_id unwrap_id) 
            then (* they are compatible so we can continue on smaller *)
              F trails' et'
            else (* they are not compatible, this is a massive error *)
              False
          end
        | _ => False
        end

      | Some (ev_arrow _ in_sig out_sig) =>
        (* we are neither WRAP or UNWRAP, so this is an error *)
        False
      end
    | left_evt et' => 
      (* we are pushing on a new left *)
      F (Trail_LEFT :: trails) et'

    | right_evt et' => 
      (* we are pushing on a new right *)
      F (Trail_RIGHT :: trails) et'

    | split_evt e1 e2 => 
      (* we are a split, depending on trail we will either go 
      left or right and continue *)
      match trail with
      | Trail_LEFT => F trails' e1
      | Trail_RIGHT => F trails' e2
      | _ => False
      end
    end
  end.

Lemma Evidence_Subterm_path_same : forall G l e e1 e2,
  Evidence_Subterm_path G e1 l e ->
  Evidence_Subterm_path G e2 l e ->
  e1 = e2.
Proof.
  intros.
  prep_induction H.
  induction H; intros; try (inv H0; eauto; congruence).
  - inv H2; eauto; try congruence.
  - inv H2; eauto; try congruence.
  - inv H1; eauto; try congruence.
  - inv H1; eauto; try congruence.
Qed.

Definition Evidence_Subterm G e' : EvidenceT -> Prop :=
  fix F e :=
  match e with
  (* sort of a hack here, the terminals are always subterms!? *)
  | mt_evt => False
  | nonce_evt _ => False
  | asp_evt _ (asp_paramsC asp_id _ _ _) e'' => 
    match (lookup asp_id (asp_types G)) with
    | None => False
    | Some (ev_arrow UNWRAP in_sig out_sig) => 
      apply_to_evidence_below G F [Trail_UNWRAP asp_id] e'' <?> False
    | Some (ev_arrow _ in_sig out_sig) => 
      e' = e''
    end
  | left_evt e'' => 
    apply_to_evidence_below G F [Trail_LEFT] e'' <?> False
  | right_evt e'' => 
    apply_to_evidence_below G F [Trail_RIGHT] e'' <?> False
  | split_evt e1 e2 => 
    e' = e1 \/ e' = e2 \/ F e1 \/ F e2
  end.

Lemma apply_to_evidence_below_res_spec : forall {A} G (f : _ -> A) e v l,
  apply_to_evidence_below G f l e = res v ->
  (exists e', Evidence_Subterm_path G e' l e /\ f e' = v).
Proof.
  induction e; simpl in *; intros; intuition; ff u.
  all: eauto using Evidence_Subterm_path; ff a.
  - exists x; split; eauto; eapply esp_wrap; eauto.
  - exists x; split; eauto; eapply esp_unwrap; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_left; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_right; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_split_l; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_split_r; eauto;
    intros HC; invc HC; eauto.
Qed.

Lemma apply_to_evidence_below_nil : forall A G (f : _ -> A) e v,
  apply_to_evidence_below G f nil e = res v ->
  f e = v.
Proof.
  destruct e; ff.
Qed.

Lemma apply_to_evidence_below_res : forall {A} G (fn1 : _ -> A) e l r,
  apply_to_evidence_below G fn1 l e = res r ->
  (forall {B} (fn2 : _ -> B),
    exists r', apply_to_evidence_below G fn2 l e = res r').
Proof.
  induction e; ff u.
Qed.

Lemma apply_to_evidence_below_errs_det : forall {A B} G (fn1 : _ -> A) (fn2 : _ -> B) e l r1 r2,
  apply_to_evidence_below G fn1 l e = err r1 ->
  apply_to_evidence_below G fn2 l e = err r2 ->
  r1 = r2.
Proof.
  induction e; ff u.
Qed.

Lemma evidence_subterm_path_nil : forall G e e',
  Evidence_Subterm_path G e' nil e ->
  e = e'.
Proof.
  intros; 
  prep_induction H; induction H; 
  intros; eauto; try congruence; ff.
Qed.

Lemma evidence_subterm_path_depth : forall G h t e e',
  Evidence_Subterm_path G e' (h :: t) e ->
  EvidenceT_depth e' < EvidenceT_depth e.
Proof.
  intros.
  prep_induction H.
  induction H; intros; try congruence; subst; ff u, l;
  destruct t >
  [ destruct trails; ff; find_eapply_lem_hyp evidence_subterm_path_nil; ff l
  |
    find_inversion; pp (IHEvidence_Subterm_path _ _ eq_refl); ff l ].
Qed.

Theorem Evidence_subterm_path_Ind_special G (P : EvidenceT -> Prop)
  (f_mt : P mt_evt)
  (f_nonce : forall n, P (nonce_evt n))
  (f_subterm_asp_nowrap : forall p aid args targp targ e t isig osig,
    t <> UNWRAP ->
    lookup aid (asp_types G) = Some (ev_arrow t isig osig) ->
    P e -> 
    P (asp_evt p (asp_paramsC aid args targp targ) e))
  (f_subterm_asp : forall p aid args targp targ e isig osig, 
    lookup aid (asp_types G) = Some (ev_arrow UNWRAP isig osig) ->
    (forall l e', Evidence_Subterm_path G e' (Trail_UNWRAP aid :: l) e -> P e') ->
    P (asp_evt p (asp_paramsC aid args targp targ) e))
  (f_subterm_asp_none : forall p aid args targp targ e,
    lookup aid (asp_types G) = None ->
    P (asp_evt p (asp_paramsC aid args targp targ) e))
  (f_subterm_left : forall e, 
    (forall e' l, Evidence_Subterm_path G e' (Trail_LEFT :: l) e -> P e') -> P (left_evt e))
  (f_subterm_right : forall e, 
    (forall e' l, Evidence_Subterm_path G e' (Trail_RIGHT :: l) e -> P e') -> P (right_evt e))
  (f_split : forall e1 e2, P e1 -> P e2 -> P (split_evt e1 e2))
  : forall e, P e.
Proof.
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    intros x F; destruct x eqn:?; eauto.
    - destruct a.
      destruct (lookup a (asp_types G)) eqn:?; eauto;
      destruct e0, f; eauto.
      * eapply f_subterm_asp_nowrap; eauto; congruence.
      * eapply f_subterm_asp_nowrap; eauto; congruence.
      * eapply f_subterm_asp; eauto; intros.
        eapply F.
        find_eapply_lem_hyp evidence_subterm_path_depth; eauto.
        simpl in *; lia.
      * eapply f_subterm_asp_nowrap; eauto; congruence.
      (* eapply f. *)
      (* ff; try (exfalso; eauto; fail). *)
      (* eapply f_subterm; intros;
      ff; try (exfalso; eauto; fail).
      clear f_subterm f_mt f_split f_nonce.
      induction l.
      * destruct e' eqn:?; simpl in *; eexists; 
        split; try reflexivity. *)
      (* eapply F.
      eapply apply_to_evidence_below_res with (fn2 := id) in Heqr as ?. *)
    - 
      eapply f_subterm_left; intros.
      eapply F.
        find_eapply_lem_hyp evidence_subterm_path_depth; eauto.
        simpl in *; lia.
      (* eapply f_subterm; intros;
      ff; try (exfalso; eauto; fail). *)
      (* eapply F. *)
    - 
      eapply f_subterm_right; intros.
      eapply F.
        find_eapply_lem_hyp evidence_subterm_path_depth; eauto.
        simpl in *; lia.
      (* eapply f_subterm; intros;
      ff; try (exfalso; eauto; fail). *)
      (* eapply F. *)
    - eapply f_split; eapply F;
      simpl in *; try lia.
  } 
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.

(**  Calculate the size of an EvidenceT type *)
Definition et_size (G : GlobalContext) : EvidenceT -> Result nat string :=
  fix F e :=
  match e with
  | mt_evt=> res 0
  | nonce_evt _ => res 1
  | asp_evt p par e' =>
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (lookup asp_id (asp_types G)) with
    | None => err err_str_asp_no_type_sig
    | Some (ev_arrow fwd in_sig out_sig) =>
      match fwd with
      | REPLACE => 
        (* we are replacing, so just the output *)
        match out_sig with
        | OutN n => res n
        | OutUnwrap => err err_str_cannot_have_outwrap
        end
      | WRAP => 
        (* we are wrapping, so just the output *)
        match out_sig with
        | OutN n => res n
        | OutUnwrap => err err_str_cannot_have_outwrap 
        end
      | UNWRAP => 
        (* we are unwrapping, so we are the size of the previous input *)
        match out_sig with
        | OutN n => err err_str_unwrap_must_have_outwrap
        | OutUnwrap => 
          n' <- apply_to_evidence_below G F [Trail_UNWRAP asp_id] e' ;;
          n'
        end
      | EXTEND =>
        match out_sig with
        | OutN n => 
          n' <- F e' ;;
          res (n + n')
        | OutUnwrap => err err_str_cannot_have_outwrap 
        end
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
    res (s1 + s2)
  end.
Close Scope string_scope.

(** Raw EvidenceT representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

(**  Type-Tagged Raw EvidenceT representation.  Used as the internal EvidenceT
     type managed by the CVM to track EvidenceT contents and its structure. *)
Inductive Evidence :=
| evc: RawEv -> EvidenceT -> Evidence.

Definition mt_evc: Evidence := (evc [] mt_evt).

Definition get_et (e:Evidence) : EvidenceT :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:Evidence): list BS :=
  match e with
  | evc ls _ => ls
  end.

(** A "well-formed" Evidence value is where the length of its raw EvidenceT portion
  has the proper size (calculated over the EvidenceT Type portion). *)
Inductive wf_Evidence : GlobalContext -> Evidence -> Prop :=
| wf_Evidence_c: forall (ls:RawEv) et G n,
    List.length ls = n ->
    et_size G et = res n ->
    wf_Evidence G (evc ls et).

Inductive CopPhrase :=
| cop_phrase : Plc -> EvidenceT -> Term -> CopPhrase.

(** Abstract Location identifiers used to aid in management and execution 
    of parallel Copland phrases. *)
Definition Loc: Set := nat.
Definition Locs: Set := list Loc.

(* Adapted from Imp language Notation in Software Foundations (Pierce) *)
Declare Custom Entry copland_entry.
Declare Scope cop_ent_scope.
Notation "<{ e }>" := e (at level 0, e custom copland_entry at level 99) : cop_ent_scope.
Notation "( x )" := x (in custom copland_entry, x at level 99) : cop_ent_scope.
Notation "x" := x (in custom copland_entry at level 0, x constr at level 0) : cop_ent_scope.
(* Branches*)
Notation "x -<- y" := (bseq (NONE, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +<- y" := (bseq (ALL, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -<+ y" := (bseq (NONE, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +<+ y" := (bseq (ALL, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -~- y" := (bpar (NONE, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +~- y" := (bpar (ALL, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -~+ y" := (bpar (NONE, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +~+ y" := (bpar (ALL, ALL) x y) (in custom copland_entry at level 70, right associativity).
(* ARROW sequences *)
Notation "x -> y" := (lseq x y) (in custom copland_entry at level 99, right associativity).
(* ASP's *)
Notation "!" := (asp SIG) (in custom copland_entry at level 98).
Notation "#" := (asp HSH) (in custom copland_entry at level 98).
Notation "* p" := (asp (ENC p)) (in custom copland_entry at level 98).
Notation "'{}'" := (asp NULL) (in custom copland_entry at level 98).
(* TODO: Surely we need something more robust than they are ALL EXTD 1, but uhhhh *)
Notation "'<<' x y z '>>'" := (asp (ASPC (asp_paramsC x (JSON_Object []) y z))) 
                      (in custom copland_entry at level 98).


(* @ plc phrase *)
Notation "@ p [ ph ]" := (att p ph) (in custom copland_entry at level 50).