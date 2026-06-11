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

(** [ASP_ID] and [Arg] are all identifiers and parameters to ASP terms
    [ASP_ID] identifies the procedure invoked.
    [Arg] represents a custom argument for a given ASP 
          (defined and interpreted per-scenario/implementaiton).
*)
Definition ASP_ID: Set := ID_Type.
Definition ASP_ARGS := JSON. (* Map string string. *)

(** Grouping ASP parameters into one constructor *)
Inductive ASP_PARAMS: Type :=
| asp_paramsC: ASP_ID -> ASP_ARGS -> ASP_PARAMS.

Definition pos_nat := { n : nat | 0 < n }.

(** EvidenceT type signatures 

    FWD indicates how the output EvidenceT is constructed from the input EvidenceT.
    EvInSig indicates whether the ASP requires ALL or NONE of the input EvidenceT.
    Attr is a list of attributes associated with the ASP's evidence transformation.
*)

Inductive EvIn :=
| InAll : EvIn
| InNone : EvIn.


Inductive EvCombSig :=
(* implicitly a Replace must consume all! *)
| REPLACE (n : pos_nat)
(* a wrap must also consume all *)
| WRAP (n : pos_nat)
(* unwrap better consume all *)
| UNWRAP
(* extend could possible consume 
None (i.e. it is just a pure measurement)
or All (i.e. it extends existing evidence) 
*)
| EXTEND (n : pos_nat) (e : EvIn).

Inductive Attr :=
(** [Reconstr] means the evidence yielded by this is "reconstructable" from a golden value *)
| Reconstr.

Inductive EvSig :=
| ev_arrow : EvCombSig -> list Attr -> EvSig.

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

Definition ASP_Type_Env `{DecEq ASP_ID} := Map ASP_ID EvSig.
Definition ASP_Compat_MapT `{DecEq ASP_ID} := Map ASP_ID ASP_ID.

Record GlobalContext `{DecEq ASP_ID} := {
  asp_types: ASP_Type_Env;
  asp_comps: ASP_Compat_MapT
}.

(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)

Inductive ev_path :=
| left_path
| right_path
| both_paths.

(** Main Copland phrase datatype definition.
        A term is either an atomic ASP (Attestation Service Provider), 
        a remote call (att), a sequence of terms with data a dependency (lseq),
        a sequence of terms with no data dependency, or parallel terms. *)
Inductive Term :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: ev_path -> Term -> Term -> Term
| bpar: ev_path -> Term -> Term -> Term.

Definition EvidenceT_depth : EvidenceT -> nat :=
  fix F e :=
  match e with
  | mt_evt => 0
  | nonce_evt _ => 1
  | asp_evt _ _ e' => 1 + F e'
  | left_evt e' => 1 + F e'
  | right_evt e' => 1 + F e'
  | split_evt e1 e2 => 1 + max (F e1) (F e2)
  end.


(* [et_size] and [wf_Evidence] now live in [Normalize.v] (downstream of
   [normalize_ev]): [et_size] is defined over the canonical evidence form, which
   has already resolved projections and matched WRAP/UNWRAP pairs. *)
Close Scope string_scope.

(** Raw EvidenceT representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

Fixpoint peel_n_rawev (n : nat) (ls : RawEv) : Result (RawEv * RawEv) string :=
  match n with
  | 0 => res ([], ls)
  | S n' =>
    match ls with
    | [] => err errStr_peel_n_am
    | x :: ls' =>
      match peel_n_rawev n' ls' with
      | err e => err e
      | res (ls1, ls2) => res (x :: ls1, ls2)
      end
    end
  end.

Lemma peel_n_rawev_result_spec : forall n ls ls1 ls2,
  peel_n_rawev n ls = res (ls1, ls2) ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; ff with u, a.
Qed.

Lemma peel_n_rawev_none_spec : forall n ls e,
  peel_n_rawev n ls = err e ->
  length ls < n.
Proof.
  induction n; ff with u, a, l.
Qed.

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
Notation "x < y" := (bseq x y) (in custom copland_entry at level 70, right associativity).
Notation "x ~ y" := (bpar x y) (in custom copland_entry at level 70, right associativity).
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