From RocqCandy Require Import All.

From CoplandSpec Require Import Term_Defs_Core Prelude.

Global Instance EqClass_ASP_PARAMS `{EqClass json} : EqClass ASP_PARAMS.
refine (Build_EqClass _ 
  (fun '(asp_paramsC a1 la1 p1 t1) '(asp_paramsC a2 la2 p2 t2) => 
    (eqb a1 a2) && (eqb la1 la2) && (eqb p1 p2) && (eqb t1 t2)
  ) 
  (fun '(asp_paramsC a1 la1 p1 t1) '(asp_paramsC a2 la2 p2 t2) => _)
).
eq_crush.
Defined.

Global Instance EqClass_ASP `{EqClass ASP_PARAMS, EqClass Plc}: EqClass ASP.
refine (Build_EqClass _ 
  (fun a1 a2 =>
    match a1, a2 with
    | NULL, NULL => true
    | (ASPC par1), (ASPC par2) => eqb par1 par2
    | SIG, SIG => true
    | HSH, HSH => true
    | APPR, APPR => true
    | ENC p1, ENC p2 => eqb p1 p2
    | _, _ => false
    end
  ) 
  (fun a1 a2 => _)
).
destruct a1, a2; ff; eq_crush.
Defined.

Global Instance EqClass_SP : EqClass SP.
refine (Build_EqClass _
  (fun s1 s2 =>
    match s1, s2 with
    | ALL, ALL => true
    | NONE, NONE => true
    | _, _ => false
    end
  )
  (fun s1 s2 => _
  )
).
destruct s1, s2; ff.
Defined.

Fixpoint eqb_Term `{EqClass Plc, EqClass SP, EqClass ASP} (t1 t2 : Term) : bool :=
  match t1, t2 with
  | asp a1, asp a2 => eqb a1 a2
  | att p1 t1, att p2 t2 => eqb p1 p2 && eqb_Term t1 t2
  | lseq t1 t2, lseq t1' t2' => eqb_Term t1 t1' && eqb_Term t2 t2'
  | bseq s t1 t2, bseq s' t1' t2' => 
      eqb s s' && eqb_Term t1 t1' && eqb_Term t2 t2'
  | bpar s t1 t2, bpar s' t1' t2' => 
      eqb s s' && eqb_Term t1 t1' && eqb_Term t2 t2'
  | _, _ => false
  end.

Global Instance EqClass_Term `{EqClass Plc, EqClass SP, EqClass ASP} : EqClass Term.
refine (Build_EqClass _ eqb_Term (fun t1 => _ )).
induction t1; intros y; destruct y; simpl in *; ff; eq_crush; rw_all.
Qed.

Fixpoint eqb_EvidenceT `{EqClass N_ID, EqClass ASP_PARAMS, EqClass Plc} (e1 e2 : EvidenceT) : bool :=
  match e1, e2 with
  | mt_evt, mt_evt => true
  | nonce_evt i, nonce_evt i' => eqb i i'
  | asp_evt p par e, asp_evt p' par' e' =>
    (eqb p p') && (eqb par par') && (eqb_EvidenceT e e')
  | left_evt e, left_evt e' => eqb_EvidenceT e e'
  | right_evt e, right_evt e' => eqb_EvidenceT e e'
  | split_evt e1 e2, split_evt e1' e2' =>
    eqb_EvidenceT e1 e1' && eqb_EvidenceT e2 e2'
  | _, _ => false
  end.

Global Instance EqClass_EvidenceT `{EqClass N_ID, EqClass Plc, EqClass ASP_PARAMS} : EqClass EvidenceT.
eapply Build_EqClass with (eqb := eqb_EvidenceT).
induction x, y; simpl in *; ff; eq_crush; rw_all.
Qed.