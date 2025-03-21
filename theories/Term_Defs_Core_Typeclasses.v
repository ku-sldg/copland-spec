From RocqCandy Require Import All.

From CoplandSpec Require Import Term_Defs_Core Prelude.

Global Instance EqClass_ASP_PARAMS : EqClass ASP_PARAMS.
refine (Build_EqClass _ 
  (fun '(asp_paramsC a1 la1 p1 t1) '(asp_paramsC a2 la2 p2 t2) => 
    (eqb a1 a2) && (eqb la1 la2) && (eqb p1 p2) && (eqb t1 t2)
  ) 
  (fun '(asp_paramsC a1 la1 p1 t1) '(asp_paramsC a2 la2 p2 t2) => _)
).
eq_crush.
Defined.

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
induction x, y; simpl in *; ff; eq_crush;
try erewrite IHx in *; ff;
try erewrite IHx1 in *;
try erewrite IHx2 in *; ff.
Defined.