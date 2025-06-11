From RocqCandy Require Import All.

From CoplandSpec Require Import Term_Defs_Core Prelude.

Global Instance DecEq_ASP_PARAMS `{DecEq ASP_ID, DecEq Plc, DecEq TARG_ID, DecEq ASP_ARGS} : DecEq ASP_PARAMS.
build_deq.
Defined.

Global Instance DecEq_ASP `{DecEq ASP_PARAMS, DecEq Plc}: DecEq ASP.
build_deq.
Defined.

Global Instance DecEq_SP : DecEq SP.
build_deq.
Defined.

Global Instance DecEq_Split `{DecEq SP} : DecEq Split.
build_deq.
Defined.

(* Fixpoint eqb_Term `{DecEq Plc, DecEq SP, DecEq ASP} (t1 t2 : Term) : bool :=
  match t1, t2 with
  | asp a1, asp a2 => eqb a1 a2
  | att p1 t1, att p2 t2 => eqb p1 p2 && eqb_Term t1 t2
  | lseq t1 t2, lseq t1' t2' => eqb_Term t1 t1' && eqb_Term t2 t2'
  | bseq s t1 t2, bseq s' t1' t2' => 
      eqb s s' && eqb_Term t1 t1' && eqb_Term t2 t2'
  | bpar s t1 t2, bpar s' t1' t2' => 
      eqb s s' && eqb_Term t1 t1' && eqb_Term t2 t2'
  | _, _ => false
  end. *)

Global Instance DecEq_Term `{DecEq Plc, DecEq Split, DecEq ASP} : DecEq Term.
ref (Build_DecEq _ _).
intros x; induction x;
intros y; destruct y; ff;
try (decdec_eq ()).
- destruct (IHx y); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
Defined.

Global Instance DecEq_EvidenceT `{DecEq N_ID, DecEq Plc, DecEq ASP_PARAMS} : DecEq EvidenceT.
ref (Build_DecEq _ _).
intros x; induction x;
intros y; destruct y; ff;
try (decdec_eq ()).
- destruct (IHx y); ff.
- destruct (IHx y); ff.
- destruct (IHx y); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
Defined.