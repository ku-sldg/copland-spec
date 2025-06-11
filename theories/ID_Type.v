(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)
From RocqCandy Require Export All.
Export ResultNotation.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set := string.
Global Opaque ID_Type.

(* Stringifiable Class for ID_Type *)
Global Instance Stringifiable_ID_Type : Stringifiable ID_Type. 
  typeclasses_eauto.
Qed.

Global Instance DecEq_ID_Type : DecEq ID_Type. 
  typeclasses_eauto. 
Qed.
