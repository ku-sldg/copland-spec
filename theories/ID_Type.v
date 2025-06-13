(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)
From RocqCandy Require Export All.
From RocqJSON Require Export JSON JSON_Error_Strings.
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

Global Instance Jsonifiable_ID_Type `{Stringifiable ID_Type} : Jsonifiable ID_Type.
ref (Build_Jsonifiable _ 
  (fun i => JSON_String (to_string i))
  (fun j =>
    match j with
    | JSON_String s => from_string s
    | _ => err (errStr_json_wrong_type "string" j)
    end)
 _).
jsonifiable_hammer.
Qed.
  