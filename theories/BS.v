(* Defining (abstract) representation for raw binary data values.
   BS stands for "Binary String".  May be instantiated with 
   types like strings and byte buffers in concrete implementations.    *)

From CoplandSpec Require Import ID_Type.

Definition BS : Set := string.

Global Instance Stringifiable_BS : Stringifiable BS := Stringifiable_ID_Type.

Global Instance EqClass_BS : EqClass BS. typeclasses eauto. Defined.

Definition passed_bs  : BS := ""%string.
