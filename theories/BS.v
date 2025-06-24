(* Defining (abstract) representation for raw binary data values.
   BS stands for "Binary String".  May be instantiated with 
   types like strings and byte buffers in concrete implementations.    *)

From CoplandSpec Require Import ID_Type.

Definition BS : Set := string.
Global Opaque BS.

Global Instance Stringifiable_BS : Stringifiable BS := Stringifiable_ID_Type.

Global Instance DecEq_BS : DecEq BS := DecEq_ID_Type.

Definition passed_bs  : BS := ""%string.
