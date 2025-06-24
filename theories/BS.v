(* Defining (abstract) representation for raw binary data values.
   BS stands for "Binary String".  May be instantiated with 
   types like strings and byte buffers in concrete implementations.    *)

From CoplandSpec Require Import ID_Type.

Definition BS : Set := ID_Type.
Global Opaque BS.

Definition passed_bs  : BS := ""%string.
