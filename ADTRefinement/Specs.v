Require Import Computation.

Set Implicit Arguments.

(* Specification of method. *)
Definition methodSpec (Ty : Type)
           (indices : Context)
           (idx : names)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> Ty (* Final Model *)
     -> cod idx (* Return value *)
     -> Prop.
