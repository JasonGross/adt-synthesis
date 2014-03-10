Require Import Computation.

Set Implicit Arguments.

(* Specification of mutator method. *)
Definition mutatorMethodSpec (Ty : Type)
           (mutCtx obsCtx : Context)
           (idx : @names mutCtx)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> Ty (* Final Model *)
     -> cod idx (* Return value *)
     -> Prop.

(* Specification of an observer method *)
Definition observerMethodSpec (Ty : Type)
           (mutCtx obsCtx : Context)
           (idx : @names obsCtx)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> cod idx (* Return value *)
     -> Prop.
