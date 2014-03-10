Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

(** * Basic ADT definitions *)
(** Type of a context *)
Definition Build_ADTContext
           (rep : Type)
           (indices : Context)
: Context :=
  {| names := names;
     dom idx := rep * dom idx;
     cod idx := rep * cod idx |}.

(** Type of a method *)
Definition methodTypeUnbundled (Ty : Type)
           (indices : Context)
           (idx : names)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty indices)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> Comp (Ty * cod idx) (* Final Model and return value *).

(** Type of a mutator method bundled with its context *)
Definition methodType (Ty : Type)
           (indices : Context)
           (idx : names)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> BundledComp (Ty * cod idx) (* Final Model *).

(** Interface of an ADT *)
Record ADT :=
  {
    Rep : Type;
    (** The representation type of the ADT **)

    MethodNames : Context;
    (** The index set of methods *)

    ADTContext : Context := Build_ADTContext Rep MethodNames;

    UnbundledMethods : forall idx, methodTypeUnbundled Rep MethodNames idx
    (** Method implementations *)
  }.

Global Existing Instance ADTContext.

Definition ADTLookupContext (A : ADT) : LookupContext
  := {| LContext := ADTContext A;
        lookup idx state_value := UnbundledMethods A idx (fst state_value) (snd state_value) |}.

Definition Methods (A : ADT) (i : names)
: methodType (Rep A) (MethodNames A) i
  := fun m x => ``[ UnbundledMethods A i m x with ADTLookupContext A ]`` .
