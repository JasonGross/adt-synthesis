Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

(** * Basic ADT definitions *)
(** Type of a context *)
Definition Build_ADTContext
           (rep : Type)
           (mutCtx obsCtx : Context)
: Context :=
  {| names := @names mutCtx + @names obsCtx;
     dom idx := rep *
                match idx with
                  | inl mIdx => dom mIdx
                  | inr oIdx => dom oIdx
                end;
     cod idx := match idx with
                  | inl mIdx => rep * cod mIdx
                  | inr oIdx => cod oIdx
                end |}.

(** Type of a mutator method *)
Definition mutatorMethodTypeUnbundled (Ty : Type)
           (mutCtx obsCtx : Context)
           (idx : @names mutCtx)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty mutCtx obsCtx)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> Comp (Ty * cod idx) (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodTypeUnbundled (Ty : Type)
           (mutCtx obsCtx : Context)
           (idx : @names obsCtx)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty mutCtx obsCtx)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> Comp (cod idx) (* Return value *).

(** Type of a mutator method bundled with its context *)
Definition mutatorMethodType (Ty : Type)
           (mutCtx obsCtx : Context)
           (idx : @names mutCtx)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> BundledComp (Ty * cod idx) (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodType (Ty : Type)
           (mutCtx obsCtx : Context)
           (idx : @names obsCtx)
  := Ty    (* Initial model *)
     -> dom idx (* Actual argument*)
     -> BundledComp (cod idx). (* Return value *)

(** Interface of an ADT *)
Record ADT :=
  {
    Rep : Type;
    (** The representation type of the ADT **)

    MutatorContext : Context;
    (** The index set of mutators *)

    ObserverContext : Context;
    (** The index set of observers *)

    ADTContext : Context := Build_ADTContext Rep MutatorContext ObserverContext;

    UnbundledMutatorMethods :
      forall idx : @names MutatorContext,
        Rep -> dom idx -> @Comp ADTContext (Rep * cod idx);
    (** Mutator method implementations *)

    UnbundledObserverMethods :
      forall idx : @names ObserverContext,
        Rep -> dom idx -> @Comp ADTContext (cod idx)
    (** Observer method implementations *)

  }.

Definition ADTLookupContext (A : ADT) : LookupContext
  := {| LContext := ADTContext A;
        lookup idx := match idx with
                        | inl mIdx => fun state_value =>
                                        UnbundledMutatorMethods A mIdx (fst state_value) (snd state_value)
                        | inr oIdx => fun state_value =>
                                        UnbundledObserverMethods A oIdx (fst state_value) (snd state_value)
                      end |}.

Definition MutatorMethods (A : ADT) (i : @names (MutatorContext A))
: mutatorMethodType (Rep A) (MutatorContext A) (ObserverContext A) i
  := fun m x => ``[ UnbundledMutatorMethods A i m x with ADTLookupContext A ]`` .

Definition ObserverMethods (A : ADT) (i : @names (ObserverContext A))
: observerMethodType (Rep A) (MutatorContext A) (ObserverContext A) i
  := fun m x => ``[ UnbundledObserverMethods A i m x with ADTLookupContext A ]``.
