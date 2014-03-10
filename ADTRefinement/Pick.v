Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Specs.

Generalizable All Variables.
Set Implicit Arguments.

(** Every spec is trivially implementable using [Pick]. *)
Section pick.
  Variable rep : Type.
  Variable methodNames : Context.
  Variable methodSpecs : forall name, @methodSpec rep methodNames name.

  Local Obligation Tactic := econstructor; eauto.

  Program Definition pickImpl : ADT :=
    {|
      Rep := rep;
      MethodNames := methodNames;
      UnbundledMethods idx :=
        fun r x =>
          { r' : rep * cod _
          | methodSpecs idx r x (fst r') (snd r')}%comp
    |}.
End pick.
