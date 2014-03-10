Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Specs.

Generalizable All Variables.
Set Implicit Arguments.

(** Every spec is trivially implementable using [Pick]. *)
Section pick.
  Variable rep : Type.
  Variable mutatorMethodContext : Context.
  Variable observerMethodContext : Context.
  Variable mutatorMethodSpecs : forall name, @mutatorMethodSpec rep mutatorMethodContext observerMethodContext name.
  Variable observerMethodSpecs : forall name, @observerMethodSpec rep mutatorMethodContext observerMethodContext name.

  Local Obligation Tactic := econstructor; eauto.

  Program Definition pickImpl : ADT :=
    {|
      Rep := rep;
      MutatorContext := mutatorMethodContext;
      ObserverContext := observerMethodContext;
      UnbundledMutatorMethods idx :=
        fun r x =>
          { r' : rep * cod _
          | mutatorMethodSpecs idx r x (fst r') (snd r')}%comp;
      UnbundledObserverMethods idx :=
        fun r n =>
          { n' : cod _
          | observerMethodSpecs idx r n n'}%comp
    |}.

End pick.
