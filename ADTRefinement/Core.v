Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Pick ADTRefinement.Specs.

Generalizable All Variables.
Set Implicit Arguments.

Section MethodRefinement.
  Variables oldRep newRep : Type.
  (** Old and new representations **)

  Variable BiR : oldRep -> newRep -> Prop.
  (** Bisimulation Relation *)

  Notation "ro ≃ rn" := (BiR ro rn) (at level 70).

  (** Refinement of a method: the values of the computation, produced
      by applying a new method [newMethod] to any new state [r_n]
      related to an old state [r_o] by the bisimulation relation
      [BiR], are related by [BiR] to some value produced by the
      corresponding old method on [r_o].  The input values must be
      equal across a specified equality of types. Related values are
      taken to related values (with the new method potentially
      producing more deterministic computations). That is, the
      following diagram commutes:

<<
                   old mutator
       old rep --------------> old rep
          |                         |
      BiR |                         | BiR
          ↓                         ↓
       new rep --------------> new rep
                   new mutator
>>  *)

  Definition refineMethod
             (oldCtx newCtx : Context)
             oldIdx newIdx
             (Hdom : @dom newCtx newIdx = @dom oldCtx oldIdx)
             (Hcod : cod oldIdx = cod newIdx)
             (oldMethod : methodType oldRep oldCtx oldIdx)
             (newMethod : methodType newRep newCtx newIdx)
    := forall r_o r_n n, r_o ≃ r_n ->
         refineBundled `[r_o' <- oldMethod r_o (Hdom # n);
                          {r_n' | fst r_o' ≃ fst r_n' /\ Hcod # snd r_o' = snd r_n'}]`
                       (newMethod r_n n).
End MethodRefinement.

Notation "c ↝ v" := (computes_to c v) (at level 70).

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)

Inductive refineADT : ADT -> ADT -> Prop :=
| refinesADT :
    forall A B
           methodMap
           SiR,
      (forall idx,
         exists (Hdom : dom (methodMap idx) = dom idx)
                (Hcod : cod idx = cod (methodMap idx)),
           @refineMethod
             (Rep A) (Rep B) SiR
             (MethodNames A) (MethodNames B)
             idx (methodMap idx)
             Hdom Hcod
             (Methods A idx) (Methods B (methodMap idx)))
      -> refineADT A B.

(** We should always just unfold [refineMethod] into [refine], so that
    we can rewrite with lemmas about [refine]. *)
Arguments refineMethod / .
