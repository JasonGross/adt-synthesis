Require Import Common.
Require Import Computation.Core.

Ltac t_refine' :=
  first [ progress simpl in *
        | progress unfold impl in *
        | progress eauto
        | eassumption
        | solve [ apply reflexivity ] (* [reflexivity] is broken in the presence of a [Reflexive pointwise_relation] instance.... see https://coq.inria.fr/bugs/show_bug.cgi?id=3257.  Also https://coq.inria.fr/bugs/show_bug.cgi?id=3265 *)
        | progress split_iff
        | progress inversion_by computes_to_inv
        | progress subst
        | intro
        | progress destruct_head_hnf prod
        | progress destruct_head_hnf and
        | progress destruct_head_hnf sig
        | econstructor
        | erewrite is_computational_val_unique
        | progress specialize_all_ways ].

Ltac t_refine := repeat t_refine'.
