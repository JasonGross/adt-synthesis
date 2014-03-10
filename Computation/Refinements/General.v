Require Import String Ensembles.
Require Import Common.
Require Import Computation.Core Computation.Monad Computation.SetoidMorphisms.

(** General Lemmas about the behavior of [computes_to], [refine], and
    [refineEquiv]. *)

Local Arguments impl _ _ / .

Local Ltac t_refine :=
  repeat first [ progress simpl in *
               | progress eauto
               | eassumption
               | reflexivity
               | progress split_iff
               | progress inversion_by computes_to_inv
               | progress subst
               | intro
               | econstructor
               | erewrite is_computational_val_unique
               | progress destruct_head_hnf prod
               | progress destruct_head_hnf and
               | progress specialize_all_ways ].

Section structural.

  (* BD: This defines a notion of equivalnce for call-free
     computations. Computations which are call-free compute to
     the same value regardless of the context, naturally. *)

  Inductive refineBundled_structural {ctx1 ctx2 : LookupContext}
  : forall A, @Comp ctx1 A -> @Comp ctx2 A -> Prop :=
| rbEq_Return : forall A (x : A), refineBundled_structural (Return x) (Return x)
| rbEq_Bind : forall A B c1 c2 f1 f2,
                refineBundled_structural c1 c2
                -> (forall v : A,
                      computes_to (ctx := ctx1) c1 v
                      -> computes_to (ctx := ctx2) c2 v
                      -> refineBundled_structural (f1 v) (f2 v))
                -> @refineBundled_structural _ _ B (Bind c1 f1) (Bind c2 f2)
| rbEq_Pick : forall A P, @refineBundled_structural ctx1 ctx2 A (Pick P) (Pick P).


  Lemma refineBundled_structural_impl_refineBundledEquiv {A} (c1 c2 : BundledComp A)
  : refineBundled_structural c1 c2 -> refineBundledEquiv c1 c2.
  Proof.
    destruct c1 as [ctx1 c1], c2 as [ctx2 c2]; simpl.
    induction 1; t_refine.
  Qed.
End structural.

Ltac refineBundledEquiv_reflexivity_ignore_context :=
  apply refineBundled_structural_impl_refineBundledEquiv;
  simpl;
  repeat (econstructor || intro).

Ltac equate_evar_context :=
  unfold refineBundledEquiv, refineBundled; simpl;
  lazymatch goal with
    | [ |- @refineEquiv ?A ?ctx1 (@CompContext ?B ?e) ?v1 ?v2 ]
      => is_evar e; refine (_ : @refineEquiv A ctx1 (@CompContext B {| CompContext := ctx1 |}) v1 v2)
    | [ |- @refine ?A ?ctx1 (@CompContext ?B ?e) ?v1 ?v2 ]
      => is_evar e; refine (_ : @refine A ctx1 (@CompContext B {| CompContext := ctx1 |}) v1 v2)
  end;
  simpl.

Ltac etransitivity_context :=
  etransitivity;
  [ equate_evar_context | refineBundledEquiv_reflexivity_ignore_context ].

Section general_refine_lemmas.
  Lemma refineEquiv_is_computational {A} {ctx1 ctx2 : LookupContext} {c} (CompC : @is_computational ctx1 A c)
  : @refineEquiv _ ctx1 ctx2
                c (ret (is_computational_val CompC)).
  Proof.
    unfold refineEquiv, refine.
    pose proof (is_computational_val_computes_to CompC).
    t_refine.
  Qed.

  Definition refineBundledEquiv_is_computational A {ctx1 : LookupContext} (c : BundledComp A)
  : forall (CompC : is_computational c),
      refineBundledEquiv c ``[ ret (is_computational_val CompC) with ctx1 ]``
    := @refineEquiv_is_computational A _ ctx1 c.

  Lemma refine_pick A {ctx1 ctx2 : LookupContext}
        (P : A -> Prop) c (H : forall x, c ↝ x -> P x)
  : @refine A ctx1 ctx2
            { x : A | P x }%comp
            c.
  Proof. t_refine. Qed.

  Definition refineBundled_pick A {ctx1 : LookupContext}
             P (c : BundledComp A)
  : _ -> refineBundled ``[ { x : A | P x }%comp with ctx1 ]``
                       c
    := @refine_pick _ _ _ P c.

  Lemma refine_pick_pick A {ctx1 ctx2 : LookupContext} (P1 P2 : A -> Prop)
        (H : forall x, P2 x -> P1 x)
  : @refine _ ctx1 ctx2
            { x : A | P1 x }%comp
            { x : A | P2 x }%comp.
  Proof. t_refine. Qed.

  Definition refineBundled_pick_pick
  : forall A {ctx1 ctx2} P1 P2 H,
      refineBundled ``[ _ with ctx1 ]``
                    ``[ _ with ctx2 ]``
    := refine_pick_pick.

  Lemma refineEquiv_pick_pick A {ctx1 ctx2} (P1 P2 : A -> Prop)
        (H : forall x, P1 x <-> P2 x)
  : @refineEquiv _ ctx1 ctx2
                 { x : A | P1 x }%comp
                 { x : A | P2 x }%comp.
  Proof. t_refine. Qed.

  Definition refineBundledEquiv_pick_pick
  : forall A {ctx1 ctx2} P1 P2 H,
      refineBundledEquiv ``[ _ with ctx1 ]``
                         ``[ _ with ctx2 ]``
    := refineEquiv_pick_pick.

  Lemma refineEquiv_pick_pair {ctx1 ctx2} A B (PA : A -> Prop) (PB : B -> Prop)
  : @refineEquiv _ ctx1 ctx2
                 { x : A * B | PA (fst x) /\ PB (snd x) }%comp
                 (a <- { a : A | PA a };
                  b <- { b : B | PB b };
                  ret (a, b))%comp.
  Proof. t_refine. Qed.

  Definition refineEquivBundled_pick_pair
  : forall A {ctx1 ctx2} P1 P2 H,
      refineBundledEquiv ``[ _ with ctx1 ]``
                         ``[ _ with ctx2 ]``
    := refineEquiv_pick_pick.

  Definition refineEquiv_split_ex {ctx1 ctx2} A B (P : A -> Prop) (P' : A -> B -> Prop)
  : @refineEquiv _ ctx1 ctx2
                 { b | exists a, P a /\ P' a b }%comp
                 (a <- { a | P a /\ exists b, P' a b };
                  { b | P' a b })%comp.
  Proof. t_refine. Qed.

  Definition refineBundledEquiv_split_ex
  : forall {ctx1 ctx2} A B P P',
      refineBundledEquiv `[ _ ]` `[ _ ]`
    := @refineEquiv_split_ex.

  Definition refineEquiv_pick_contr_ret {ctx1 ctx2} A (P : A -> Prop)
             (x : A) (H : unique P x)
  : @refineEquiv _ ctx1 ctx2
                 { y | P y }
                 (ret x).
  Proof. t_refine. Qed.

  Definition refineEquiv_pick_eq {ctx1 ctx2}
             A (x : A)
  : @refineEquiv _ ctx1 ctx2
                 { y | y = x }%comp
                 (ret x).
  Proof. t_refine. Qed.

  Definition refineBundledEquiv_pick_eq
  : forall {ctx1 ctx2}
           A (x : A),
      refineBundledEquiv `[ _ ]` `[ _ ]`
    := @refineEquiv_pick_eq.

  Definition refineEquiv_pick_eq' {ctx1 ctx2}
             A (x : A)
  : @refineEquiv _ ctx1 ctx2
                 { y | x = y }%comp
                 (ret x).
  Proof. t_refine. Qed.

  Definition refineBundledEquiv_pick_eq'
  : forall {ctx1 ctx2}
           A (x : A),
      refineBundledEquiv `[ _ ]` `[ _ ]`
    := @refineEquiv_pick_eq'.

  Definition refineBundledEquiv_split_func_ex {ctx1 ctx2}
             A B (P : A -> Prop) (f : A -> B)
  : refineBundledEquiv ``[ { b | exists a, P a /\ b = f a}%comp with ctx1 ]``
                       ``[ (a <- { a | P a};
                            ret (f a))%comp
                           with ctx2 ]``.
  Proof.
    repeat setoid_rewrite refineBundledEquiv_split_ex.
    (** I want to just [setoid_rewrite refineBundledEquiv_pick_eq].  But I can't because things don't line up nicely, and there are no parameterized setoid relations.  :-(  So instead we need to [etransitivity_context] instead. *)
    etransitivity_context.
    setoid_rewrite refineEquiv_pick_eq.
    (** [erewrite] is buggy: https://coq.inria.fr/bugs/show_bug.cgi?id=3244 *)
    erewrite (@refineEquiv_pick_pick _ _ _).
    - reflexivity.
    - abstract (repeat (intro || esplit); intuition).
  Qed.

  Definition refineEquiv_split_func_ex {ctx1 ctx2}
  : forall A B (P : A -> Prop) (f : A -> B),
      @refineEquiv _ ctx1 ctx2
                   { b | exists a, P a /\ b = f a}%comp
                   (a <- { a | P a};
                    ret (f a))%comp
    := refineBundledEquiv_split_func_ex.

  Definition refineBundledEquiv_split_func_ex2 {ctx1 ctx2} A A' B (P : A -> Prop) (P' : A' -> Prop)
             (f : A -> A' -> B)
  : refineBundledEquiv ``[ { b | exists a, P a /\ exists a', P' a' /\ b = f a a'} with ctx1 ]``
                       ``[ (a <- { a | P a};
                            a' <- { a' | P' a'};
                            ret (f a a'))
                           with ctx2 ]``.
  Proof.
    etransitivity_context.
    (** >:-(   We shouldn't need to clear the context to get typeclass resolution and setoid rewriting to work. *)
    clear.
    repeat setoid_rewrite (@refineEquiv_split_ex _ _).
    setoid_rewrite (@refineEquiv_pick_eq _ _).
    split; intro; intros;
    inversion_by computes_to_inv; subst;
    repeat econstructor; eassumption.
  Qed.

  Definition refineEquiv_split_func_ex2 {ctx1 ctx2}
  : forall A A' B (P : A -> Prop) (P' : A' -> Prop)
           (f : A -> A' -> B),
      refineEquiv _ _
    := @refineBundledEquiv_split_func_ex2 ctx1 ctx2.

  (* [refine_bind] assumes a uniform context, which we don't always have.*)
  Definition refineBundled_bind {ctx1 ctx2 : LookupContext}
  : forall A B a a' (b : A -> @Comp ctx1 B) (b' : A -> @Comp ctx2 B),
      refineBundled ``[a with ctx1]`` ``[a' with ctx2]``
      -> (forall a, refineBundled ``[b a with ctx1]`` ``[b' a with ctx2]``)
      -> refineBundled ``[(a'' <- a; b a'') with ctx1]`` ``[a'' <- a'; b' a'' with ctx2]`` .
  Proof.
    unfold refineBundled, refine; intros.
    apply_in_hyp computes_to_inv; simpl in *; destruct_ex; intuition;
    econstructor; eauto.
  Qed.

  Lemma refineBundledEquiv_pick_fst_snd_eq {ctx1 ctx2} A B x y
  : refineBundledEquiv ``[ { v : A * B | x = fst v /\ y = snd v } with ctx1 ]``
                       ``[ ret (x, y) with ctx2 ]``.
  Proof. t_refine. Qed.


  Definition refineEquiv_pick_fst_snd_eq {ctx1 ctx2}
  : forall A B x y, refineEquiv { v : A * B | _ } (ret (x, y))
    := @refineBundledEquiv_pick_fst_snd_eq ctx1 ctx2.
End general_refine_lemmas.
