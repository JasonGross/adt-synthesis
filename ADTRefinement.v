Require Import Common Computation ADT.

Generalizable All Variables.
Set Implicit Arguments.

(* Specification of mutator method. *)
Definition mutatorMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final Model *)
  -> Prop.

(* Specification of an observer method *)
Definition observerMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> nat (* Return value *)
  -> Prop.

(** Every spec is trivially implementable using [Pick]. *)
Section pick.
  Variable model : Type.
  Variable mutatorMethodIndex : Type.
  Variable observerMethodIndex : Type.
  Variable mutatorMethodSpecs : mutatorMethodIndex -> mutatorMethodSpec model.
  Variable observerMethodSpecs : observerMethodIndex -> observerMethodSpec model.

  Definition pickImpl : ADT :=
    {|
      Model := model;
      MutatorIndex := mutatorMethodIndex;
      ObserverIndex := observerMethodIndex;
      MutatorMethods idx :=
        fun m x =>
          { m' : model
          | mutatorMethodSpecs idx m x m'}%comp;
      ObserverMethods idx :=
        fun m n =>
          { n' : nat
          | observerMethodSpecs idx m n n'}%comp
    |}.
End pick.

Section MethodRefinement.
  Variables oldModel newModel : Type.

  Variable abs : newModel -> Comp oldModel.
  (** Abstraction function *)

  (** Refinement of a mutator method: if we first do the new
      computation and then abstract, this is a refinement of first
      abstracting and then doing the old computation.  That is, the
      following diagram commutes:
<<
                   old mutator
       old model --------------> old model
          ↑                         ↑
      abs |                         | abs
          |                         |
       new model --------------> new model
                   new mutator
>>  *)
  Definition refineMutator
             (oldMutator : mutatorMethodType oldModel)
             (newMutator : mutatorMethodType newModel)
    := forall new_state n,
         refine (old_state <- abs new_state;
                 oldMutator old_state n)
                (new_state' <- newMutator new_state n;
                 abs new_state').

  (** Refinement of an observer method: the new computation should be
      a refinement of first abstracting and then doing the old
      computation.  That is, the following diagram should commute:
<<
                  old observer
       old model --------------> ℕ
          ↑                      ∥
      abs |                      ∥ id
          |                      ∥
       new model --------------> ℕ
                  new observer
>>
   *)
  Definition refineObserver
             (oldObserver : observerMethodType oldModel)
             (newObserver : observerMethodType newModel)
    := forall new_state n,
         refine (old_state <- abs new_state;
                 oldObserver old_state n)
                (newObserver new_state n).
End MethodRefinement.

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)
Inductive refineADT (A B : ADT) : Prop :=
| refinesADT :
    forall abs mutatorMap observerMap,
      (forall idx, @refineMutator
                     (Model A) (Model B) abs
                     (MutatorMethods A idx)
                     (MutatorMethods B (mutatorMap idx)))
      -> (forall idx, @refineObserver
                     (Model A) (Model B) abs
                     (ObserverMethods A idx)
                     (ObserverMethods B (observerMap idx)))
      -> refineADT A B.

(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .

Check bind_bind.
Print Bind.
Add Parametric Morphism A B C : (fun ca cb f => @Bind A C ca (fun a => @Bind B C (cb a) f))
    with signature
    (@refine A)
      ==> (pointwise_relation _ (@refine B))
      ==> (pointwise_relation _ (@refine C))
      ==> (@refine C)
      as refine_bind_bind.
Proof.
  intros.
  unfold pointwise_relation in *.
  setoid_rewrite_hyp.
  apply refine_bind; [ reflexivity | intro ].
  apply refine_bind; [ reflexivity | intro ].
  auto.
Qed.

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (abs := @Return _)
      (mutatorMap := id)
      (observerMap := id);
      unfold id; simpl; intros;
      autorewrite with refine_monad;
      reflexivity.
  - intros x y z
           [abs mutMap obsMap mutH obsH]
           [abs' mutMap' obsMap' mutH' obsH'].
    econstructor 1 with
    (abs := fun z => (z' <- abs' z; abs z')%comp)
    (mutatorMap := mutMap' ∘ mutMap)
    (observerMap := obsMap' ∘ obsMap);
    unfold id, compose; simpl in *; intros.
    autorewrite with refine_monad.
    setoid_rewrite_hyp.
    setoid_rewrite mutH'.
    interleave_autorewrite_refine_monad_with setoid_rewrite_hyp.
Qed.

Add Parametric Relation : ADT refineADT
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as refineADT_rel.

Add Parametric Morphism model mutIdx obsIdx : (@Build_ADT model mutIdx obsIdx)
  with signature
  (pointwise_relation _ (@refineMutator _ _ (@Return _)))
    ==> (pointwise_relation _ (@refineObserver _ _ (@Return _)))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B (@Return _) id id);
    unfold id, pointwise_relation in *; simpl in *; intros;
    auto.
Qed.

(** If we had dependent setoid relations in [Type], then we could write

<<
Add Parametric Morphism : @Build_ADT
  with signature
  (fun oldM newM => newM -> Comp oldM)
    ==> arrow
    ==> arrow
    ==> (pointwise_relation _ (@refineMutator _ _ _))
    ==> (pointwise_relation _ (@refineObserver _ _ _))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  ...
Qed.
>>

    But, alas, Matthieu is still working on those.  So the rewrite
    machinery won't work very well when we're switching models, and
    we'll instead have to use [etransitivity] and [apply] things. *)

(* Given an abstraction function, we can transform the model of a pickImpl ADT. *)

Theorem refines_model_pickImpl
        newModel oldModel
        (abs : newModel -> oldModel)
        MutatorIndex ObserverIndex
        ObserverSpec MutatorSpec :
  refineADT
    (@pickImpl oldModel MutatorIndex ObserverIndex MutatorSpec ObserverSpec)
    (@pickImpl newModel MutatorIndex ObserverIndex
               (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
               (fun idx nm => ObserverSpec idx (abs nm))).
Proof.
  econstructor 1 with (abs := fun nm => Return (abs nm))
                        (mutatorMap := @id MutatorIndex)
                        (observerMap := @id ObserverIndex);
  compute; intros; inversion_by computes_to_inv; subst; eauto.
Qed.

(* We can cache an observer value by refining the model and the mutators. *)

Open Scope comp_scope.

Theorem refines_cached_Observer adt
        (ObserverIndex_eq : forall idx idx' : ObserverIndex adt,
                               {idx = idx'} + {idx <> idx'})
        (cachedIndex : ObserverIndex adt) (* Index of the Observer to Cache *)
        (cached_func : Model adt -> nat -> nat)
        (refines_cached : forall om n,
                            refine (ObserverMethods adt cachedIndex om n)
                                   (ret (cached_func om n)))

:
  refineADT adt
            {| Model := {om : (Model adt) * (nat -> nat) |
                         forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n))};
               MutatorIndex := MutatorIndex adt;
               ObserverIndex := ObserverIndex adt;
               ObserverMethods idx nm n :=
                   if (ObserverIndex_eq idx cachedIndex) then
                     ret ((snd (proj1_sig nm)) n)
                   else
                     ObserverMethods adt idx (fst (proj1_sig nm)) n;
                 MutatorMethods idx nm n :=
                   origModel <- (MutatorMethods adt idx (fst (proj1_sig nm)) n);
                     ret (exist
                            (fun om => forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n)))
                            (origModel, cached_func origModel)
                            (refines_cached origModel))|}.
Proof.
  destruct adt;
  econstructor 1 with
  (abs := fun om : {om | forall n, refine (ObserverMethods cachedIndex (fst om) n) (ret (snd om n))} =>
            ret (fst (proj1_sig om)))
    (mutatorMap := @id MutatorIndex)
    (observerMap := @id ObserverIndex); simpl; intros.
  - autorewrite with refine_monad; rewrite refineEquiv_under_bind with (g := @Return _);
    intros; autorewrite with refine_monad; reflexivity.
  - autorewrite with refine_monad; find_if_inside;
    [ destruct new_state; subst; auto
      | reflexivity].
Qed.

Theorem refines_cached_computational_Observer adt
        (ObserverIndex_eq : forall idx idx' : ObserverIndex adt,
                               {idx = idx'} + {idx <> idx'})
        (cachedIndex : ObserverIndex adt) (* Index of the Observer to Cache *)
        (computational_Index : forall om n, is_computational (ObserverMethods adt cachedIndex om n))
:
  refineADT adt
  {| Model := {om : (Model adt) * (nat -> nat) |
               forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n))};
     MutatorIndex := MutatorIndex adt;
     ObserverIndex := ObserverIndex adt;
     ObserverMethods idx nm n :=
       if (ObserverIndex_eq idx cachedIndex) then
                     ret ((snd (proj1_sig nm)) n)
       else
         ObserverMethods adt idx (fst (proj1_sig nm)) n;
     MutatorMethods idx nm n :=
                   origModel <- (MutatorMethods adt idx (fst (proj1_sig nm)) n);
     ret (exist
            (fun om => forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n)))
            (origModel, fun n => proj1_sig (is_computational_val (computational_Index origModel n)))
            (fun n => refine_is_computational (computational_Index origModel n))) |}. 
Proof.
  apply refines_cached_Observer.
Qed.

(** If you mutate and then observe, you can do it before or after
    refinement.  I'm not actually sure this isn't obvious.  *)

Lemma ADTRefinementOk
      (old new : ADT)
      (new_initial_value : Comp (Model new))
      abs mutatorMap observerMap H H'
      (ref : refineADT old new
       := @refinesADT old new abs mutatorMap observerMap H H')
      mutIdx obsIdx n n'
: refine (v0 <- new_initial_value;
          v <- abs v0;
          v' <- MutatorMethods old mutIdx v n;
          ObserverMethods old obsIdx v' n')
         (v <- new_initial_value;
          v' <- MutatorMethods new (mutatorMap mutIdx) v n;
          ObserverMethods new (observerMap obsIdx) v' n').
Proof.
  simpl in *.
  apply refine_bind; [ reflexivity | ].
  intro.
  interleave_autorewrite_refine_monad_with setoid_rewrite_hyp.
Qed.
