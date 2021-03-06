Require Export QueryStructureNotations QueryQSSpecs.
Require Import List Compare_dec AdditionalLemmas
        AdditionalPermutationLemmas AdditionalMorphisms
        EnsembleListEquivalenceProperties flattenCompListProperties
        GeneralQueryRefinements.

Unset Implicit Arguments.

Transparent Count Query_For.

Ltac subst_strings :=
  repeat match goal with
           | [ H : string |- _ ] => subst H
           | [ H : BoundedIndex _ |- _ ] => subst H
         end.

Ltac pose_string_ids :=
  subst_strings;
  repeat match goal with
           | |- context [String ?R ?R'] =>
             let str := fresh "StringId" in
             set (String R R') as str in *
           | |- context [ ``(?R) ] =>
             let idx := fresh in
             set ``(R) as fresh in *
         end.

Section ConstraintCheckRefinements.
  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesSchemaConstraints.

  Fixpoint app_assoc {A : Set} (As As' As'' : list A):
      As ++ (As' ++ As'') = (As ++ As') ++ As'' :=
    match As as As return
                  As ++ (As' ++ As'') = (As ++ As') ++ As'' with
              | [] => eq_refl _
              | a :: As => (f_equal (fun l => a :: l) (app_assoc As As' As''))
            end.

  Lemma app_comm_cons' {A : Set}:
    forall (a : A) As As',
      As ++ (a :: As') = (As ++ [a]) ++ As'.
  Proof.
    intros; rewrite <- app_assoc; reflexivity.
  Defined.

  Definition Ensemble_BoundedIndex_app_comm_cons {A : Set}
    (a : A)
    (As As' : list A)
    (P : Ensemble (BoundedIndex (As ++ a :: As')))
  : Ensemble (BoundedIndex ((As ++ [a]) ++ As')).
    rewrite app_comm_cons' in P; exact P.
  Defined.

  Definition BoundedIndex_app_comm_cons {A : Set}
    (a : A)
    (As As' : list A)
    (a' : BoundedIndex (As ++ a :: As'))
  : BoundedIndex ((As ++ [a]) ++ As').
    rewrite app_comm_cons' in a'; exact a'.
  Defined.

  Lemma ibound_BoundedIndex_app_comm_cons {A : Set}
    (a : A)
    (As As' : list A)
    (a' : BoundedIndex (As ++ a :: As'))
  : ibound a' = ibound (BoundedIndex_app_comm_cons a As As' a').
  Proof.
    unfold BoundedIndex_app_comm_cons, eq_rec, eq_rect; simpl.
    destruct (app_comm_cons' a As As'); reflexivity.
  Qed.

  Program Fixpoint Iterate_Ensemble_BoundedIndex'
          {A : Set}
          (Visited Remaining : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining))) : Prop :=
    match Remaining with
        | [] => True
        | a :: Remaining' =>
          P {| bindex := a;
               indexb := {| ibound := List.length Visited;
                            boundi := _ |} |}
          /\ Iterate_Ensemble_BoundedIndex' (Visited ++ (a :: nil)) Remaining' _
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.

  (* Iterating with a filter. *)
  Program Fixpoint Iterate_Ensemble_BoundedIndex_filter'
          {A : Set}
          (Visited Remaining : list A)
          (filter : nat -> bool)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining))) : Prop :=
    match Remaining with
        | [] => True
        | a :: Remaining' =>
          if filter (List.length Visited)
          then
            P {| bindex := a;
                 indexb := {| ibound := List.length Visited;
                              boundi := _ |} |}
            /\ Iterate_Ensemble_BoundedIndex_filter' (Visited ++ (a :: nil)) Remaining' filter _
          else
            Iterate_Ensemble_BoundedIndex_filter' (Visited ++ (a :: nil)) Remaining' filter _
    end.
  Next Obligation.
    clear filter P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.

  Lemma Ensemble_BoundedIndex_app_equiv {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
        (a : A) (As As' : list A)
        (P : Ensemble (BoundedIndex (As ++ a :: As')))
  : forall idx idx' n nth nth',
      P {| bindex := idx; indexb := {| ibound := n; boundi := nth |}|} <->
      Ensemble_BoundedIndex_app_comm_cons a As As' P
                                     {| bindex := idx'; indexb := {| ibound := n; boundi := nth' |}|}.
  Proof.
    split; unfold Ensemble_BoundedIndex_app_comm_cons, BoundedIndex_app_comm_cons, app_comm_cons'; simpl;
    unfold eq_rec, eq_rect, eq_ind, eq_rect; destruct (app_assoc As [a] As'); auto;
    generalize (indexb_ibound_eq
            {| bindex := idx'; indexb := {| ibound := n; boundi := nth' |}|}
            {| bindex := idx; indexb := {| ibound := n; boundi := nth |}|}
            eq_refl); simpl; intros; subst;
    erewrite (eq_proofs_unicity_Opt_A A_eq_dec _); eauto.
  Qed.

  Lemma BoundedIndex_app_comm_cons_nth_eq {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall
      (As As' : list A)
      a a' a'' n nth nth',
      {| bindex := a; indexb := {| ibound := n; boundi := nth |}|} =
      BoundedIndex_app_comm_cons a' As As' {| bindex := a''; indexb := {| ibound := n; boundi := nth' |}|}.
  Proof.
    intros.
    unfold BoundedIndex_app_comm_cons, eq_rec, eq_rect; simpl.
    destruct (app_comm_cons' a' As As').
    generalize (indexb_ibound_eq
            {| bindex := a''; indexb := {| ibound := n; boundi := nth' |}|}
            {| bindex := a; indexb := {| ibound := n; boundi := nth |}|}
               eq_refl); simpl; intros; subst.
    erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth'); reflexivity.
  Qed.

  Lemma Ensemble_BoundedIndex_nth_eq {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall
      (As : list A)
      (P : Ensemble (BoundedIndex As))
      a a' n nth nth',
      P {| bindex := a; indexb := {| ibound := n; boundi := nth |}|} ->
      P {| bindex := a'; indexb := {| ibound := n; boundi := nth' |}|}.
  Proof.
    intros;
    generalize (indexb_ibound_eq
            {| bindex := a'; indexb := {| ibound := n; boundi := nth' |}|}
            {| bindex := a; indexb := {| ibound := n; boundi := nth |}|}
               eq_refl); simpl; intros; subst.
    erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth'); eassumption.
  Qed.

  Lemma nth_error_app {A : Set} :
    forall (a : A) (As As' : list A) n,
      nth_error As n = Some a ->
      nth_error (As ++ As') n = Some a.
  Proof.
    induction As; destruct n; simpl; intros; try discriminate; auto.
  Defined.

  Lemma Ensemble_nth_error_app
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall a (As As' : list A) nth'
      (P : Ensemble (BoundedIndex (As ++ (a :: As')))),
      P {| bindex := a;
           indexb := {| ibound := Datatypes.length As;
                        boundi := nth' |} |}
      -> (forall (a' : A) (n : nat) (nth : nth_error As n = Some a'),
      P {| bindex := a';
           indexb := {|
                      ibound := n;
                      boundi := nth_error_app _ As (a :: As') n nth |} |})
      -> forall (a' : A) (n : nat) (nth : nth_error (As ++ [a]) n = Some a'),
           Ensemble_BoundedIndex_app_comm_cons a As As' P
                                          {| bindex := a';
                                             indexb := {| ibound := n;
                                                          boundi := nth_error_app _ (As ++ [a]) As' n nth |} |}.
  Proof.
    intros.
    destruct (eq_nat_dec (List.length As) n ); subst.
    - rewrite (BoundedIndex_app_comm_cons_nth_eq
                 A_eq_dec As As' _ _ _  (List.length As)
                 (nth_error_app _ (As ++ [a]) As'
                                (Datatypes.length As) nth)
                 nth').
      erewrite <- BoundedIndex_app_comm_cons_nth_eq; eauto.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
    - assert (nth_error As n = Some a') by
          (revert n nth n0; clear; induction As; destruct n; simpl; intros;
           try congruence;
           [destruct n; discriminate
           | eauto]).
      generalize (H0 _ _ H1); intros.
      erewrite (BoundedIndex_app_comm_cons_nth_eq
                 A_eq_dec As As' _ _ _ n
                 (nth_error_app _ (As ++ [a]) As'
                                n nth)).
      erewrite <- BoundedIndex_app_comm_cons_nth_eq; eauto.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
      Grab Existential Variables.
      rewrite <- app_assoc; simpl; apply nth_error_app; eassumption.
      apply nth_error_app; eassumption.
      apply nth_error_app; eassumption.
  Qed.

  Lemma Ensemble_nth_error_app_filter
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall a (As As' : list A) nth'
           (P : Ensemble (BoundedIndex (As ++ (a :: As'))))
           (filter : Ensemble nat)
           (filter_dec : DecideableEnsemble filter),
      (filter (Datatypes.length As) ->
       P {| bindex := a;
            indexb := {| ibound := Datatypes.length As;
                         boundi := nth' |} |})
      -> (forall (a' : A) (n : nat) (nth : nth_error As n = Some a'),
            filter n ->
            P {| bindex := a';
                 indexb := {|
                            ibound := n;
                            boundi := nth_error_app _ As (a :: As') n nth |} |})
      -> forall (a' : A) (n : nat) (nth : nth_error (As ++ [a]) n = Some a'),
           filter n ->
           Ensemble_BoundedIndex_app_comm_cons a As As' P
                                          {| bindex := a';
                                             indexb := {| ibound := n;
                                                          boundi := nth_error_app _ (As ++ [a]) As' n nth |} |}.
  Proof.
    intros.
    destruct (eq_nat_dec (List.length As) n ); subst.
    - rewrite (BoundedIndex_app_comm_cons_nth_eq
                 A_eq_dec As As' _ _ _  (List.length As)
                 (nth_error_app _ (As ++ [a]) As'
                                (Datatypes.length As) nth)
                 nth').
      erewrite <- BoundedIndex_app_comm_cons_nth_eq; eauto.
      eapply Ensemble_BoundedIndex_app_equiv; auto.
    - assert (nth_error As n = Some a') by
          (generalize n nth n0; clear; induction As; destruct n; simpl; intros;
           try congruence;
           [destruct n; discriminate
           | eauto]).
      generalize (H0 _ _ H2 H1); intros.

      erewrite (BoundedIndex_app_comm_cons_nth_eq
                 A_eq_dec As As' _ _ _ n
                 (nth_error_app _ (As ++ [a]) As'
                                n nth)).
      erewrite <- BoundedIndex_app_comm_cons_nth_eq; eauto.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
      Grab Existential Variables.
      rewrite <- app_assoc; simpl; apply nth_error_app; eassumption.
      apply nth_error_app; eassumption.
      apply nth_error_app; eassumption.
  Qed.

  Lemma Iterate_Ensemble_equiv' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall a n (nth : nth_error Visited n = Some a),
         P {| bindex := a;
              indexb := {| ibound := n;
                           boundi := nth_error_app _ _ _ _ nth |} |})
      -> (Iterate_Ensemble_BoundedIndex' Visited Remaining P ->
         forall idx, P idx).
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    revert Visited P H H0 idx n nth_n; induction Remaining; simpl; intros.
    - eapply Ensemble_BoundedIndex_nth_eq with (a := idx); auto.
    - split_and.
      assert (nth_error ((Visited ++ [a]) ++ Remaining) n = Some idx)
        as nth_n'
          by (rewrite <- app_assoc; simpl; assumption).
      generalize (IHRemaining _ _ (Ensemble_nth_error_app A_eq_dec _ _ _ _ P H1 H) H2 _ _ nth_n').
      unfold Ensemble_BoundedIndex_app_comm_cons, eq_rect; destruct (app_comm_cons' a Visited Remaining).
      intros; erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth_n); eauto.
      Grab Existential Variables.
      rewrite app_nil_r in nth_n; assumption.
  Qed.

  Lemma Iterate_Ensemble_equiv'' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx)
      -> Iterate_Ensemble_BoundedIndex' Visited Remaining P.
    induction Remaining; simpl; auto.
    intros; split; eauto.
    eapply IHRemaining; intros; eauto.
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    eapply Ensemble_BoundedIndex_app_equiv; eauto.
    Grab Existential Variables.
    rewrite <- app_assoc in nth_n; simpl in nth_n; eassumption.
  Qed.

  Lemma Iterate_Ensemble_equiv_filter' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
           (filter : Ensemble nat)
           (filter_dec : DecideableEnsemble filter),
      (forall a n (nth : nth_error Visited n = Some a),
         filter n ->
         P {| bindex := a;
              indexb := {| ibound := n;
                           boundi := nth_error_app _ _ _ _ nth |} |})
      -> (Iterate_Ensemble_BoundedIndex_filter' Visited Remaining
                                              (@dec _ _ filter_dec) P ->
          forall idx, filter (ibound (indexb idx)) -> P idx).
  Proof.
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    revert Visited filter filter_dec P H H0 idx n nth_n H1;
      induction Remaining; simpl; intros.
    - eapply Ensemble_BoundedIndex_nth_eq with (a := idx); auto.
    - revert H0; case_eq (dec (Datatypes.length Visited)); intros.
      + split_and.
        assert (nth_error ((Visited ++ [a]) ++ Remaining) n = Some idx)
          as nth_n'
            by (rewrite <- app_assoc; simpl; assumption).
        generalize (IHRemaining
                      _ filter filter_dec _
                      (Ensemble_nth_error_app_filter
                         A_eq_dec _ _ _ _ P
                         filter filter_dec (fun _ => H3) H)
                      H4 _ _ nth_n').
        unfold Ensemble_BoundedIndex_app_comm_cons, eq_rect.
        destruct (app_comm_cons' a Visited Remaining).
        clear H.
        intros; erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth_n); eauto.
      + assert (nth_error ((Visited ++ [a]) ++ Remaining) n = Some idx)
        as nth_n'
          by (rewrite <- app_assoc; simpl; assumption).
        assert (forall P, filter (Datatypes.length Visited) -> P)
          as H' by
              (intros P' filt_a; apply dec_decides_P in filt_a;
               congruence).
        assert (nth_error (Visited ++ (a :: Remaining))
                           (Datatypes.length Visited) = Some a)
               as nth_a
                 by (clear; induction Visited; simpl; auto).
        generalize (IHRemaining
                    _ filter filter_dec _
                    (Ensemble_nth_error_app_filter
                       A_eq_dec _ _ _ nth_a P
                       filter filter_dec (H' _) H)
                    H2 _ _ nth_n').
      unfold Ensemble_BoundedIndex_app_comm_cons, eq_rect.
      destruct (app_comm_cons' a Visited Remaining).
      clear H.
      intros; erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth_n); eauto.
      Grab Existential Variables.
      rewrite app_nil_r in nth_n; assumption.
  Qed.

  Lemma Iterate_Ensemble_equiv_filter'' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
           (filter : Ensemble nat)
           (filter_dec : DecideableEnsemble filter),
      (forall idx, filter (ibound (indexb idx)) -> P idx)
      -> Iterate_Ensemble_BoundedIndex_filter'
           Visited Remaining
           (@dec _ _ filter_dec) P.
  Proof.
    induction Remaining; simpl; auto.
    intros; case_eq (dec (Datatypes.length Visited)); try split; eauto.
    - eapply H; apply dec_decides_P; simpl; auto.
    - eapply IHRemaining; intros; eauto.
      intros; destruct idx as [idx [n nth_n] ]; simpl in *.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
    - intros; eapply IHRemaining; intros; eauto.
      intros; destruct idx as [idx [n nth_n] ]; simpl in *.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
    Grab Existential Variables.
    rewrite <- app_assoc in nth_n; simpl in nth_n; eassumption.
    rewrite <- app_assoc in nth_n; simpl in nth_n; eassumption.
  Qed.

  Definition Iterate_Ensemble_BoundedIndex
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound)) : Prop :=
    Iterate_Ensemble_BoundedIndex' [] Bound P.

  Definition Iterate_Ensemble_BoundedIndex_filter
          (Bound : list string)
          (filter : nat -> bool)
          (P : Ensemble (BoundedIndex Bound))
  : Prop :=
    Iterate_Ensemble_BoundedIndex_filter' [] Bound filter P.

  Lemma refine_Iterate_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As)),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex As P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Lemma refine_Iterate_Ensemble_filter {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As))
           (filter : Ensemble nat)
           (filter_dec : DecideableEnsemble filter),
      refine {b | decides b (forall idx : BoundedIndex As,
                               filter (ibound idx) -> P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex_filter
                               As (@dec _ _ filter_dec) P )}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv_filter' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H.
    apply Iterate_Ensemble_equiv_filter''; auto using string_dec.
  Qed.

  Lemma refine_decides_Equiv_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P P' : Ensemble (BoundedIndex As))
           (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (forall idx : BoundedIndex As, P' idx)}.
  Proof.
    intros * equiv_P'_P v Comp_v.
    inversion_by computes_to_inv; constructor; destruct v; simpl in *.
    intros; eapply equiv_P'_P; eauto.
    unfold not; intros; eapply Comp_v; eapply equiv_P'_P; eauto.
  Qed.

  Corollary Iterate_Ensemble_filter_neq {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As))
           (Ridx : BoundedIndex As),
    (forall idx : BoundedIndex As, idx <> Ridx -> P idx)
    <-> (@Iterate_Ensemble_BoundedIndex_filter
           As (fun idx =>
                 if (eq_nat_dec (ibound Ridx) idx)
                 then false else true) P ).
  Proof.
    intros.
    assert (forall a : nat,
              (if eq_nat_dec (ibound Ridx) a then false else true) = true
              <-> a <> ibound Ridx)
      as filter_dec'
      by (intros; find_if_inside; try rewrite e; intuition).
    assert ((forall idx : BoundedIndex As, idx <> Ridx -> P idx)
            <-> (forall idx  : BoundedIndex As,
                   ibound idx <> ibound Ridx -> P idx)).
    { split; intros; eauto.
      apply H; destruct idx as [idx [n nth_n] ];
      destruct Ridx as [Ridx [n' nth_n'] ]; simpl in *.
      unfold not; intros; apply H0; injection H1; auto.
      apply H; unfold not; intros; apply H0.
      destruct idx as [idx [n nth_n] ];
        destruct Ridx as [Ridx [n' nth_n'] ]; simpl in *.
      clear H0; revert nth_n; rewrite H1; intros.
      assert (Ridx = idx) by
          (rewrite nth_n' in nth_n; congruence).
      revert nth_n' nth_n; rewrite H0.
      intros; repeat f_equal.
      apply (eq_proofs_unicity_Opt_A string_dec).
    }
    rewrite H.
    split; intros.
    - eapply Iterate_Ensemble_equiv_filter'' with
      (filter := fun idx => idx <> ibound Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |}); eauto.
      apply string_dec.
    - eapply Iterate_Ensemble_equiv_filter'  with
      (Visited := [])
      (filter := fun idx => idx <> ibound Ridx)
        (filter_dec := {|dec_decides_P := filter_dec' |});
      unfold dec; eauto using string_dec.
      intros; destruct n; simpl in *; discriminate.
  Qed.

  Lemma refine_Iterate_Equiv_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As As' : list string)
           (P : Ensemble (BoundedIndex As))
           (P' : Ensemble (BoundedIndex As'))
           (equiv_P'_P : (forall idx, P idx) <-> (forall idx', P' idx')),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex As' P')}.
  Proof.
    intros; setoid_rewrite refine_Iterate_Ensemble; try eassumption.
    intros v Comp_v.
    inversion_by computes_to_inv; constructor; destruct v; simpl in *.
    apply Iterate_Ensemble_equiv'' with (Visited := []);
      eauto using string_dec; simpl.
    apply equiv_P'_P; intros;
    apply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec; simpl.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply Comp_v.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
    apply equiv_P'_P;
    apply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec; simpl.
    destruct n; simpl; intros; discriminate.
  Qed.

  (* So that things play nicely with setoid rewriting *)
  Definition If_Then_Else {A}  (b : bool) (t e : A)
    := if b then t else e.

  Program Fixpoint Iterate_Decide_Comp' (A : Set)
          (Remaining Visited : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        Bind {b' |
              decides b' (P {| bindex := a;
                               indexb := {| ibound := List.length Visited;
                                            boundi := _ |} |})}%comp
             (fun b' =>
                If_Then_Else b'
                             (Iterate_Decide_Comp' _ Remaining' (Visited ++ [a]) _)
                             (ret false))
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.

  Lemma refine_Iterate_Decided_Ensemble' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      refine {b | decides b (Iterate_Ensemble_BoundedIndex' Visited Remaining P)}
             (Iterate_Decide_Comp' _ Remaining Visited P).
  Proof.
    induction Remaining; simpl; intros.
    - econstructor; inversion_by computes_to_inv; subst; simpl; auto.
    - econstructor; apply computes_to_inv in H; destruct_ex;
      split_and; inversion_by computes_to_inv; subst.
      destruct x; simpl in *.
      {  destruct v; simpl in *; intuition; intros; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ H1).
           intros; inversion_by computes_to_inv; simpl in *; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ H1).
           intros; inversion_by computes_to_inv; simpl in *; eauto.
      }
      { inversion_by computes_to_inv; subst; simpl; intuition. }
  Qed.

  Definition Iterate_Decide_Comp
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound))
  : Comp bool :=
    Iterate_Decide_Comp' _ Bound [] P.

  Definition Iterate_Decide_Comp_BoundedIndex
  : forall (Bound : list string)
           (P : Ensemble (BoundedIndex Bound)),
      refine {b | decides b (forall Ridx', P Ridx')}
             (Iterate_Decide_Comp _ P).
  Proof.
    intros.
    setoid_rewrite refine_Iterate_Ensemble; auto using string_dec.
    setoid_rewrite refine_Iterate_Decided_Ensemble'; auto using string_dec.
    reflexivity.
  Qed.

  (* Variants for inserting additional assumptions into the
   decision procedure. *)
  Program Lemma refine_Iterate_Ensemble_Pre {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As))
           (Q : Prop),
      refine {b | Q -> decides b (forall idx : BoundedIndex As, P idx)}
             {b | Q -> decides b (@Iterate_Ensemble_BoundedIndex As P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *; apply H in H0.
    intros; eapply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H0.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Program Fixpoint Iterate_Decide_Comp'_Pre (A : Set)
          (Remaining Visited : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
          (Q : Prop)
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        Bind {b' | Q ->
              decides b' (P {| bindex := a;
                               indexb := {| ibound := List.length Visited;
                                            boundi := _ |} |})}%comp
             (fun b' =>
                If_Then_Else b'
                             (Iterate_Decide_Comp'_Pre _ Remaining' (Visited ++ [a]) _ Q)
                             (ret false))
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_comm_cons _ _ _ P).
  Defined.

  Lemma refine_Iterate_Decided_Ensemble'_Pre {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
           (Q : Prop),
      refine {b | Q -> decides b (Iterate_Ensemble_BoundedIndex' Visited Remaining P)}
             (Iterate_Decide_Comp'_Pre _ Remaining Visited P Q).
  Proof.
    induction Remaining; simpl; intros.
    - econstructor; inversion_by computes_to_inv; subst; simpl; auto.
    - econstructor; apply computes_to_inv in H; destruct_ex;
      split_and; inversion_by computes_to_inv; subst.
      destruct x; simpl in *.
      {  destruct v; simpl in *; intuition; intros; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ _ H1).
           intros; inversion_by computes_to_inv; simpl in *; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ _ H1).
           intros; inversion_by computes_to_inv; simpl in *; eauto.
           eapply H0; eauto.
      }
      { inversion_by computes_to_inv; subst; simpl; intuition. }
  Qed.

  Definition Iterate_Decide_Comp_Pre
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound))
          (Q : Prop)
  : Comp bool :=
    Iterate_Decide_Comp'_Pre _ Bound [] P Q.

  Definition Iterate_Decide_Comp_BoundedIndex_Pre
  : forall (Bound : list string)
           (P : Ensemble (BoundedIndex Bound))
           (Q : Prop),
      refine {b | Q -> decides b (forall Ridx', P Ridx')}
             (Iterate_Decide_Comp_Pre _ P Q).
  Proof.
    intros.
    setoid_rewrite refine_Iterate_Ensemble_Pre; auto using string_dec.
    setoid_rewrite refine_Iterate_Decided_Ensemble'_Pre; auto using string_dec.
    reflexivity.
  Qed.

  Lemma decides_True :
    refine {b | decides b True}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_True_Pre (Q : Prop) :
    refine {b | Q -> decides b True}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_2_True (A : Type) (B : A -> Type) :
    refine {b' | decides b' (forall a : A, B a -> True)}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_3_True (A B : Type) (C : B -> Type) :
    refine {b' | decides b' (A -> forall b : B, C b -> True)}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_neq (A : Type) (B : Prop) (a : A) :
    refine {b' | decides b' (a <> a -> B)}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
    congruence.
  Qed.

  Global Add Parametric Morphism A
  : If_Then_Else
      with signature
      (@eq bool) ==> (@refine A) ==> (@refine A) ==> (@refine A)
        as refine_If_Then_Else_if.
  Proof.
    compute.
    intros; destruct_head bool; intros; eauto.
  Qed.

  Definition Ensemble_opt_BoundedIndex_app_comm_cons {A : Set}
    (a : A)
    (As As' : list A)
    (P : BoundedIndex (As ++ a :: As') -> option Prop)
  : BoundedIndex ((As ++ [a]) ++ As') -> option Prop.
    rewrite app_comm_cons' in P; exact P.
  Defined.

  Program Fixpoint Iterate_Decide_Comp_opt' (A : Set)
          (Remaining Visited : list A)
          (P : BoundedIndex (Visited ++ Remaining) -> option Prop )
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        match (P {| bindex := a;
                    indexb := {| ibound := List.length Visited;
                                 boundi := _ |} |}) with
          | Some P' => b' <- {b' | decides b' P'};
                      If_Then_Else b'
                                   (Iterate_Decide_Comp_opt' _ Remaining' (Visited ++ [a])
                                                             (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P))
                                   (ret false)
          | None => (Iterate_Decide_Comp_opt' _ Remaining' (Visited ++ [a])
                                              (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P))
        end
    end%comp.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.

  Lemma refine_Iterate_Decide_Comp'
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : BoundedIndex (Visited ++ Remaining)
                -> option Prop),
      refine (@Iterate_Decide_Comp' _ Remaining Visited (fun idx => match P idx with
                                                                      | Some P' => P'
                                                                      | None => True
                                                                    end))
             (@Iterate_Decide_Comp_opt' _ Remaining Visited P).
    induction Remaining; simpl; intros.
    - reflexivity.
    - destruct (P ``(a)).
      + f_equiv; unfold pointwise_relation; intros.
        destruct a0; simpl; try reflexivity.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
      + rewrite decides_True; simplify with monad laws; simpl.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp
  : forall (Bound : list string)
           (P : BoundedIndex Bound -> option Prop),
      refine (@Iterate_Decide_Comp _ (fun idx => match P idx with
                                                 | Some P' => P'
                                                 | None => True
                                               end))
             (@Iterate_Decide_Comp_opt' _ Bound [] P).
  Proof.
    intros; unfold Iterate_Decide_Comp;
    rewrite refine_Iterate_Decide_Comp'.
    reflexivity.
    apply string_dec.
  Qed.

  Program Fixpoint Iterate_Decide_Comp_opt'_Pre (A : Set)
          (Remaining Visited : list A)
          (P : BoundedIndex (Visited ++ Remaining) -> option Prop)
          (Q : Prop)
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        match (P {| bindex := a;
                    indexb := {| ibound := List.length Visited;
                                 boundi := _ |} |}) with
          | Some P' => b' <- {b' | Q -> decides b' P'};
                      If_Then_Else b'
                                   (Iterate_Decide_Comp_opt'_Pre _ Remaining' (Visited ++ [a])
                                                             (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P) Q)
                                   (ret false)
          | None => (Iterate_Decide_Comp_opt'_Pre _ Remaining' (Visited ++ [a])
                                              (Ensemble_opt_BoundedIndex_app_comm_cons _ _ _ P) Q)
        end
    end%comp.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.

  Lemma refine_Iterate_Decide_Comp'_Pre
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : BoundedIndex (Visited ++ Remaining) -> option Prop)
           (Q : Prop),
      refine (@Iterate_Decide_Comp'_Pre _ Remaining Visited
                                        (fun idx => match P idx with
                                                      | Some P' => P'
                                                      | None => True
                                                    end) Q)
             (@Iterate_Decide_Comp_opt'_Pre _ Remaining Visited P Q).
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - destruct (P ``(a)).
      + f_equiv; unfold pointwise_relation; intros.
        destruct a0; simpl; try reflexivity.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
      + rewrite decides_True_Pre; simplify with monad laws; simpl.
        setoid_rewrite <- IHRemaining; f_equiv.
        unfold Ensemble_BoundedIndex_app_comm_cons,
        Ensemble_opt_BoundedIndex_app_comm_cons; simpl.
        destruct (app_comm_cons' a Visited Remaining); simpl.
        reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp_Pre
  : forall (Bound : list string)
           (P : BoundedIndex Bound -> option Prop)
           (Q : Prop),
      refine (@Iterate_Decide_Comp_Pre _ (fun idx => match P idx with
                                                 | Some P' => P'
                                                 | None => True
                                               end) Q)
             (@Iterate_Decide_Comp_opt'_Pre _ Bound [] P Q).
  Proof.
    intros; unfold Iterate_Decide_Comp_Pre;
    rewrite refine_Iterate_Decide_Comp'_Pre.
    reflexivity.
    apply string_dec.
  Qed.

  Lemma refine_Iterate_Decide_Comp_equiv_Pre
        (Q Q' : Prop)
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P P' : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx -> P' idx)
      -> (forall idx, ~ P idx -> ~ P' idx)
      -> (Q -> Q')
      -> refine (@Iterate_Decide_Comp'_Pre _ Remaining Visited P' Q)
                (@Iterate_Decide_Comp'_Pre _ Remaining Visited P Q').
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - f_equiv.
      + unfold refine; intros; inversion_by computes_to_inv; subst;
        econstructor; destruct v; simpl in *; eauto.
      + unfold pointwise_relation; intros b; destruct b; simpl.
        apply IHRemaining; eauto.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        reflexivity.
  Qed.

  (* Consequences of ith_replace_BoundIndex_neq and ith_replace_BoundIndex_eq on updates *)

  Lemma refine_SatisfiesSchemaConstraints_self
  : forall qsSchema
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup tup' : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides b (SatisfiesSchemaConstraints Ridx tup tup')}
             match (schemaConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr => {b | decides b (Constr tup tup') }
               | None => ret true
             end.
  Proof.
    unfold SatisfiesSchemaConstraints.
    intros; destruct (schemaConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
  Qed.

  Lemma refine_SatisfiesSchemaConstraints
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides b
                          (forall tup',
                             GetUnConstrRelation qs Ridx tup'
                             -> SatisfiesSchemaConstraints Ridx tup tup')}
             match (schemaConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr =>
                 {b | decides b (forall tup',
                                   GetUnConstrRelation qs Ridx tup'
                                   -> Constr tup tup')}
               | None => ret true
             end.
  Proof.
    unfold SatisfiesSchemaConstraints.
    intros; destruct (schemaConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesSchemaConstraints'
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine {b | decides b
                          (forall tup',
                             GetUnConstrRelation qs Ridx tup'
                             -> SatisfiesSchemaConstraints Ridx tup' tup)}
             match (schemaConstraints (QSGetNRelSchema qsSchema Ridx)) with
                 Some Constr =>
                 {b | decides b (forall tup',
                                   GetUnConstrRelation qs Ridx tup'
                                   -> Constr tup' tup)}
               | None => ret true
             end.
  Proof.
    unfold SatisfiesSchemaConstraints.
    intros; destruct (schemaConstraints (QSGetNRelSchema qsSchema Ridx));
    eauto using decides_True.
    reflexivity.
    apply decides_2_True.
  Qed.

  Lemma refine_SatisfiesCrossConstraints
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine
        (@Iterate_Decide_Comp _
                              (fun Ridx' =>
                                 SatisfiesCrossRelationConstraints
                                   Ridx Ridx' tup
                                   (GetUnConstrRelation qs Ridx')))
        (@Iterate_Decide_Comp_opt' _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end)) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.

  Lemma refine_Iterate_Decide_Comp_equiv
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P P' : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx -> P' idx) ->
      (forall idx, ~ P idx -> ~ P' idx) ->
      refine (@Iterate_Decide_Comp' _ Remaining Visited P')
             (@Iterate_Decide_Comp' _ Remaining Visited P).
  Proof.
    induction Remaining; simpl; intros.
    - reflexivity.
    - f_equiv.
      + unfold refine; intros; inversion_by computes_to_inv; subst;
        econstructor; destruct v; simpl in *; eauto.
      + unfold pointwise_relation; intros b; destruct b; simpl.
        apply IHRemaining.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        unfold Ensemble_BoundedIndex_app_comm_cons; simpl;
        destruct (app_comm_cons' a Visited Remaining); simpl; eauto.
        reflexivity.
  Qed.

  Lemma refine_SatisfiesCrossConstraints_Pre (Q : Prop)
  : forall qsSchema qs
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx))),
      refine
        (@Iterate_Decide_Comp_Pre _
                              (fun Ridx' =>
                                 SatisfiesCrossRelationConstraints
                                   Ridx Ridx' tup
                                   (GetUnConstrRelation qs Ridx')) Q)
        (@Iterate_Decide_Comp_opt'_Pre _ _ []
                                   (fun Ridx' =>
                                      match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
                                        | Some CrossConstr =>
                                          Some (CrossConstr tup (GetUnConstrRelation qs Ridx'))
                                        | None => None
                                      end) Q) .
  Proof.
    intros.
    setoid_rewrite <- refine_Iterate_Decide_Comp_Pre.
    unfold SatisfiesCrossRelationConstraints; f_equiv.
    apply functional_extensionality; intros.
    destruct BuildQueryStructureConstraints; reflexivity.
  Qed.


  Lemma DeletePrimaryKeysOK {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           DeletedTuples
           attrlist1 attrlist2,
      refine {b | (forall tup tup',
                          GetUnConstrRelation qs Ridx tup
                          -> GetUnConstrRelation qs Ridx tup'
                          -> (FunctionalDependency_P attrlist1 attrlist2 tup tup'))
                     -> decides b (DeletePreservesSchemaConstraints
                                      (GetUnConstrRelation qs Ridx)
                                      DeletedTuples
                                      (FunctionalDependency_P attrlist1 attrlist2))}
             (ret true).
  Proof.
    unfold DeletePreservesSchemaConstraints, FunctionalDependency_P;
    intros * v Comp_v; inversion_by computes_to_inv; subst.
    constructor; simpl.
    intros.
    unfold EnsembleDelete in *; destruct H0; destruct H1; eauto.
  Qed.

  Local Transparent Count.

  Lemma refine_Where' {A B} :
    forall (P : Ensemble A)
           (P_dec : DecideableEnsemble P)
           (bod : Comp (list B)),
    forall a,
      refine
             (if (dec a) then
                bod
              else
                (ret []))
             (Where (P a) bod)%QuerySpec.
  Proof.
    unfold refine, Query_Where; intros.
    inversion_by computes_to_inv.
    caseEq (dec a).
    apply dec_decides_P in H; eauto.
    rewrite H1; eauto.
    unfold not; intros H'; apply dec_decides_P in H'; congruence.
  Qed.

  Require Import flattenCompListProperties.

  Lemma In_UnConstrQuery_In {qsSchema} {A}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx bod results,
      UnConstrQuery_In qs Ridx bod ↝ results
      -> forall (a : A), List.In a results ->
                         exists (tup' : IndexedTuple) results',
                           Ensembles.In _ (GetUnConstrRelation qs Ridx) tup'
                           /\ bod tup' ↝ results'
                           /\ List.In a results'.
  Proof.
    unfold UnConstrQuery_In, QueryResultComp; intros;
    inversion_by computes_to_inv.
    unfold EnsembleListEquivalence in *; intuition.
    rewrite map_map in H2.
    remember (GetUnConstrRelation qs Ridx); clear Hequ;
    revert u a results H0 H2 H H3;
    induction x; simpl in *; intros;
    inversion_by computes_to_inv; subst.
    simpl in H0; intuition.
    apply in_app_or in H0; intuition.
    exists a x0; intuition; eapply H3; eauto.
    inversion H; subst.
    destruct (IHx (fun tup => tup <> a /\ u tup) _ _ H1 H4 H7).
    unfold Ensembles.In; intros; intuition; subst; eauto.
    eapply H3 in H8; intuition.
    intuition.
    apply H3; intuition.
    destruct_ex; intuition.
    exists x2 x3; intuition.
    apply H5.
  Qed.

  Lemma In_UnConstrQuery_In' {qsSchema} {A}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx
           (bod : Tuple -> Comp (list A))
           results
           (a : A) (tup' : IndexedTuple),
      Ensembles.In _ (GetUnConstrRelation qs Ridx) tup'
      -> (forall results', bod tup' ↝ results'
                           -> List.In a results')
      -> UnConstrQuery_In qs Ridx bod ↝ results
      -> List.In a results.
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, Ensembles.In; intros.
    inversion_by computes_to_inv.
    unfold EnsembleListEquivalence in *; intuition.
    rewrite map_map in H3.
    remember (GetUnConstrRelation qs Ridx); clear Hequ;
    revert u a results H H0 H1 H3 H4;
    induction x; simpl in *; intros;
    inversion_by computes_to_inv; subst.
    simpl in *; intuition; eapply H4; eauto.
    apply H4 in H; intuition; subst; apply in_or_app; eauto.
    right; inversion H1; subst.
    eapply (IHx (fun tup => tup <> a /\ u tup)); eauto.
    intuition; subst; eauto.
    apply H4; eauto.
    unfold Ensembles.In; intuition; intros; eauto.
    rewrite H4 in H9; intuition.
    subst; eauto.
    apply H4; eauto.
  Qed.

  Lemma DeleteForeignKeysCheck {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx Ridx' : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (DeletedTuples : Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (Delete_dec : DecideableEnsemble DeletedTuples)
           (attr : Attributes (schemaHeading (QSGetNRelSchema _ Ridx)))
           (attr' : Attributes (schemaHeading (QSGetNRelSchema _ Ridx')))
           (tupmap : Domain (schemaHeading (QSGetNRelSchema _ Ridx)) attr
                     -> Domain (schemaHeading (QSGetNRelSchema _ Ridx')) attr')
           (AgreeDelete : forall tup tup',
                            tupleAgree tup tup' [attr] ->
                            DeletedTuples tup ->
                            DeletedTuples tup')
           (attr_eq_dec : Query_eq (Domain (schemaHeading (QSGetNRelSchema _ Ridx)) attr))
                      (P : Prop)
           (ForeignKey_P_P :
              P -> (forall tup' : IndexedTuple,
                        GetUnConstrRelation qs Ridx' tup' ->
                        ForeignKey_P attr' attr tupmap tup'
                                     (GetUnConstrRelation qs Ridx)))

           (tup_map_inj : forall a a', tupmap a = tupmap a' -> a = a'),
      refine {b' |
              P ->
               decides b'
                       (DeletePreservesCrossConstraints
                       (GetUnConstrRelation qs Ridx)
                       (GetUnConstrRelation qs Ridx')
                       DeletedTuples
                       (ForeignKey_P attr' attr tupmap))}
             (x <- Count (For (UnConstrQuery_In
                                 qs Ridx'
                                 (fun tup' =>
                                    UnConstrQuery_In
                                      qs Ridx
                                      (fun tup =>
                                         Where (DeletedTuples tup)
                                         Where (tupmap (tup attr) = tup' attr')
                                         Return ()))));
              ret (match x with
                       0  => true
                     | S _ => false
                   end)).
  Proof.
    simpl; unfold ForeignKey_P; intros.
    intros v Comp_v.
    apply computes_to_inv in Comp_v; destruct_ex; split_and.
    unfold Count in *; inversion_by computes_to_inv.
    destruct x0; simpl in *; subst; inversion_by computes_to_inv; subst;
    constructor; simpl; unfold not;
    unfold DeletePreservesCrossConstraints; intros.
    - destruct (ForeignKey_P_P H _ H1) as [tup2 [In_tup2 Agree_tup2]].
      eexists; intuition eauto.
      unfold EnsembleDelete; constructor; unfold In; intros; eauto.
      unfold Complement, Ensembles.In, not; intros.
      unfold Query_For in *; inversion_by computes_to_inv.
      rewrite Permutation_nil in H4; symmetry in H5; eauto.
      apply (fun x => In_UnConstrQuery_In' _ _ _ _ () _ H1 x H4).
      intros; apply (fun x => In_UnConstrQuery_In' _ _ _ _ () _ In_tup2 x H0).
      intros.
      unfold Query_Where in H5; apply computes_to_inv in H6;
      simpl in *; intuition.
      apply computes_to_inv in H6; split_and.
      rewrite Agree_tup2 in H9; pose proof (H9 (refl_equal _)) as H';
      apply computes_to_inv in H'; simpl in *; subst; simpl; eauto.
    - unfold Query_For in *; inversion_by computes_to_inv.
      eapply In_UnConstrQuery_In with (a := u) in H2; destruct_ex;
      intuition.
      pose proof (H4 _ H2); pose proof (H1 _ H2); destruct_ex;
      intuition.
      eapply In_UnConstrQuery_In with (a := u) in H0; destruct_ex;
      intuition.
      unfold EnsembleDelete in *; inversion H6; subst;
      unfold Ensembles.In, Complement, In in *.
      unfold Query_Where in H0; apply computes_to_inv in H0;
      intuition.
      case_eq (@dec _ _ Delete_dec x5); intros.
      + apply Delete_dec in H0; pose proof (H14 H0) as H'.
        apply computes_to_inv in H'; split_and.
        rewrite H10 in *.
        destruct (A_eq_dec (indexedTuple x5 attr) (indexedTuple x3 attr)).
        * rewrite e in *;
          pose proof (H16 (refl_equal _)) as e'; apply computes_to_inv in e'; simpl in *; subst.
          apply H13; eapply AgreeDelete; eauto.
          unfold tupleAgree; simpl; intros attr'' In_attr''; destruct In_attr'';
          [rewrite H18 in *; eauto | intuition ].
        * rewrite H17 in H12; simpl in *; eauto.
      + rewrite H15 in H12; simpl in *; eauto.
        intros H'; apply dec_decides_P in H'; congruence.
      + eapply Permutation_in; symmetry in H3; simpl; eauto.
        simpl; eauto.
  Qed.

End ConstraintCheckRefinements.

Lemma For_computes_to_In :
  forall {heading} P,
    (forall a, P a \/ ~ P a) ->
    forall seq ens,
      computes_to (For (QueryResultComp (heading := heading) ens
                                        (fun tup => Where (P tup) Return tup))) seq ->
      forall x,
        List.In x seq -> (P x /\ (exists x0, ens x0 /\ indexedTuple x0 = x)).
Proof.
  unfold refine, decides;
  unfold Query_For, QueryResultComp; intros * excl;
  induction seq as [ | head seq' IH ]; intros.

  exfalso; intuition.

  inversion_by computes_to_inv.

  pose proof (permutation_cons_in H4) as in_x0.
  apply in_split in in_x0.
  destruct in_x0 as [ x0_before [ x0_after ? ] ]; subst.
  symmetry in H4. apply Permutation_cons_app_inv in H4.

  rewrite map_map in H5.
  destruct (flatten_CompList_app_cons_inv _ excl _ _ _ _ H5) as [ x1_before [ x1_middle [ head' [ x1_after (_eq & in_orig & before & middle & after) ] ] ] ]; subst.

  unfold boxed_option in middle; simpl in middle.
  apply computes_to_inv in middle.
  destruct middle as [head'' (middle1 & middle2)].
  apply computes_to_inv in middle1.
  apply computes_to_inv in middle2.
  destruct middle1 as ( spec1 & spec2 ).
  destruct middle2 as [ nil' (ret_nil & ret_cons) ].
  apply computes_to_inv in ret_nil; subst.
  rewrite app_nil_r in *; subst.
  apply computes_to_inv in ret_cons; subst.

  rewrite singleton_neq_nil in spec2.
  destruct (excl head') as [ H | H ]; try solve [exfalso; intuition].
  specialize (spec1 H).

  apply computes_to_inv in spec1.
  injection spec1; intros; subst.

  destruct H0.

  - subst x; split; [ | exists head'; split; [ apply H3  | ] ]; auto.
  - pose proof (EnsembleListEquivalence_slice _ _ _ H3) as smaller_equiv.
    pose proof (flatten_CompList_app _ _ _ _ before after) as flatten_app.
    set (smaller_ens := (fun x : IndexedTuple => ens x /\ ~ In x x1_middle)).
    split.

    + eapply H1; try assumption.
      econstructor; [ | constructor; symmetry; eassumption ].
      econstructor.
      constructor.

      apply smaller_equiv.

      unfold boxed_option in *.
      rewrite !map_app, !map_map.
      apply flatten_app.
    + assert (exists x0 : IndexedTuple, smaller_ens x0 /\ indexedTuple x0 = x) as temp.
      apply H2; try eassumption.
      econstructor; [ | constructor; symmetry; eassumption ].
      econstructor.
      constructor.

      eassumption.
      unfold boxed_option in *.
      rewrite !map_app, !map_map.
      apply flatten_app.

      destruct temp as [ x0 ( ens_x & _eq ) ]; subst.
      eexists; split; eauto.

      unfold smaller_ens in ens_x; intuition.
Qed.


Lemma For_computes_to_nil :
  forall {heading} P,
  forall ens,
    computes_to (For (QueryResultComp (heading := heading) ens
                                      (fun tup => Where (P tup) Return tup))) [] ->
    forall x,
      ens x -> ~ (P (indexedTuple x)).
Proof.
  unfold refine, decides, Count, Query_For, QueryResultComp; intros **.

                                            inversion_by computes_to_inv.
  symmetry in H2; apply Permutation_nil in H2; subst.
  apply H1 in H0.
  apply in_split in H0.
  destruct H0 as [ x1_before [ x1_after _eq ] ]; subst.

  rewrite map_map in H3.
  eapply flatten_CompList_nil; unfold boxed_option; eauto; intuition.
Qed.

Lemma decidable_excl :
  forall {A : Type} (P : Ensemble A) (P_dec : DecideableEnsemble P),
    (forall (a: A), P a \/ ~ P a).
Proof.
  intros ** a.
  destruct (dec a) eqn:eqdec;
    [ rewrite dec_decides_P in eqdec | rewrite Decides_false in eqdec ]; intuition.
Qed.

Lemma refine_constraint_check_into_query :
  forall {schm tbl} P (P_dec : DecideableEnsemble P),
  forall (c : UnConstrQueryStructure schm),
    refine
      (Pick (fun (b : bool) =>
               decides b
                       (exists tup2: @IndexedTuple _,
                          (GetUnConstrRelation c tbl tup2 /\ P (indexedTuple tup2)))))
      (Bind
         (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return tup))))
         (fun count => ret (negb (beq_nat count 0)))).
Proof.
  unfold refine, Count, UnConstrQuery_In; intros * excl * pick_comp ** .
  inversion_by computes_to_inv; subst.

  constructor.

  destruct (Datatypes.length x0) eqn:eq_length;
    destruct x0 as [ | head tail ]; simpl in *; try discriminate; simpl.

  pose proof (For_computes_to_nil _ (GetUnConstrRelation c tbl) H0).
  rewrite not_exists_forall; intro a; rewrite not_and_implication; intros.
  apply H; trivial.

  apply For_computes_to_In with (x := head) in H0; try solve [intuition].
  destruct H0 as ( p & [ x0 ( in_ens & _eq ) ] ); subst.
  eexists; split; eauto.

  apply decidable_excl; assumption.
Qed.

Definition refine_foreign_key_check_into_query {schm tbl} :=
  @refine_constraint_check_into_query schm tbl.

Require Import tupleAgree Bool AdditionalRefinementLemmas.

Lemma refine_functional_dependency_check_into_query :
  forall {schm : QueryStructureSchema} {tbl} ref args1 args2,
    DecideableEnsemble (fun x : Tuple => tupleAgree_computational ref x args1 /\
                                         ~ tupleAgree_computational ref x args2) ->
    forall c : UnConstrQueryStructure schm,
      ((forall tup' : IndexedTuple,
          GetUnConstrRelation c tbl tup' -> tupleAgree ref tup' args1 -> tupleAgree ref tup' args2) <->
       (forall tup' : IndexedTuple,
          ~ (GetUnConstrRelation c tbl tup' /\ tupleAgree ref tup' args1 /\ ~ tupleAgree ref tup' args2))) ->
      refine
        (Pick (fun (b : bool) =>
                 decides b
                         (forall tup' : IndexedTuple,
                            GetUnConstrRelation c tbl tup' ->
                            tupleAgree ref tup' args1 ->
                            tupleAgree ref tup' args2)))
        (Bind (Count
                 For (UnConstrQuery_In c tbl
                                       (fun tup : Tuple =>
                                          Where (tupleAgree_computational ref tup args1 /\
                                                 ~ tupleAgree_computational ref tup args2)
                                                Return tup)))
              (fun count => ret (beq_nat count 0))).
Proof.
  intros * is_dec ** .

  setoid_replace (forall tup', GetUnConstrRelation c tbl tup' ->
                               tupleAgree ref tup' args1 -> tupleAgree ref tup' args2)
  with           (forall tup', ~ (GetUnConstrRelation c tbl tup' /\
                                  tupleAgree ref tup' args1 /\
                                  ~ tupleAgree ref tup' args2)); eauto.

  setoid_rewrite refine_decide_negation.
  setoid_rewrite tupleAgree_equivalence.
  setoid_rewrite (refine_constraint_check_into_query
                    (fun (x: Tuple ) => tupleAgree_computational ref x args1 /\
                                        ~ tupleAgree_computational ref x args2)); try assumption.

  Opaque Query_For Count.
  simplify with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.

Lemma tupleAgree_refl :
  forall (h : Heading)
         (tup : @Tuple h)
         (attrlist : list (Attributes h)),
    tupleAgree tup tup attrlist.
Proof.
  unfold tupleAgree; auto.
Qed.

Lemma refine_tupleAgree_refl_True :
  forall (h : Heading)
         (tup : @Tuple h)
         (attrlist attrlist' : list (Attributes h)),
    refine {b |
            decides b (tupleAgree tup tup attrlist'
                       -> tupleAgree tup tup attrlist)}
           (ret true).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  subst; econstructor; simpl; auto using tupleAgree_refl.
Qed.

Ltac simplify_trivial_SatisfiesSchemaConstraints :=
  simpl;
  try rewrite refine_tupleAgree_refl_True;
  try setoid_rewrite decides_True;
  try setoid_rewrite decides_2_True; reflexivity.

Ltac simplify_trivial_SatisfiesCrossRelationConstraints :=
  simpl map; simpl;
    repeat match goal with
             | |- context [if _ then ret true else ret false] =>
               setoid_rewrite refine_if_bool_eta at 1
             | |- refine (Bind (Pick (fun b => decides b True)) _) _ =>
             etransitivity; [ apply refine_bind;
                              [ apply decides_True
                              | unfold pointwise_relation;
                                intro; higher_order_1_reflexivity ]
                            | rewrite refineEquiv_bind_unit at 1;
                              unfold If_Then_Else ]
             | |- refine (Bind (Pick (fun b' => decides b' (forall _ _ _, True))) _ ) _ =>
               etransitivity;
                 [ apply refine_bind;
                   [ apply decides_3_True
                   | unfold pointwise_relation;
                     intro; higher_order_1_reflexivity ]
                 | rewrite refineEquiv_bind_unit at 1;
                   unfold If_Then_Else ]

    end.
