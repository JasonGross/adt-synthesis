Require Import Program.

Require Export FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.

Require Import SetEq SetEqProperties AdditionalLemmas.

Unset Implicit Arguments.

Module FMapExtensions_fun (E: DecidableType) (Import M: WSfun E).
  Module Export BasicFacts := WFacts_fun E M.
  Module Export BasicProperties := WProperties_fun E M.

  Definition TKey := key.

  Definition FindWithDefault {A} (key: TKey) (default: A) (fmap: t A) :=
    match find key fmap with
      | Some result => result
      | None        => default
    end.

  Definition Values {A} container :=
    List.map snd (@elements A container).

  Lemma FindWithDefault_dec :
    forall {A : Type} (key : TKey) (default : A) (fmap : t A),
      { exists result,
          MapsTo key result fmap /\
          @FindWithDefault A key default fmap = result } +
      { find key fmap = None /\
        @FindWithDefault A key default fmap = default }.
  Proof.
    unfold FindWithDefault;
    intros A key default fmap;
    destruct (find key fmap) eqn:find;
    [ left; rewrite <- find_mapsto_iff in find | right ];
    eauto.
  Qed.

  Lemma Values_empty :
    forall {A}, Values (empty A) = [].
  Proof.
    intros;
    unfold Values;
    rewrite elements_empty;
    reflexivity.
  Qed.

  Definition GetValues {A: Type} (db: t A) : list A  :=
    List.map snd (elements db).

  Definition IndexedBy {A} projection tree :=
    forall key (value: A),
      MapsTo key value tree ->
      key = projection value.

  Lemma FindWithDefault_MapsTo :
    forall {A} default key (value: A) tree,
      MapsTo key value tree ->
      FindWithDefault key default tree = value.
  Proof.
    unfold FindWithDefault; intros ? ? ? ? ? maps_to.
    rewrite find_mapsto_iff in *.
    rewrite maps_to; trivial.
  Qed.

  Definition ValueFilter {A B: Type} (pred: B -> bool) :=
    (fun (key: A) (value: B) => pred value).

  Lemma ValueFilter_proper:
    forall (B: Type) (pred: B->bool),
      Proper (E.eq ==> eq ==> eq) (ValueFilter pred).
  Proof.
    unfold Proper; compute; intros; subst; trivial.
  Qed.

  Definition SameElements {A: Type} (seq: list A) (db: t A) :=
    SetEq seq (GetValues db).

  Lemma elements_iff :
    forall (elt : Type) (m : t elt) (x : key) (e : elt),
      MapsTo x e m <-> InA (eq_key_elt (elt:=elt)) (x, e) (elements (elt:=elt) m).
  Proof.
    intros; split;
    eauto using elements_1, elements_2.
  Qed.

  Lemma InA_In_snd :
    forall {A: Type} (k: key) (e: A) (l : list (key*A)),
      InA (eq_key_elt (elt:=A)) (k, e) l -> List.In e (List.map snd l).
  Proof.
    intros ? k e ? in_a;
    rewrite InA_alt, in_map_iff in *;
    destruct in_a as [(k', e') (eq0, ?)];
    destruct eq0; simpl in *;
    exists (k', e'); intuition.
  Qed.

  Lemma equiv_eq_key_elt :
    forall {A: Type}, Equivalence (eq_key_elt (elt := A)).
  Proof.
    unfold eq_key_elt;
    repeat constructor;
    simpl in *;
    intuition;
    eauto using E.eq_trans, eq_trans.
  Qed.

  Lemma equiv_eq_key :
    forall elt,
      Equivalence (eq_key (elt:=elt)).
  Proof.
    intros; unfold eq_key; intuition.
    unfold Transitive; firstorder.
    transitivity (fst y); trivial.
  Qed.

  Lemma InA_front_InA :
    forall elt,
    forall {item} front middle tail,
      InA (eq_key_elt (elt:=elt)) item front -> InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
  Proof.
    intros; intuition.
    rewrite InA_app_iff;
      [intuition | apply equiv_eq_key_elt].
  Qed.

  Lemma InA_tail_InA :
    forall elt,
    forall {item} front middle tail,
      InA (eq_key_elt (elt:=elt)) item tail -> InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
  Proof.
    intros; intuition.
    rewrite InA_app_iff;
      [intuition | apply equiv_eq_key_elt].
  Qed.

  Lemma InA_front_tail_InA :
    forall elt,
    forall {item} front middle tail,
      InA (eq_key_elt (elt:=elt)) item front \/ InA (eq_key_elt (elt:=elt)) item tail ->
      InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
  Proof.
    intros elt item front middle tail in_or;
    destruct in_or; eauto using InA_front_InA, InA_tail_InA.
  Qed.

  Lemma eq_stronger_than_eq_key_elt :
    forall {A: Type} x seq,
      InA eq x seq -> InA (eq_key_elt (elt:=A)) x seq.
  Proof.
    intros.
    apply InA_In in H.
    apply (In_InA ); eauto using equiv_eq_key_elt.
  Qed.

  Lemma in_elements_mapsto :
    forall {A: Type} k (e: A) (m: t A),
      List.In (k, e) (elements m) -> MapsTo k e m.
    intros;
    eauto using elements_2, In_InA, equiv_eq_key_elt.
  Qed.

  Lemma in_elements_after_map :
    forall {A B: Type} (proc: A -> B) (m: t A) (x: B),
      List.In x (List.map snd (elements (map proc m)))
      -> exists k pred, MapsTo k pred m /\ proc pred = x.
    intros ? ? ? ? ? in_map;
    rewrite in_map_iff in in_map;
    destruct in_map as [(k, e) (is_proc, in_elements)];
    apply in_elements_mapsto in in_elements;
    rewrite map_mapsto_iff in in_elements;
    destruct in_elements as [e_pred (is_pred, maps_to)];
    exists k e_pred;
    subst; intuition.
  Qed.

  Lemma map_list_map_fmap:
    forall {A B: Type} m (proc: A -> B),
      SetEq (GetValues (map proc m)) (List.map proc (GetValues m)).
  Proof.
    unfold GetValues; split; intros.

    apply in_elements_after_map in H;
      destruct H as [k [predecessor (maps_to, is_predecessor)]];
      rewrite in_map_iff;
      exists predecessor;
      subst;
      intuition;
      apply (InA_In_snd k), elements_1;
      trivial.

    rewrite in_map_iff in H;
      destruct H as [x0 (?, H)];
      rewrite in_map_iff in H;
      destruct H as [x1 (is_pred, ?)].

    apply (InA_In_snd (fst x1));
      rewrite <- elements_mapsto_iff;
      apply map_mapsto_iff;
      exists x0;
      split;
      [ | apply in_elements_mapsto;
          rewrite <- is_pred, <- surjective_pairing ];
      subst;
      congruence.
  Qed.


  Lemma filter_list_filter_fmap :
    forall {A: Type} m pred,
      SetEq (List.filter pred (GetValues (A:=A) m)) (GetValues (filter (ValueFilter pred) m)).
  Proof.
    intros.
    unfold SetEq; intuition.
    unfold GetValues.

    rewrite filter_In in H.
    destruct H as [inL sat].
    unfold GetValues in inL.
    apply in_map_iff in inL.
    destruct inL as [x0 (ok, inL)].

    destruct x0.
    apply in_elements_mapsto in inL.
    subst.
    simpl.

    apply (InA_In_snd k).
    apply elements_mapsto_iff.
    rewrite filter_iff.
    intuition.

    eauto using ValueFilter_proper.

    unfold GetValues in *.
    rewrite filter_In.

    rewrite in_map_iff in H.
    destruct H as [(k, e) (is_snd, is_in)].

    apply in_elements_mapsto in is_in.

    rewrite filter_iff in is_in; eauto using ValueFilter_proper.

    destruct is_in as [maps_to sat].
    compute in sat.
    simpl in *.
    subst.
    intuition.

    rewrite elements_mapsto_iff in maps_to.
    apply (InA_In_snd k).
    trivial.
  Qed.

  Lemma map_modulo_equiv :
    forall {A B: Type} (db: t A) (seq: list A),
      SameElements seq db ->
      forall (proc: A -> B),
        SameElements (List.map proc seq) (map proc db).
  Proof.
    unfold SameElements; intros.
    rewrite (@map_modulo_SetEq _ _ _ (GetValues db)); trivial.
    clear H; clear seq.
    unfold SetEq.
    symmetry.
    apply map_list_map_fmap.
  Qed.

  Lemma MapsTo_snd :
    forall {A: Type} val tree,
      (exists key, MapsTo key val tree)
      <-> List.In val (List.map snd (elements (elt:=A) tree)).
  Proof.
    split;
    intro H;
    [
      destruct H as [key mapsto];
      apply (InA_In_snd key);
      apply elements_1
    |
    rewrite in_map_iff in H;
      destruct H as [(key, val') (eq_val_val', in_lst)];
      subst; simpl;
      exists key;
      apply in_elements_mapsto
    ]; trivial.
  Qed.

  Lemma MapsTo_In :
    forall {A: Type} key (val: A) tree,
      MapsTo key val tree -> In key tree.
  Proof.
    intros.
    rewrite elements_in_iff.
    rewrite elements_mapsto_iff in *.
    eauto.
  Qed.

  Lemma in_elements_after_add:
    forall {A: Type} key (added elem: A) tree,
      (List.In elem (GetValues (add key added tree))
       -> (elem = added \/ List.In elem (GetValues tree))).
  Proof.
    unfold GetValues;
    intros ? ? ? ? ? is_in;
    rewrite <- MapsTo_snd;
    rewrite <- MapsTo_snd in is_in.

    destruct is_in as [key' map_add];
      rewrite add_mapsto_iff in map_add;
      destruct map_add;
      [ left | right ]; intuition; eauto.
  Qed.

  Lemma in_elements_after_add':
    forall {A: Type} _key (added elem: A) tree,
      (~ In _key tree) ->
      (elem = added \/ List.In elem (GetValues tree))
      -> (List.In elem (GetValues (add _key added tree))).
  Proof.
    unfold GetValues;
    intros ? ? ? ? ? not_in is_in;
    rewrite <- MapsTo_snd;
    rewrite <- MapsTo_snd in is_in.

    setoid_rewrite add_mapsto_iff;
      destruct is_in as [eq | [_key' _key'_map]];
      [ exists _key
             | exists _key';
               right;
               split;
               [ intro Eeq;
                 apply MapsTo_In in _key'_map;
                 apply not_in;
                 rewrite (In_iff _ Eeq) | ]
      ]; intuition.
  Qed.

  Lemma in_elements_after_add_iff:
    forall {A: Type} key (added elem: A) tree,
      (~ In key tree) ->
      (List.In elem (GetValues (add key added tree))
       <-> (elem = added \/ List.In elem (GetValues tree))).
  Proof.
    intros;
    split;
    eauto using in_elements_after_add, in_elements_after_add'.
  Qed.


  Lemma In_MapsTo :
    forall A tree key,
      In key tree ->
      exists (value: A),
        (MapsTo key value tree /\ find key tree = Some value).
  Proof.
    intros A tree key H;
    apply in_find_iff in H;
    destruct (find key tree) as [value | ] eqn:eq_option;
    try rewrite <- find_mapsto_iff in eq_option;
    intuition eauto.
  Qed.

  Require Import Permutation AdditionalPermutationLemmas.

  Lemma InA_mapsto_add {Value} :
    forall bag' kv k' (v' : Value),
      InA (@eq_key_elt _) kv (elements (add k' v' bag')) ->
      eq_key_elt kv (k', v') \/
      (~ E.eq (fst kv) k' /\
       InA (@eq_key_elt _) kv (elements bag')).
  Proof.
    intros.
    destruct kv as [k v]; apply elements_2 in H.
    apply add_mapsto_iff in H; intuition; subst;
    [left; split; simpl; eauto |
     right; eauto using elements_1].
  Qed.

  Lemma InA_mapsto_add' {Value} :
    forall bag' kv k' (v' : Value),
      (eq_key_elt kv (k', v') \/
       (~ E.eq (fst kv) k' /\
        InA (@eq_key_elt _) kv (elements bag')))
      -> InA (@eq_key_elt _) kv (elements (add k' v' bag')).
  Proof.
    intros; destruct kv as [k v]; apply elements_1;
    apply add_mapsto_iff; intuition;
    [destruct H0; eauto
    | right; intuition; apply elements_2; eauto].
  Qed.

  Lemma Permutation_InA_cons {Value} :
    forall l (l' : list (key * Value)),
      NoDupA (@eq_key _) l
      -> NoDupA (@eq_key _) l'
      -> (forall k v,
            InA (@eq_key_elt _) (k, v) l' <->
            (InA (@eq_key_elt _) (k, v) l))
      -> Permutation (List.map snd l')
                     (List.map snd l).
  Proof.
    induction l; intros.
    destruct l'.
    constructor.
    assert (InA (eq_key_elt (elt:=Value)) (fst p, snd p) []) as H2
                                                               by (eapply H1; left; split; reflexivity); inversion H2.
    destruct a as [k v].
    assert (InA (eq_key_elt (elt:=Value)) (k, v) l') as H2
                                                       by (eapply H1; econstructor; split; reflexivity).
    destruct (InA_split H2) as [l'1 [kv [l'2 [eq_kv eq_l]]]]; subst.
    repeat rewrite List.map_app; simpl.
    etransitivity.
    symmetry.
    apply Permutation_middle.
    destruct eq_kv; simpl in *; subst; constructor.
    rewrite <- List.map_app.
    eapply NoDupA_swap in H0; eauto using eqk_equiv.
    inversion H0; inversion H; subst; apply IHl; eauto.
    assert (forall (k0 : key) (v : Value),
              InA (eq_key_elt (elt:=Value)) (k0, v) (kv :: (l'1 ++ l'2)) <->
              InA (eq_key_elt (elt:=Value)) (k0, v) ((k, snd kv) :: l)) by
        (split; intros;
         [ eapply H1; eapply InA_app_cons_swap
         | eapply H1 in H4; eapply InA_app_cons_swap in H4 ]; eauto using eqke_equiv).
    split; intros.
    + generalize (proj1 (H4 k0 v) (InA_cons_tl _ H5)); intros.
      inversion H8; subst; eauto.
      destruct H12; simpl in *.
      elimtype False; apply H6.
      revert H5 H9 H3; clear; induction (l'1 ++ l'2); intros;
      inversion H5; subst;
      [ constructor; destruct H0; simpl in *; unfold eq_key;
        rewrite <- H3, <- H9; eauto
      | constructor 2; eauto ].
    + generalize (proj2 (H1 k0 v) (InA_cons_tl _ H5)); intros.
      eapply InA_app_cons_swap in H8; eauto using eqke_equiv.
      inversion H8; subst; eauto.
      destruct H12; simpl in *.
      elimtype False; apply H10.
      revert H5 H9 H3; clear; induction l; intros;
      inversion H5; subst;
      [ constructor; destruct H0; simpl in *; unfold eq_key;
        simpl; rewrite <- H, H9; eauto
      | constructor 2; eauto ].
  Qed.


  Lemma FMap_Insert_fold_add {Value}
  : forall (f : Value -> Value) (bag : t Value) bag',
      (forall (k : key), InA E.eq k (List.map fst (elements bag))
                         -> ~ In k bag')
      -> Permutation
           (List.map snd (elements (fold (fun k bag'' r' => add k (f bag'') r')
                                         bag bag')))
           (List.map snd ((List.map (fun kv => (fst kv, f (snd kv))) (elements bag)) ++ elements bag')).
  Proof.
    intros.
    intros; rewrite fold_1.
    generalize (elements_3w bag) as NoDupl.
    revert bag' H; induction (elements bag); simpl; intros.
    reflexivity.
    rewrite IHl, Permutation_cons_app;
      try (rewrite List.map_app; reflexivity).
    rewrite List.map_app, List.map_map.
    apply Permutation_app; try reflexivity.
    apply (Permutation_InA_cons ((fst a, f (snd a)) :: elements bag'));
      eauto using elements_3w.
    econstructor; eauto using elements_3w.
    unfold not; intros; eapply (H (fst a));
    [ constructor; reflexivity
    | eapply elements_in_iff; revert H0; clear; intro; induction H0].
    repeat econstructor; eauto.
    destruct IHInA; econstructor; econstructor 2; eauto.
    split; intros.
    apply InA_mapsto_add in H0; intuition.
    inversion H0; subst; eapply InA_mapsto_add'; intuition.
    right; intuition.
    eapply H; simpl.
    econstructor; reflexivity.
    eapply elements_in_iff; revert H2 H1; clear; intros;
    induction H2.
    destruct H; repeat econstructor; eauto.
    destruct IHInA; econstructor; econstructor 2; eauto.
    unfold not; intros.
    apply add_in_iff in H1; destruct H1.
    inversion NoDupl; subst; rewrite <- H1 in H0; eapply H4.
    revert H0; clear; induction l; intros; inversion H0; subst.
    constructor; eauto.
    econstructor 2; eauto.
    eapply H; eauto.
    inversion NoDupl; eauto.
  Qed.

  Lemma FMap_fold_add_MapsTo_NIn {Value}
  : forall (f : Value -> Value) l k v bag',
      ~ InA (@eq_key _) (k,v) (List.map (fun kv => (fst kv, f (snd kv))) l)
      -> (MapsTo k v (fold_left (fun a p => add (fst p) (f (snd p)) a) l bag')
          <-> MapsTo k v bag').
  Proof.
    unfold eq_key; intros; revert k v bag' H.
    induction l; simpl; intros; split; eauto.
    intros; assert (MapsTo k v (add (fst a) (f (snd a)) bag')).
    apply IHl;
      [unfold not; intros; apply H; constructor 2; eauto
      | eauto].
    apply add_mapsto_iff in H1; intuition; subst.
    intros; eapply IHl; eauto using add_2.
  Qed.

  Lemma FMap_fold_add_MapsTo_In {Value}
  : forall (f : Value -> Value) (bag : t Value) bag' k v,
      InA (@eq_key_elt _) (k,v) (List.map (fun kv => (fst kv, f (snd kv))) (elements bag))
      -> MapsTo k v
                (fold (fun k bag'' r' => add k (f bag'') r') bag bag').
  Proof.
    intros; rewrite fold_1 in *; revert k v bag' H;
    generalize (elements_3w bag); induction (elements bag);
    intros; inversion H0; inversion H; subst; simpl in *; eauto.
    destruct H2; simpl in *; subst; rewrite H1.
    apply FMap_fold_add_MapsTo_NIn; eauto.
    unfold not, eq_key in *; intros; apply H6; revert H2; clear;
    induction l; simpl in *; intros; inversion H2; subst; eauto.
    apply add_1; reflexivity.
  Qed.

  Lemma FMap_Insert_fold_add_MapsTo {Value}
  : forall (f : Value -> Value) (bag : t Value) bag' k v,
      MapsTo k v
             (fold (fun k bag'' r' => add k (f bag'') r') bag bag') ->
      MapsTo k v bag' \/
      InA (@eq_key_elt _) (k,v) (List.map (fun kv => (fst kv, f (snd kv))) (elements bag)).
  Proof.
    intros; rewrite fold_1 in *; revert bag' H;
    induction (elements bag); simpl in *; eauto; intros.
    apply IHl in H; intuition.
    apply add_mapsto_iff in H0; intuition; subst.
    right; constructor; split; eauto.
  Qed.

  Lemma InA_Map {A B} eqB
  : forall (f : A -> B) (b : B) (l : list A),
      InA eqB b (List.map f l) <->
      exists a, eqB b (f a) /\ List.In a l.
  Proof.
    split; induction l; simpl; intros; inversion H; subst;
    eauto. destruct (IHl H1) as [a' [In_a eq_b]]; eauto.
    intuition.
    intuition; subst.
    constructor; eauto.
    constructor 2; eauto.
  Qed.

  Lemma FMap_Insert_fold_add_map_eq {Value}
  : forall (f : Value -> Value) (bag : t Value),
      Equal
        (fold (fun k bag'' r' => add k (f bag'') r') bag (empty _))
        (map f bag).
  Proof.
    unfold Equal.
    intros; case_eq (find y
                          (fold
                             (fun (k : key) (bag'' : Value) (r' : t Value) => add k (f bag'') r')
                             bag (empty Value)));
    intros; case_eq (find y (map f bag)); intros; eauto.
    - apply find_2 in H; apply find_2 in H0.
      apply FMap_Insert_fold_add_MapsTo in H; destruct H.
      elimtype False; apply empty_mapsto_iff in H; eauto.
      apply map_mapsto_iff in H0; destruct H0 as [a [eq_a MapsTo_y]]; subst.
      generalize (elements_3w bag); apply elements_1 in MapsTo_y;
      induction MapsTo_y; intros.
      + inversion H1; subst; destruct H0; simpl in *; subst.
        inversion H; subst;
        [destruct H3; simpl in *; subst; eauto
        | elimtype False; apply H4; revert H0 H3; clear; induction l;
          intros; inversion H3; subst; unfold eq_key in *].
        destruct H1; simpl in *; subst; constructor; eauto.
        constructor 2; eauto.
      + inversion H0; subst; eapply IHMapsTo_y; eauto.
        inversion H; subst; eauto.
        destruct H2; simpl in *; subst.
        elimtype False; apply H3; revert H1 MapsTo_y; clear; induction l;
        intros; inversion MapsTo_y; subst; unfold eq_key in *.
        destruct H0; simpl in *; subst; constructor; eauto.
        constructor 2; eauto.
    - apply find_2 in H; apply FMap_Insert_fold_add_MapsTo in H; destruct H.
      elimtype False; apply empty_mapsto_iff in H; eauto.
      apply InA_Map in H; destruct H as [[k v'] [eq_k In_k]]; simpl in *.
      destruct eq_k; simpl in *; rewrite H in H0.
      apply not_find_in_iff in H0; elimtype False; eapply H0.
      apply map_in_iff; exists v'; apply elements_2.
      apply InA_alt; eexists; repeat split; eauto.
    - apply find_2 in H0; apply not_find_in_iff in H.
      apply map_mapsto_iff in H0; destruct H0 as [k [k_eq MapsTo_k]]; subst.
      elimtype False; apply H.
      econstructor 1 with (x := f k); apply FMap_fold_add_MapsTo_In.
      apply elements_1 in MapsTo_k; revert MapsTo_k; clear;
      intro; induction MapsTo_k; simpl.
      repeat constructor; destruct H; simpl in *; subst; eauto.
      constructor 2; eauto.
  Qed.

  (* Partitioning a finite map [m] with a function that respects key and value equality
       will produce a pair of maps equivalent to [m]. *)
  Lemma MapsTo_partition_fst:
    forall TValue f k v (m: t TValue),
      Proper (E.eq ==> eq ==> eq) f ->
      MapsTo k v (fst (partition f m)) ->
      MapsTo k v m.
  Proof.
    intros * ? maps_to.
    rewrite partition_iff_1 with (f := f) (m := m) in maps_to;
      intuition.
  Qed.

  Lemma MapsTo_partition_snd:
    forall TValue f k v (m: t TValue),
      Proper (E.eq ==> eq ==> eq) f ->
      MapsTo k v (snd (partition f m)) ->
      MapsTo k v m.
  Proof.
    intros * ? maps_to.
    rewrite partition_iff_2 with (f := f) (m := m) in maps_to;
      intuition.
  Qed.

  (* A restatement of the specification of the [Partition] relation. *)
  Lemma partition_Partition_simple :
    forall TValue f,
      Proper (E.eq ==> eq ==> eq) f ->
      forall (m: t TValue),
        Partition m
                  (fst (partition f m))
                  (snd (partition f m)).
  Proof.
    intros.
    eapply partition_Partition; eauto.
  Qed.

  (* folding a function [f] which respects key, value, and accumulator
       equivalences over two equivalent maps [m1] [m2] will produce
       equivalent values. *)
  Lemma fold_Equal_simpl :
    forall {TValue TAcc} {eqA: TAcc -> TAcc -> Prop} {m1 m2: t TValue} {f} {init: TAcc},
      Equal m1 m2 ->
      Equivalence eqA ->
      Proper (E.eq ==> eq ==> eqA ==> eqA) f ->
      transpose_neqkey eqA f ->
      eqA (fold f m1 init) (fold f m2 init).
  Proof.
    intros.
    apply fold_Equal; assumption.
  Qed.

  Lemma fold_empty :
    forall {TValue TAcc} f (default: TAcc),
      fold f (empty TValue) default = default.
  Proof.
    intros;
    apply fold_Empty;
    eauto using empty_1.
  Qed.

  (* Adding the same key [k] to equivalent maps will produce equivalent maps*)
  Lemma add_Equal_simple :
    forall {TValue} {m1 m2: t TValue},
      Equal m1 m2 ->
      forall k v,
        Equal (add k v m1) (add k v m2).
  Proof.
    intros.
    apply add_m; eauto.
  Qed.

  (* Adding a key [k] overwrites previous values of [k] in a map. *)
  Lemma multiple_adds :
    forall {TValue} k v1 v2 (m: t TValue),
      Equal (add k v2 (add k v1 m))
            (add k v2 m).
  Proof.
    intros.
    unfold Equal.
    intros k'.
    destruct (E.eq_dec k k').

    rewrite !add_eq_o; eauto.
    rewrite !add_neq_o; eauto.
  Qed.

  Lemma Values_fold_Proper :
    forall {A},
      Proper (E.eq ==> eq ==> Permutation (A:=A) ==> Permutation (A:=A))
             (fun (_ : key) (val : A) (acc : list A) => val :: acc).
  Proof.
    unfold Proper, respectful; intros.
    subst; eauto.
  Qed.

  Lemma Values_fold_transpose_neqkey :
    forall {A},
      transpose_neqkey (Permutation (A:=A))
                       (fun (_ : key) (val : A) (acc : list A) => val :: acc).
  Proof.
    unfold transpose_neqkey; intros; constructor.
  Qed.

  Lemma empty_In :
    forall {TValue} k,
      ~ In k (empty TValue).
  Proof.
    intros; rewrite empty_in_iff; tauto.
  Qed.

  Lemma fold_right_map :
    forall {A B} f seq,
      @List.fold_right (list B) A (fun b a => f b :: a) [] seq = List.map f seq.
  Proof.
    intros; induction seq; simpl; try rewrite IHseq; reflexivity.
  Qed.

  Lemma fold_left_map :
    forall {A B} f seq,
      @List.fold_left (list B) A (fun a b => f b :: a) seq [] = List.map f (rev seq).
  Proof.
    intros; rewrite <- fold_left_rev_right; apply fold_right_map.
  Qed.

  Lemma Values_fold_perm :
    forall {TValues} (m: t TValues),
      Permutation
        (Values m)
        (fold (fun key val acc => cons val acc) m []).
  Proof.
    intros.
    rewrite fold_1.

    rewrite fold_left_map.
    unfold Values.

    rewrite map_rev.
    apply Permutation_rev.
  Qed.

  Lemma Values_fold_eq :
    forall {TValues} (m: t TValues),
      (Values m) =
      (rev (fold (fun key val acc => cons val acc) m [])).
  Proof.
    intros.
    rewrite fold_1.

    rewrite fold_left_map.
    unfold Values.

    rewrite map_rev.
    rewrite rev_involutive; reflexivity.
  Qed.


  Lemma map_fold :
    forall {A B TValue} f g m init,
      (@List.map A B g
                 (fold
                    (fun k (v: TValue) acc =>
                       f k v :: acc) m init)) =
      (fold (fun k v acc => g (f k v) :: acc) m (List.map g init)).
  Proof.
    intros until m; setoid_rewrite fold_1.
    setoid_rewrite <- fold_left_rev_right; simpl.
    induction (elements m) as [ | ? ? IH ]; simpl; trivial.
    setoid_rewrite fold_right_app.
    setoid_rewrite IH; simpl.
    reflexivity.
  Qed.

  Lemma elements_fold_eq :
    forall {TValues} (m: t TValues),
      (elements m) =
      (rev (fold (fun key val acc => cons (key, val) acc) m [])).
  Proof.
    intros.
    rewrite fold_1.

    assert ((fold_left
               (fun (a : list (key * TValues)) (p : key * TValues) =>
                  (fst p, snd p) :: a) (elements m) [])
            = (fold_left
                 (fun (a : list (key * TValues)) (p : key * TValues) =>
                    p :: a) (elements m) []))
      by (f_equal; repeat (apply functional_extensionality; intros);
          rewrite <- surjective_pairing; reflexivity).

    rewrite H.

    setoid_rewrite fold_left_id.
    rewrite rev_involutive; reflexivity.
  Qed.

  Lemma elements_fold_perm :
    forall {TValues} (m: t TValues),
      Permutation
        (elements m)
        (fold (fun key val acc => cons (key, val) acc) m []).
  Proof.
    intros.
    rewrite fold_1.

    assert ((fold_left
               (fun (a : list (key * TValues)) (p : key * TValues) =>
                  (fst p, snd p) :: a) (elements m) [])
            = (fold_left
                 (fun (a : list (key * TValues)) (p : key * TValues) =>
                    p :: a) (elements m) []))
      by (f_equal; repeat (apply functional_extensionality; intros);
          rewrite <- surjective_pairing; reflexivity).

    rewrite H.

    setoid_rewrite fold_left_id.
    apply Permutation_rev.
  Qed.

  Lemma values_add_not_in {A : Type} :
    forall (m: t A),
    forall k v,
      ~ In k m ->
      Permutation
        (Values (add k v m))
        (v :: Values m).
  Proof.
    intros.
    unfold Values.
    rewrite elements_fold_eq.

    rewrite map_rev.
    rewrite map_fold; simpl.
    etransitivity.
    symmetry.
    etransitivity; [ | apply Permutation_rev].
    symmetry.
    apply (fold_add (elt := A) (eqA := @Permutation A )); eauto.

    apply Permutation_Equivalence.

    unfold Proper, respectful; intros; simpl;
    subst; apply Permutation_cons; assumption.

    unfold transpose_neqkey; intros; simpl;
    constructor.

    rewrite fold_1.
    rewrite fold_left_map.
    econstructor.
    rewrite Permutation_rev.

    rewrite map_rev.
    rewrite rev_involutive.
    reflexivity.
  Qed.



  (* This should be simplified by the switch to Permutations.

  Lemma EnsembleListEquivalence_fmap_add_filtered :
    forall {A: Type} (cond : A -> Prop) ensemble key tree added,
      cond added ->
      (~ In (elt:=A) key tree) ->
      EnsembleListEquivalence
        (fun x => Ensembles.In _ ensemble x /\ cond x)
        (GetValues tree) ->
      EnsembleListEquivalence
        (fun x => (x = added \/ Ensembles.In _ ensemble x) /\ cond x)
        (GetValues (add key added tree)).
  Proof.
    unfold EnsembleListEquivalence;
    repeat split; intros;
    unfold Ensembles.In in *; simpl in *; intuition.



    apply in_elements_after_add'; trivial.
    rewrite <- H1.
    intuition.

    apply in_elements_after_add in H2.
    destruct H2; intuition.
    subst; intuition.
    rewrite <- H1 in H2; intuition.
    rewrite <- H1 in H2; intuition.
  Qed. *)

  Lemma fold_pair {A B A' B' V} :
    forall (m : t V) (ab : A * B) (f : TKey -> V -> (A' * B')) fa fb,
      @fold V (A * B) (fun k (v : V) (ab : A * B) =>
                         let (a, b) := f k v in
                         let (a', b') := ab in
                         (fa k a a', fb k b b'))
            m ab
      = (fold (fun k m (a' : A) =>
                 fa k (fst (f k m)) a') m (fst ab),
         fold (fun k m (b' : B) =>
                 fb k (snd (f k m)) b')
              m (snd ab)).
  Proof.
    intros; repeat rewrite fold_1; revert ab; induction (elements m);
    destruct ab; simpl; eauto.
    destruct a; simpl; destruct (f k v);
    rewrite IHl; reflexivity.
  Qed.

  Lemma fold_over_Values :
    forall {TValue TAcc} (m: t TValue) f g (init: TAcc),
      (forall k v acc, f k v acc = g acc v) ->
      fold f m init = fold_left g (Values m) init.
  Proof.
    intros * equiv.
    rewrite fold_1.
    unfold Values.
    rewrite <- fold_map.
    revert init; induction (elements m); simpl; eauto.
    intros; rewrite IHl, equiv; reflexivity.
  Qed.

  Lemma Permutation_map_Values {A B} :
    forall (f : A -> B) m,
      Permutation
        (List.map f (Values m))
        (Values (map f m)).
  Proof.
    unfold Values; intros.
    rewrite map_snd.
    apply Permutation_InA_cons; eauto using elements_3w.
    - pose proof (elements_3w m) as NoDupM.
      induction NoDupM; simpl in *; simpl; constructor; eauto.
      unfold not; intros; apply H; clear NoDupM IHNoDupM H;
      induction l; simpl in *; inversion H0; subst; eauto.
    - split; intros.
      apply elements_1.
      rewrite InA_Map in H; destruct H as [[k' v'] [eq_k In_k]];
      destruct eq_k; simpl in *; subst.
      rewrite H; eauto using elements_2, map_1, In_InA, equiv_eq_key_elt.
      rewrite InA_Map.
      apply elements_2 in H.
      apply map_mapsto_iff in H; destruct H as [a [a_eq MapsTo_k]]; subst.
      apply elements_1 in MapsTo_k.
      rewrite InA_alt in MapsTo_k.
      destruct MapsTo_k as [[k' a'] [eq_k In_k]].
      eexists; split; eauto.
      destruct eq_k; simpl in *; subst; constructor; eauto.
  Qed.

  Lemma Permutation_filter_Values {B} :
    forall (f : key -> B -> bool) m
           (Proper_f : Proper (E.eq ==> eq ==> eq) f),
      Permutation
        (Values (filter f m))
        (List.map snd (List.filter (fun kv => f (fst kv) (snd kv)) (elements m))).
  Proof.
    unfold Values; intros.
    apply Permutation_InA_cons; eauto using elements_3w.
    - pose proof (elements_3w m) as NoDupM.
      induction NoDupM; simpl in *; simpl; try constructor.
      case_eq (f (fst x) (snd x)); simpl; eauto.
      intros; constructor; eauto.
      unfold not; intros; apply H; clear NoDupM IHNoDupM H;
      induction l; simpl in *.
      inversion H0; subst; eauto.
      case_eq (f (fst a) (snd a)); intros; rewrite H in *; eauto.
      inversion H1; subst.
      constructor; eauto.
      constructor 2; eauto.
    - intros; rewrite <- elements_mapsto_iff, filter_iff; eauto;
      intuition.
      + rewrite elements_mapsto_iff in H0; induction H0.
        * simpl; destruct H; rewrite Proper_f in H1; eauto;
          rewrite H1; repeat constructor; eauto.
        * simpl; destruct (f (fst y) (snd y)); simpl; eauto.
      + rewrite elements_mapsto_iff; induction (elements m);
        simpl in *.
        * inversion H.
        * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H.
          inversion H; subst.
          constructor; eauto.
          constructor 2; eauto.
          constructor 2; eauto.
      + induction (elements m); simpl in *.
        * inversion H.
        * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H; eauto.
          inversion H; subst.
          destruct H2; rewrite Proper_f in H0; eauto.
          eauto.
  Qed.

  Lemma Permutation_Partition_App {Value}:
    forall (m m1 m2 : t Value),
      Partition m m1 m2 ->
      Permutation (Values m) (Values m1 ++ Values m2).
  Proof.
    unfold Partition; intros; intuition.
    unfold Values; rewrite <- List.map_app.
    eapply Permutation_InA_cons; eauto using elements_3w.
    eapply NoDupA_app; eauto using elements_3w, equiv_eq_key.
    intros; destruct x as [k v]; eapply (H0 k).
    apply InA_alt in H; destruct H; apply InA_alt in H2; destruct H2;
    intuition; unfold eq_key in *; simpl in *.
    destruct x; simpl in *; rewrite H3; econstructor;
    apply elements_2; eauto; apply In_InA; eauto using equiv_eq_key_elt.
    destruct x0; simpl in *; rewrite H; econstructor;
    apply elements_2; eauto; apply In_InA; eauto using equiv_eq_key_elt.
    intros; rewrite InA_app_iff by eauto using equiv_eq_key_elt;
    intuition.
    apply elements_2 in H; rewrite H1 in H; intuition;
    eauto using elements_1.
    apply elements_1; rewrite H1; eauto using elements_2.
    apply elements_1; rewrite H1; eauto using elements_2.
  Qed.

  Corollary Permutation_partition {Value}:
    forall f (m : t Value),
      (Proper (E.eq ==> eq ==> eq) f)
      -> Permutation (Values m)
                     (Values (fst (partition f m)) ++ Values (snd (partition f m))).
  Proof.
    intros; eauto using Permutation_Partition_App,
            partition_Partition_simple.
  Qed.

  Lemma map_add {A B}:
    forall (f : A -> B) m k v,
      Equal (map f (add k v m))
            (add k (f v) (map f m)).
  Proof.
    unfold Equal; intros; case_eq (find y (add k (f v) (map f m)));
    case_eq (find y (map f (add k v m))); intros; eauto.
    - rewrite <- find_mapsto_iff in H, H0.
      rewrite map_mapsto_iff in H; destruct H as [a [b_eq In_b]]; subst.
      rewrite add_mapsto_iff in H0, In_b; intuition; subst; eauto.
      rewrite map_mapsto_iff in H3; destruct H3 as [a' [b_eq' In_b']]; subst.
      rewrite find_mapsto_iff in In_b', H2; congruence.
    - rewrite <- find_mapsto_iff in H0.
      rewrite <- not_find_in_iff in H; exfalso; apply H.
      rewrite add_mapsto_iff in H0; intuition; subst; eauto.
      rewrite H0, map_in_iff, add_in_iff; eauto.
      rewrite map_mapsto_iff in H2; destruct H2 as [a [b_eq In_b]]; subst.
      rewrite map_in_iff, add_in_iff; right; econstructor; eauto.
    - rewrite <- find_mapsto_iff in H.
      rewrite <- not_find_in_iff in H0; exfalso; apply H0.
      rewrite map_mapsto_iff in H; destruct H as [a [b_eq In_b]]; subst.
      rewrite add_mapsto_iff in In_b; intuition; subst; eauto.
      rewrite H1, add_in_iff; eauto.
      rewrite add_in_iff, map_in_iff; right; econstructor; eauto.
  Qed.

  Lemma Equal_elements {A} :
    forall m1 m2,
      Equal m1 m2
      -> forall k (a : A), (InA (@eq_key_elt _) (k, a) (elements m1)
                            <-> InA (@eq_key_elt _) (k, a) (elements m2)).
  Proof.
    unfold Equal; split; intros;
    rewrite <- elements_mapsto_iff, find_mapsto_iff in H0;
    rewrite <- elements_mapsto_iff, find_mapsto_iff; congruence.
  Qed.

  Add Parametric Morphism {A} :
    (@Values A)
      with signature (Equal ==> @Permutation A)
        as Permutation_Equal_Values.
  Proof.
    intros; unfold Values.
    eapply Permutation_InA_cons; eauto using elements_3w, Equal_elements.
  Qed.

  Lemma elements_in_iff' :
    forall (elt : Type) (m : t elt) x,
      In x m <->
      exists v, InA (eq_key (elt:=elt)) (x, v) (elements m) .
  Proof.
    split; rewrite elements_in_iff; intros.
    destruct H; induction H.
    destruct H; eexists x0; econstructor; eauto.
    destruct IHInA; econstructor; econstructor 2; eassumption.
    destruct H; induction H.
    eexists; repeat econstructor; simpl; eauto.
    destruct IHInA; eexists; econstructor 2; eauto.
  Qed.

  Corollary elements_in_if' :
    forall (elt : Type) (m : t elt) x v,
      InA (eq_key (elt:=elt)) (x, v) (elements m) ->
      In x m.
  Proof.
    intros; eapply elements_in_iff'; eauto.
  Qed.


End FMapExtensions_fun.

Module FMapExtensions (M: WS) := FMapExtensions_fun M.E M.
