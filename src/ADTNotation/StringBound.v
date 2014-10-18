Require Import List String Arith ilist.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section IndexBound.

  Context {A : Set}.

  Class IndexBound (a : A) (Bound : list A) :=
    { ibound :> nat;
      boundi : nth_error Bound ibound = Some a}.

  Fail Global Instance IndexBound_head (a : A) (Bound : list A)
  : IndexBound a (a :: Bound) :=
    {| ibound := 0;
       boundi := eq_refl|}.

  Global Instance IndexBound_tail
           (a a' : A) (Bound : list A)
           {sB' : IndexBound a Bound}
  : IndexBound a (a' :: Bound) :=
    {| ibound := S ibound;
       boundi := boundi |}.

  Definition tail_IndexBound
           (a : A) (Bound : list A)
           (n : nat)
           (nth_n : nth_error Bound n = Some a)
  : IndexBound a Bound :=
    {| ibound := n;
       boundi := nth_n |}.

  Global Arguments ibound [a Bound] _ .
  Global Arguments boundi [a Bound] _.

  Record BoundedIndex (Bound : list A) :=
    { bindex :> A;
      indexb :> IndexBound bindex Bound }.

  Global Arguments bindex [Bound] _ .
  Global Arguments indexb [Bound] _ .

  Lemma lt_nth :
    forall n As (a : A),
      nth_error As n = Some a
      -> n < List.length As.
  Proof.
    induction n; destruct As; simpl; intros;
    try auto with arith; try discriminate.
    apply lt_n_S; eauto with arith.
  Qed.

  Definition BoundedIndex_nil
             (AnyT : Type)
             (idx : BoundedIndex nil)
  : AnyT.
  Proof.
    destruct idx as [idx [n nth_n]].
    elimtype False; eapply lt_n_0.
    apply (lt_nth _ _ nth_n).
  Qed.

  Lemma indexb_ibound_eq :
    forall Bound (bidx bidx' : BoundedIndex Bound),
      ibound (indexb bidx) = ibound (indexb bidx') ->
      bindex bidx = bindex bidx'.
  Proof.
    intros; induction Bound; simpl in *.
    - apply BoundedIndex_nil; auto.
    - destruct bidx as [bindex [n nth_n]];
      destruct bidx' as [bindex' [n' nth_n']]; simpl in *; subst.
      congruence.
  Qed.

  Section Bounded_Index_Dec_Eq.
  (* If equality on A is decideable, so is equality
     on bounded indices in A. *)
    Variable A_eq_dec :
      forall a a' : A, {a = a'} + {a <> a'}.

    Require Import Eqdep_dec.

    Program Definition Opt_A_eq_dec (a a' : option A):
      {a = a'} + {a <> a'} :=
      match a as a, a' as a' return {a = a'} + {a <> a'} with
          | Some a, Some a' => if A_eq_dec a a' then left _ else right _
          | None, None => left _
          | _, _ => right _
      end.

    Definition K_Opt_A :
      forall (a : option A) (P: a = a -> Prop),
          P (refl_equal a) -> forall p : a = a, P p :=
      K_dec_set Opt_A_eq_dec.

    Definition UIP_Opt_A  :
      forall (a : option A) (Q : option A -> Type)
             (x : Q a) (h : a = a),
        x = eq_rect a Q x a h.
      intros; eapply K_Opt_A with (p := h); reflexivity.
    Defined.

    Lemma eq_proofs_unicity_Opt_A
      : forall (a a' : option A) (p1 p2 : a = a'), p1 = p2.
      apply eq_proofs_unicity; intros.
      destruct (Opt_A_eq_dec x y); auto.
    Qed.

    Corollary idx_ibound_eq
    : forall Bound (idx idx' : BoundedIndex Bound),
        ibound (indexb idx) = ibound (indexb idx') ->
        idx = idx'.
    Proof.
      intros; generalize (indexb_ibound_eq idx idx' H);
      destruct idx as [idx [n' In_n' ]];
        destruct idx' as [idx' [n'' In_n'' ]]; intros;
        simpl in *; subst; f_equal.
      rewrite (eq_proofs_unicity_Opt_A In_n' In_n''); auto.
    Qed.

    Corollary idx_ibound_neq
    : forall Bound (idx idx' : BoundedIndex Bound),
        ibound (indexb idx) <> ibound (indexb idx') ->
        idx <> idx'.
    Proof.
      intros; destruct idx as [idx [n' In_n' ]];
        destruct idx' as [idx' [n'' In_n'' ]]; intros;
        simpl in *; subst.
      unfold not; intros; apply H; injection H0; auto.
    Qed.

    Corollary BoundedIndex_eq_dec Bound :
      forall idx idx' : (BoundedIndex Bound),
        {idx = idx'} + {idx <> idx'}.
    Proof.
      intros; destruct (eq_nat_dec (ibound idx) (ibound idx')).
      - left; auto using idx_ibound_eq.
      - right; auto using idx_ibound_neq.
    Defined.

    End Bounded_Index_Dec_Eq.

End IndexBound.

Definition BoundedString := @BoundedIndex string.
Definition BoundedString_eq_dec
           {Bound}
           (bidx bidx' : BoundedString Bound)
: {bidx = bidx'} + {bidx <> bidx'} :=
  BoundedIndex_eq_dec string_dec  bidx bidx'.

Notation "`` A" :=
  ({| bindex := A%string |}) (at level 0, format "`` A").

Section ithIndexBound.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {C : Set}.
  Variable (projAC : A -> C).

  Lemma None_neq_Some
  : forall (AnyT AnyT' : Type) (a : AnyT),
      None = Some a -> AnyT'.
  Proof.
    intros; discriminate.
  Qed.

  (* Given a [BoundedIndex] for a list, we can always return an element. *)
  Definition nth_Bounded'
             (Bound : list A)
             (c : C)
             (a_opt : option A)
             (nth_n : option_map projAC a_opt = Some c)
  : A := match a_opt as x
               return (option_map projAC x = Some c) -> A with
             | Some a => fun _ => a
             | None => fun f => None_neq_Some _ f
         end nth_n.

  Lemma nth_error_map :
    forall n As c_opt,
      nth_error (map projAC As) n = c_opt
      -> option_map projAC (nth_error As n) = c_opt.
  Proof.
    induction n; destruct As; simpl; eauto.
  Defined.

  Definition nth_Bounded
             (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
  : A := nth_Bounded' Bound (nth_error Bound (ibound idx))
                      (nth_error_map _ _ (boundi idx)).

  (* We can lift [B (nth_Bounded idx)] to a dependent option. *)
  Definition Some_Dep_Option
             {B : A -> Type}
             (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) ->
    Dep_Option B (nth_error Bound (ibound idx)) :=
    match (nth_error Bound (ibound idx)) as e return
           forall c,
             B (@nth_Bounded' _ _ e c) ->
              Dep_Option B e with
       | Some a => fun c => Dep_Some _ _
       | None => fun c => None_neq_Some _ c
     end (nth_error_map _ _ (boundi idx)).

  (* [nth_Bounded_rect] builds a function whose type depends
     on [nth_Bounded] by reducing to a case with [nth_error],
     which is easier to work/reason with. *)

  Definition nth_Bounded_rect
        (P : forall As, BoundedIndex (map projAC As) -> A -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound)),
      Dep_Option (P Bound idx) (nth_error Bound (ibound idx))
      -> P Bound idx (nth_Bounded Bound idx) :=
    fun Bound idx =>
      match (nth_error Bound (ibound idx)) as e
            return
            (forall (f : option_map _ e = Some (bindex idx)),
               (Dep_Option (P Bound idx) e) ->
               P _ _
                 (match e as e' return
                        option_map _ e' = Some (bindex idx)
                        -> A
                  with
                    | Some a => fun _ => a
                    | None => fun f => _
                  end f)) with
        | Some a => fun _ H => Dep_Option_elim H
        | None => fun f => None_neq_Some _ f
      end (nth_error_map _ _ (boundi idx)).

  (* [nth_Bounded_ind2] builds a function whose type depends
     on *two* occurences of [nth_Bounded] by reducing to a case
     with [nth_error], which is easier to reason with. *)

  Program Definition nth_Bounded_ind2
             (P : forall As, BoundedIndex (map projAC As)
                             -> BoundedIndex (map projAC As)
                             -> A -> A -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (idx' : BoundedIndex (map projAC Bound)),
      match nth_error Bound (ibound idx), nth_error Bound (ibound idx') with
          | Some a, Some a' => P Bound idx idx' a a'
          | _, _ => True
      end
      -> P Bound idx idx' (nth_Bounded _ idx) (nth_Bounded _ idx'):=
    fun Bound idx idx' =>
      match (nth_error Bound (ibound idx)) as e, (nth_error Bound (ibound idx')) as e'
            return
            (forall (f : option_map _ e = Some (bindex idx))
                    (f' : option_map _ e' = Some (bindex idx')),
               (match e, e' with
                  | Some a, Some a' => P Bound idx idx' a a'
                  | _, _ => True
                end)
               -> P Bound idx idx'
                 (match e as e'' return
                        option_map _ e'' = Some (bindex idx)
                        -> A
                  with
                    | Some a => fun _ => a
                    | _ => fun f => _
                  end f)
                 (match e' as e'' return
                        option_map _ e'' = Some (bindex idx')
                        -> A
                  with
                    | Some a => fun _ => a
                    | _ => fun f => _
                  end f')) with
        | Some a, Some a' => fun _ _ H => _
        | _, _ => fun f => _
      end (nth_error_map _ _ (boundi idx))
          (nth_error_map _ _ (boundi idx')).

  (* [nth_Bounded] returns the same elements as [nth_default] *)

  Lemma nth_Bounded_eq_nth_default
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (default_A : A),
      nth_Bounded Bound idx = nth (ibound idx) Bound default_A.
  Proof.
    intros Bound idx; eapply nth_Bounded_rect.
    case_eq (nth_error Bound (ibound idx)); econstructor; auto.
    intros; rewrite <- nth_default_eq; unfold nth_default;
    rewrite H; reflexivity.
  Qed.

  (* The result of [nth_Bounded] doesn't depend on the proof
     that [ibound] is a valid index. *)
  Lemma nth_Bounded_eq
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound)),
      ibound idx = ibound idx'
      -> nth_Bounded Bound idx = nth_Bounded Bound idx'.
  Proof.
    intros.
    eapply nth_Bounded_ind2 with (idx := idx) (idx' := idx').
    simpl.
    case_eq (nth_error Bound (ibound idx'));
      case_eq (nth_error Bound (ibound idx)); auto.
    congruence.
  Defined.

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)
  Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) :=
    match (nth_error Bound (ibound idx)) as a'
                  return
                  Dep_Option B a' ->
                  forall (f : option_map _ a' = Some (bindex idx)),
                    B (nth_Bounded' Bound _ f) with
        | Some a => fun b _ => Dep_Option_elim b
        | None => fun _ f => None_neq_Some _ f
    end (ith_error il (ibound idx)) (nth_error_map _ _ (boundi idx)).

  (* To build a reasoning principle for ith_Bounded, we need to
     show that option types are shuffled around by [Dep_Option_elim] *)
    Definition ith_error_eq_P
               {B : A -> Type}
               (Bound : list A)
               (idx : BoundedIndex (map projAC Bound))
               e' b c d :=
      match e' as e'
        return
        (Dep_Option B e' ->
         forall c : option_map _ e' = Some (bindex idx),
           B (nth_Bounded' Bound _ c) -> Type)
      with
        | Some e =>
          fun b c d => Dep_Option_elim b = d
        | None => fun b c d => True
      end b c d.

    Lemma ith_error_eq
          {B : A -> Type}
    : forall (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
              (il : ilist B Bound),
        ith_error_eq_P Bound idx
        (ith_error il (ibound idx))
        (nth_error_map _ _ (boundi idx))
        (ith_Bounded il idx).
    Proof.
      unfold ith_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n; induction Bound; destruct n;
      simpl; eauto; intros.
      eapply IHBound.
    Qed.

  Definition Dep_Option_elim_P
             {B : A -> Type}
             (P : forall a, B a -> Type)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
      := match a_opt as a' return
               Dep_Option_elimT B a' -> Type with
           | Some a => P a
           | None => fun _ => True
         end (Dep_Option_elim b_opt).

    (* [ith_Bounded_rect] builds a function whose type depends
     on [ith_Bounded] by reducing to a case with [ith_error],
     which is easier to work/reason with. *)

    Program Definition ith_Bounded_rect
            {B : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As -> forall a : A, B a -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      Dep_Option_elim_P (P Bound idx il) (ith_error il (ibound idx))
      -> P Bound idx il _ (ith_Bounded il idx) :=
    fun Bound idx il =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (c : option_map _ e = Some (bindex idx))
                        d,
                   (ith_error_eq_P Bound idx b c d)
                   -> Dep_Option_elim_P (P Bound idx il) b ->
                   P _ _ _ (@nth_Bounded' _ _ e c) d with
          | Some a => _
          | None => _
           end (ith_error il (ibound idx))
               _
               (ith_Bounded il idx)
               (ith_error_eq idx il).

    (* [ith_Bounded_ind] builds a proof whose type depends
     on both [nth_Bounded] and an occurence of [ith_Bounded] by reducing
     it to a case with an [ith_error], which is easier to reason with. *)

    Program Definition ith_Bounded_ind
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (b : B' (nth_Bounded Bound idx)),
      Dep_Option_elim_P2 (P Bound idx il) (ith_error il (ibound idx))
                      (Some_Dep_Option Bound idx b)
      -> P Bound idx il _ (ith_Bounded il idx) b :=
      fun Bound idx il b =>
        match (nth_error Bound (ibound idx)) as e
              return
              forall (b : Dep_Option B e)
                     (b' : Dep_Option B' e)
                     (c : option_map _ e = Some (bindex idx))
                     d d',
                (ith_error_eq_P Bound idx b c d)
                -> (ith_error_eq_P Bound idx b' c d')
                -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                P _ _ _ (@nth_Bounded' _ _ _ c) d d' with
          | Some a => _
          | None => _
        end (ith_error il (ibound idx))
            (Some_Dep_Option Bound idx b)
            _
            (ith_Bounded il idx)
            b
            (ith_error_eq idx il)
            _.
    Next Obligation.
      unfold ith_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      unfold Some_Dep_Option; simpl.
      intros; eapply IHBound.
    Qed.

    (* [ith_Bounded_ind2] builds a proof whose type depends
     on *two* occurences of [ith_Bounded] by reducing  it to a case
     with two [ith_error]s, which is easier to reason with. *)

    Program Definition ith_Bounded_ind2
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound),
      Dep_Option_elim_P2 (P Bound idx il)
                      (ith_error il (ibound idx))
                      (ith_error il' (ibound idx) )
      -> P Bound idx il _ (ith_Bounded il idx) (ith_Bounded il' idx) :=
    fun Bound idx il il' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith_error_eq_P Bound idx b c d)
                   -> (ith_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                   P _ _ _ (@nth_Bounded' _ _ _ c) d d' with
          | Some a => _
          | None => _
           end (ith_error il (ibound idx))
               (ith_error il' (ibound idx) )
               _
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_error_eq idx il)
               (ith_error_eq idx il').

    Definition Dep_Option_elim_P3
             {B B' B'' : A -> Type}
             (P : forall a,
                    B a
                    -> B' a
                    -> B'' a
                    -> Prop)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt)
             (b''_opt : Dep_Option B'' a_opt)
      := match a_opt as a return
               Dep_Option_elimT B a
               -> Dep_Option_elimT B' a
               -> Dep_Option_elimT B'' a
               -> Prop with
           | Some a => P a
           | _ => fun _ _ _ => True
         end (Dep_Option_elim b_opt)
             (Dep_Option_elim b'_opt)
             (Dep_Option_elim b''_opt).

    Program Definition ith_Bounded_ind3
            {B B' B'' : A -> Type}
            (P : forall As,
                   BoundedIndex (map projAC As)
                   -> ilist B As
                   -> ilist B' As
                   -> ilist B'' As
                   -> forall a : A,
                        B a -> B' a -> B'' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound)
           (il'' : ilist B'' Bound),
      Dep_Option_elim_P3 (P Bound idx il il' il'')
                      (ith_error il (ibound idx))
                      (ith_error il' (ibound idx))
                      (ith_error il'' (ibound idx))
      -> P Bound idx il il' il'' _
           (ith_Bounded il idx)
           (ith_Bounded il' idx)
           (ith_Bounded il'' idx) :=
    fun Bound idx il il' il'' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (b'' : Dep_Option B'' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d' d'',
                   (ith_error_eq_P Bound idx b c d)
                   -> (ith_error_eq_P Bound idx b' c d')
                   -> (ith_error_eq_P Bound idx b'' c d'')
                   -> Dep_Option_elim_P3 (P Bound idx il il' il'') b b' b'' ->
                   P Bound idx il il' il''
                     (@nth_Bounded' _ _ _ c)
                     d d' d'' with
          | Some a => _
          | _  => _
           end (ith_error il (ibound idx))
               (ith_error il' (ibound idx) )
               (ith_error il'' (ibound idx) )
               _
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_Bounded il'' idx)
               (ith_error_eq idx il)
               (ith_error_eq idx il')
               (ith_error_eq idx il'').

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    intros.
    eapply ith_Bounded_ind2 with (idx0 := idx) (il0 := il) (il' := imap B' f il).
    destruct idx as [idx [n nth_n] ]; simpl in *; subst.
    revert Bound nth_n il;
      induction n; destruct Bound; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

  Definition replace_BoundedIndex
           {B : A -> Type}
           (Bound : list A)
           (il : ilist B Bound)
           (idx : BoundedIndex (map projAC Bound))
           (new_b : B (nth_Bounded Bound idx))
  : ilist B Bound :=
    replace_Index (ibound idx) il (Dep_Option_elim (Some_Dep_Option _ _ new_b)).

  Variable C_eq_dec : forall c c' : C, {c = c'} + {c <> c'}.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx')),
      idx <> idx'
      -> ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
         ith_Bounded il idx.
  Proof.
    intros.
    eapply ith_Bounded_ind2 with (idx0 := idx) (il0 := replace_BoundedIndex il idx' new_b)
                                                (il' := il).
    eapply ith_replace_Index_neq; eauto using idx_ibound_eq.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx)),
      ith_Bounded (replace_BoundedIndex il idx new_b) idx = new_b.
  Proof.
    intros.
    eapply ith_Bounded_ind with (idx0 := idx)
                                  (il0 := replace_BoundedIndex il idx new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    eapply ith_replace_Index_eq; eauto.
  Qed.

  Lemma ith_replace_BoundedIndex_ind
        {B : A -> Type}
        (P : forall As (idx : BoundedIndex (map projAC As)),
               B (nth_Bounded As idx)
               -> B (nth_Bounded As idx) -> Prop)
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (new_b : B (nth_Bounded Bound idx')),
      (forall idx :  BoundedIndex (map projAC Bound),
         ibound idx <> ibound idx'
         -> P _ idx (ith_Bounded il idx)
              (ith_Bounded il idx))
      -> P _ idx' (ith_Bounded il idx') new_b
      -> P _ idx
           (ith_Bounded il idx)
           (ith_Bounded (replace_BoundedIndex il idx' new_b) idx).
  Proof.
    intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx'); subst.
    + rewrite ith_replace_BoundIndex_eq; assumption.
    + rewrite ith_replace_BoundIndex_neq;
      unfold not; eauto using idx_ibound_eq.
  Qed.

  Lemma ilist_eq {B : A -> Type}
  : forall (Bound : list A)
           (il il' : ilist B Bound),
      (forall idx, ith_Bounded il idx = ith_Bounded il' idx) -> il = il'.
  Proof.
    induction Bound; intros.
    - rewrite (ilist_invert il), (ilist_invert il'); reflexivity.
    - icons_invert; f_equal.
      generalize (H {| bindex := projAC a |}).
      unfold ith_Bounded; simpl; auto.
      apply IHBound; intros.
      generalize (H  {| bindex := bindex idx;
                       indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}).
      unfold ith_Bounded; simpl; auto.
  Qed.

  Lemma imap_replace_BoundedIndex
        {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           b,
      imap B' f (replace_BoundedIndex il idx b) =
      replace_BoundedIndex (imap B' f il) idx (f _ b).
  Proof.
    intros; apply ilist_eq; intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx0); subst;
    rewrite <- ith_Bounded_imap.
    - repeat rewrite ith_replace_BoundIndex_eq; reflexivity.
    - repeat rewrite ith_replace_BoundIndex_neq; auto.
      rewrite <- ith_Bounded_imap; auto.
  Qed.

End ithIndexBound.

Arguments BoundedString [_].
