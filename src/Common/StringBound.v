Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith ADTSynthesis.Common.ilist.
Require Import ADTSynthesis.Common.Equality ADTSynthesis.Common.UIP.
Require Import Coq.Program.Program.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Existing Class is_true.
Global Instance true_is_true : is_true true := eq_refl.
Global Instance orb_l_is_true {x y} `{is_true x} : is_true (x || y).
Proof. destruct x, y; simpl in *; congruence. Defined.
Global Instance orb_r_is_true {x y} `{is_true y} : is_true (x || y).
Proof. destruct x, y; simpl in *; congruence. Defined.
Global Instance andb_is_true {x y} `{is_true x, is_true y} : is_true (x && y).
Proof. destruct x, y; simpl in *; congruence. Defined.

Class has_beq A := beq : A -> A -> bool.
Notation has_beq_refl A := (forall x, is_true (@beq A _ x x)) (only parsing).
Class has_beq_bl A `{has_beq A} := beq_bl : forall x y, is_true (@beq A _ x y) -> x = y.
Arguments has_beq_bl _ {_}.
Instance: has_beq string := string_beq.
Instance: has_beq_refl string := fun x => string_lb (eq_refl x).
Instance: has_beq_bl string := @string_bl.

Fixpoint nth_eq {A} {eq_A : has_beq A} (n : nat) (a : A) (ls : list A) {struct ls} : bool
  := match ls with
       | nil => false
       | x::xs => match n with
                    | 0 => eq_A a x
                    | S m => nth_eq m a xs
                  end
     end.

Lemma nth_eq_bl {A} {eq_A : has_beq A} {bl : has_beq_bl A} (n : nat) (a a' : A) (ls : list A)
      {H0 : is_true (nth_eq n a ls)} {H1 : is_true (nth_eq n a' ls)}
: is_true (beq a a').
Proof.
  revert ls H0 H1; induction n; intros.
  { destruct ls; simpl in *.
    { exfalso; congruence. }
    { apply beq_bl in H1; subst; assumption. } }
  { destruct ls; simpl in *.
    { exfalso; congruence. }
    { eapply IHn; eassumption. } }
Defined.

Section IndexBound.

  Context {A : Set}.
  Context {eq_A : has_beq A}.
  Context {eq_A_refl : has_beq_refl A}.

  Class > IndexBound (a : A) (Bound : list A) :=
    { ibound : nat;
      boundi :> is_true (nth_eq ibound a Bound) }.

  (*Global Coercion ibound : IndexBound >-> nat.*)

  Global Arguments ibound [a Bound] _.
  Global Arguments boundi [a Bound] _.

  Global Instance IndexBound_head (a : A) (Bound : list A)
  : IndexBound a (a :: Bound) :=
    { ibound := 0 }.

  Global Instance IndexBound_tail
           (a a' : A) (Bound : list A)
           {sB' : IndexBound a Bound}
  : IndexBound a (a' :: Bound) :=
    { ibound := S (ibound sB') }.

  Record BoundedIndex (Bound : list A) :=
    { bindex :> A;
      indexb :> IndexBound bindex Bound }.

  Global Existing Instance indexb.

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
  Defined.

  Definition BoundedIndex_nil
             (AnyT : Type)
             (idx : BoundedIndex nil)
  : AnyT.
  Proof.
    destruct idx as [idx [[|n] nth_n]];
    simpl in *;
    congruence.
  Defined.

  Lemma indexb_ibound_eq {bl : has_beq_bl A} :
    forall Bound (bidx bidx' : BoundedIndex Bound),
      ibound (indexb bidx) = ibound (indexb bidx') ->
      bindex bidx = bindex bidx'.
  Proof.
    intros; induction Bound; simpl in *.
    - apply BoundedIndex_nil; auto.
    - destruct bidx as [bindex [n nth_n]];
      destruct bidx' as [bindex' [n' nth_n']]; simpl in *; subst.
      pose proof (nth_eq_bl n' bindex bindex' (a::Bound)) as H.
      apply beq_bl in H; exact H.
  Defined.

  Section Bounded_Index_Dec_Eq.
  (* If equality on A is decideable, so is equality
     on bounded indices in A. *)
    Variable A_eq_dec :
      forall a a' : A, {a = a'} + {a <> a'}.

    Require Import Coq.Logic.Eqdep_dec.

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
    Defined.

    (*Corollary idx_ibound_eq
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
    Qed.*)

    Corollary BoundedIndex_eq_dec Bound :
      forall idx idx' : (BoundedIndex Bound),
        {idx = idx'} + {idx <> idx'}.
    Proof.
      intros; destruct (eq_nat_dec (ibound idx) (ibound idx')); [ | right ];
      [ destruct (A_eq_dec (bindex idx) (bindex idx')); [ left | right ] | ];
      destruct idx as [idx [n0 ?]], idx' as [idx' [n1 ?]]; simpl in *; subst; repeat (f_equal; []).
      { apply dec_eq_uip, Bool.bool_dec. }
      { abstract congruence. }
      { intro H'.
        abstract (inversion H'; congruence). }
    Defined.

    End Bounded_Index_Dec_Eq.

End IndexBound.

Definition BoundedString := @BoundedIndex string.
Definition BoundedString_eq_dec
           {Bound}
           (bidx bidx' : BoundedString string_beq Bound)
: {bidx = bidx'} + {bidx <> bidx'} :=
  BoundedIndex_eq_dec string_dec  bidx bidx'.

Notation "`` A" :=
  ({| bindex := A%string |}) (at level 0, format "`` A").

Section ithIndexBound.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {C : Set}.
  Context {eq_C : has_beq C}.
  Context {eq_refl_C : has_beq_refl C}.
  Variable (projAC : A -> C).

  Lemma None_neq_Some
  : forall (AnyT AnyT' : Type) (a : AnyT),
      None = Some a -> AnyT'.
  Proof.
    intros; discriminate.
  Qed.

  (* Given a [BoundedIndex] for a list, we can always return an element. *)
  Fixpoint nth_Bounded'
             (Bound : list A)
             (c : C)
             (n : nat)
             (nth_n : is_true (nth_eq n c (map projAC Bound)))
             {struct Bound}
  : A
    := match Bound, n return is_true (nth_eq n c (map projAC Bound)) -> A  with
         | nil, _ => fun nth_n' => match Bool.diff_false_true nth_n' : False with end
         | x::_, 0 => fun _ => x
         | _::xs, S m => @nth_Bounded' xs c m
       end nth_n.

  (*Lemma nth_error_map :
    forall n As c_opt,
      nth_error (map projAC As) n = c_opt
      -> option_map projAC (nth_error As n) = c_opt.
  Proof.
    induction n; destruct As; simpl; eauto.
  Defined.*)

  Definition nth_Bounded
             (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
  : A
    := nth_Bounded' Bound (bindex idx) (ibound idx) (boundi idx).

  Global Arguments nth_Bounded !_ !_ / .

  (*(* We can lift [B (nth_Bounded idx)] to a dependent option. *)
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
     end (nth_error_map _ _ (boundi idx)).*)

  (* [nth_Bounded_rect] builds a function whose type depends
     on [nth_Bounded] by reducing to a case with [nth_error],
     which is easier to work/reason with. *)

  (*Definition nth_Bounded_rect
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
      end (nth_error_map _ _ (boundi idx)).*)

  (*(* [nth_Bounded_ind2] builds a function whose type depends
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
          (nth_error_map _ _ (boundi idx')).*)

  (* [nth_Bounded] returns the same elements as [nth_default] *)

  Lemma nth_Bounded_eq_nth_default
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (default_A : A),
      nth_Bounded Bound idx = nth (ibound idx) Bound default_A.
  Proof.
    unfold nth_Bounded in *.
    destruct idx as [? [n ?]].
    intros; generalize dependent n; induction Bound; intros.
    { simpl in *; congruence. }
    { destruct n; try reflexivity; simpl in *; eauto. }
  Qed.

  Lemma nth_Bounded_eq_nth_error
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (default_A : A),
      Some (nth_Bounded Bound idx) = nth_error Bound (ibound idx).
  Proof.
    unfold nth_Bounded in *.
    destruct idx as [? [n ?]].
    intros; generalize dependent n; induction Bound; intros.
    { simpl in *; congruence. }
    { destruct n; try reflexivity; simpl in *; eauto. }
  Qed.

  (* The result of [nth_Bounded] doesn't depend on the proof
     that [ibound] is a valid index. *)
  Lemma nth_Bounded_eq
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound)),
      ibound idx = ibound idx'
      -> nth_Bounded Bound idx = nth_Bounded Bound idx'.
  Proof.
    unfold nth_Bounded in *.
    destruct idx as [? [n ?]], idx' as [? [n' ?]]; simpl; intro; subst n'.
    intros; generalize dependent n; induction Bound; intros.
    { simpl in *; congruence. }
    { destruct n; try reflexivity; simpl in *; eauto. }
  Defined.

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition Dep_Option_extract_Some {A' B} {x : A'} (y : Dep_Option B (Some x)) : B x
    := match y in Dep_Option _ sx return match sx with
                                           | Some x' => B x'
                                           | None => True
                                         end with
         | Dep_Some _ b => b
         | Dep_None => I
       end.

  Fixpoint ith_Bounded'
           {B : A -> Type}
           (Bound : list A)
           (c : C)
           (n : nat)
           {struct Bound}
  : forall (nth_n : is_true (nth_eq n c (map projAC Bound)))
           (il : ilist B Bound),
      B (nth_Bounded' Bound c n nth_n)
    := match Bound, n
             return (forall (nth_n : is_true (nth_eq n c (map projAC Bound)))
                            (il : ilist B Bound),
                       B (nth_Bounded' Bound c n nth_n))
       with
         | nil, _ => fun nth_n' _ => match Bool.diff_false_true nth_n' : False with end
         | x::_, 0 => fun _ il => ilist_hd il
         | _::xs, S m => fun nth_n il => @ith_Bounded' B xs c m nth_n (ilist_tl il)
       end.

  Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx)
    := ith_Bounded' (bindex idx) (ibound idx) (boundi idx) il.

  Global Arguments ith_Bounded _ !_ _ !_ / .

  (* To build a reasoning principle for ith_Bounded, we need to
     show that option types are shuffled around by [Dep_Option_elim] *)
    (*Definition ith_error_eq_P
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
      end b c d.*)

  (*Lemma ith_error_eq
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
    Defined.*)

    (* [ith_Bounded_rect] builds a function whose type depends
     on [ith_Bounded] by reducing to a case with [ith_error],
     which is easier to work/reason with. *)

    Definition ith_Bounded_rect
            {B : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As -> forall a : A, B a -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      Dep_Option_elim_P (P Bound idx il) (ith_error il (ibound idx))
      -> P Bound idx il _ (ith_Bounded il idx).
    Proof.
      unfold ith_Bounded, nth_Bounded in *.
      intros Bound [idx [n H']]; simpl.
      generalize dependent n; induction Bound; simpl in *; try congruence; []; intros.
      destruct n; simpl in *.
      { assumption. }
      { dependent destruction il.        Unset Printing Notations.
                specialize (IHBound _ H').

              Arguments ith_Bounded' : clear implicits.
 edestruct Bool.diff_false_true
      Focus 2.

      fun Bound idx il =>
                match (nth_error Bound (ibound idx)) as e
                      return
                      forall (b : Dep_Option B e)
                             (c : option_map _ e = Some (bindex idx))
                             d,
                        (ith_error_eq_P Bound idx b c d)
                        -> Dep_Option_elim_P (P Bound idx il) b ->
                        P _ _ _ (@nth_Bounded' _ _ e c) d with
                  | Some a => fun b e_eq d c_eq =>
                                match c_eq with
                                  | eq_refl => fun b_opt => b_opt
                                end
                  | None => fun _ e_eq _ _ _ => None_neq_Some _ e_eq
                end (ith_error il (ibound idx))
                    _
                    (ith_Bounded il idx)
                    (ith_error_eq idx il).

    (*Definition ith_Bounded_rect2
               {B B' : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As
                        -> ilist B' As
                        -> forall a : A, B a -> B' a -> Type)
        (Bound : list A)
        (idx : BoundedIndex (map projAC Bound))
        (il : ilist B Bound)
        (il' : ilist B' Bound)
    : Dep_Option_elim_T2 (P Bound idx il il')
                         (ith_error il (ibound idx))
                         (ith_error il' (ibound idx))
      -> P Bound idx il il' _
           (ith_Bounded il idx)
           (ith_Bounded il' idx) :=
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith_error_eq_P Bound idx b c d)
                   -> (ith_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_T2 (P Bound idx il il') b b' ->
                   P _ _ _ _ (@nth_Bounded' _ _ _ c) d d' with
        | Some a => fun b b' e_eq d d' d_eq d'_eq =>
                      match d_eq, d'_eq with
                        | eq_refl, eq_refl => fun b_opt => b_opt
                      end
        | None => fun b b' e_eq d d' d_eq d'_eq => None_neq_Some _ e_eq
           end (ith_error il (ibound idx))
               (ith_error il' (ibound idx) )
               _
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_error_eq idx il)
               (ith_error_eq idx il').*)

    (*Program Definition nth_Bounded_ind
            (P : forall As, BoundedIndex (map projAC As)
                            -> A -> Prop)
    : forall (Bound : list A)
             (idx : BoundedIndex (map projAC Bound)),
        match nth_error Bound (ibound idx) with
          | Some a => P Bound idx a
          | _ => True
        end
        -> P Bound idx (nth_Bounded _ idx) :=
      fun Bound idx =>
        match (nth_error Bound (ibound idx)) as e return
              (forall (f : option_map _ e = Some (bindex idx)),
                 (match e with
                    | Some a => P Bound idx a
                    | _ => True
                  end)
                 -> P Bound idx
                      (match e as e'' return
                             option_map _ e'' = Some (bindex idx)
                             -> A
                       with
                         | Some a => fun _ => a
                         | _ => fun f => _
                       end f)) with
          | Some a => fun _ H => _
          | _ => fun f => _
        end (nth_error_map _ _ (boundi idx)).

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
    Qed.*)

    (* [ith_Bounded_ind2] builds a proof whose type depends
     on *two* occurences of [ith_Bounded] by reducing  it to a case
     with two [ith_error]s, which is easier to reason with. *)

    (*Program Definition ith_Bounded_ind2
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                            -> ilist B As
                            -> ilist B' As
                            -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound),
      Dep_Option_elim_P2 (P Bound idx il il')
                      (ith_error il (ibound idx))
                      (ith_error il' (ibound idx) )
      -> P Bound idx il il' _ (ith_Bounded il idx) (ith_Bounded il' idx) :=
    fun Bound idx il il' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith_error_eq_P Bound idx b c d)
                   -> (ith_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_P2 (P Bound idx il il') b b' ->
                   P _ _ _ _ (@nth_Bounded' _ _ _ c) d d' with
          | Some a => _
          | None => _
           end (ith_error il (ibound idx))
               (ith_error il' (ibound idx) )
               _
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_error_eq idx il)
               (ith_error_eq idx il').*)

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

    (*Program Definition ith_Bounded_ind3
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
               (ith_error_eq idx il'').*)

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

Section i2thIndexBound.

  Require Import ADTSynthesis.Common.i2list.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {D : Set}.
  Variable (projAD : A -> D).

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition i2th_Bounded
          {B : A -> Type}
          {C : forall a, B a -> Type}
          {As}
          (Bs : ilist B As)
          (Cs : i2list C Bs)
          (idx : BoundedIndex (map projAD As))
  : C (nth_Bounded _ As idx) (ith_Bounded projAD Bs idx) :=
    ith_Bounded_rect projAD (fun _ _ _ => C) idx Bs
                           (i2th_error' Cs (ibound idx)).

  (*Lemma ith_Bounded_imap
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
  Qed. *)

  (* We can lift [C (ith_Bounded idx)] to a dependent option. *)
  Definition Some_Dep_Option_elim_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (Bs : ilist B As)
             (idx : BoundedIndex (map projAD As))
             (c_opt : C (nth_Bounded projAD As idx) (ith_Bounded projAD Bs idx))
  : Dep_Option_elim_P C (ith_error Bs (ibound idx)) :=
    match (nth_error As (ibound idx)) as e return
          forall nth_n
                 (b : B (@nth_Bounded' _ _ _ _ _ e nth_n))
                 b_opt,
            ith_error_eq_P projAD As idx
                           b_opt
                           nth_n
                           b
            -> C _ b
            -> Dep_Option_elim_P C (a_opt := e) b_opt with
      | Some a => fun nth_n b b_opt b_eq c =>
                    match b_eq in _ = b'
                          return C _ b' -> _ with
                      | eq_refl => fun c => c
                    end c
      | None => fun nth_n b b_opt b_eq c => I
    end (nth_error_map _ _ _ (boundi idx))
        _ _ (ith_error_eq _ _ _) c_opt.

  Definition replace_BoundedIndex2
           {B : A -> Type}
           {C : forall a, B a -> Type}
           {As}
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (idx : BoundedIndex (map projAD As))
           (new_c : C _ (ith_Bounded projAD Bs idx))
  : i2list C Bs :=
    replace_Index2' (ibound idx) Cs
                   (Some_Dep_Option_elim_P Bs idx new_c).

  Definition Dep_Option_elim2_P2
             {B : A -> Type}
             {C C' : forall a, B a -> Type}
             (P : forall a b, C a b -> C' a b -> Prop)
             (a_opt : option A)
    := match a_opt return
             forall (b : Dep_Option B a_opt),
               Dep_Option_elim_P C (a_opt := a_opt) b
               -> Dep_Option_elim_P C' (a_opt := a_opt) b -> Prop with
         | Some a => fun b => P a (Dep_Option_elim b)
         | None => fun _ _ _ => True
       end .

  Lemma Dep_Option_elim2_P2_refl
        {B : A -> Type}
        {C C' : forall a, B a -> Type}
  : forall a_opt b_opt c_opt,
      Dep_Option_elim2_P2 (fun (a : A) (b : B a) (c c' : C a b) => c = c')
                          (a_opt := a_opt) b_opt c_opt c_opt.
    unfold Dep_Option_elim2_P2; destruct a_opt; eauto.
  Qed.

  Definition i2th_error_eq_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (idx : BoundedIndex (map projAD As))
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (c_opt : Dep_Option_elim_P C b_opt)
             (e_eq : option_map projAD a_opt = Some (bindex idx))
             (c_opt' : C (nth_Bounded' projAD As a_opt e_eq)
                         (ith_Bounded' projAD As e_eq b_opt))
  : Type :=
      match a_opt as a_opt'
        return
        forall (b_opt : Dep_Option B a_opt')
               (e_eq : option_map projAD a_opt' = Some (bindex idx)),
          Dep_Option_elim_P C b_opt ->
          C (nth_Bounded' projAD As a_opt' e_eq)
            (ith_Bounded' projAD As e_eq b_opt)
          -> Type
      with
        | Some a =>
          fun b_opt e_eq c_opt c_opt' => c_opt = c_opt'
        | None => fun b_opt e_eq c_opt c_opt' => True
      end b_opt e_eq c_opt c_opt'.

    Lemma ilist_invert' {B} (As : list A) (il : ilist B As) :
      match As as As' return ilist B As' -> Type with
        | a :: As' => fun il => { b : _ & {il' : _ & il = icons a b il'}}
        | nil => fun il => il = inil _
      end il.
    Proof.
      destruct il; eauto.
    Qed.

    Lemma i2th_error_eq
          {B : A -> Type}
          {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist B As)
             (Cs : i2list C Bs),
        i2th_error_eq_P As idx
        (ith_error Bs (ibound idx))
        (i2th_error' Cs (ibound idx))
        (nth_error_map _ _ _ (boundi idx))
        (i2th_Bounded Cs idx).
    Proof.
      unfold i2th_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Cs; simpl; eauto.
      intros; generalize (IHn As idx In_n (ilist_tl Bs) Cs); intro H';
      unfold i2th_Bounded, ith_Bounded_rect; simpl; eauto.
    Qed.

    Definition i2th_error_eq'
               {B : A -> Type}
               {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist B As)
             (c : C (nth_Bounded _ As idx) (ith_Bounded _ Bs idx)),
        i2th_error_eq_P As idx (ith_error Bs (ibound idx))
                        (Some_Dep_Option_elim_P Bs idx c)
                        (nth_error_map projAD (ibound idx) As (boundi idx)) c.
    Proof.
      unfold i2th_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Bs; simpl; eauto.
      generalize (IHn As idx In_n Bs);
      unfold i2th_Bounded, ith_Bounded_rect; simpl; eauto.
    Qed.

    Program Definition i2th_Bounded_ind
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist B As) (Cs : i2list C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
    : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (c : C' (nth_Bounded _ As idx) (ith_Bounded _ Bs idx)),
        Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith_error Bs (ibound idx))
                          (i2th_error' Cs (ibound idx))
                          (Some_Dep_Option_elim_P Bs idx c)
        -> P As Bs Cs idx _ (ith_Bounded _ Bs idx) (i2th_Bounded Cs idx) c
      := fun As idx Bs Cs c H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith_Bounded' projAD As e_eq b_opt)),
                 i2th_error_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith_error Bs (ibound idx))
             (i2th_error' Cs (ibound idx))
             (Some_Dep_Option_elim_P _ _ c)
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error_eq _ _) (i2th_error_eq' _ _ _) H.

    Program Definition i2th_Bounded_ind2
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist B As) (Cs : i2list C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
  : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (Cs' : i2list C' Bs),
      Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith_error Bs (ibound idx))
                          (i2th_error' Cs (ibound idx))
                          (i2th_error' Cs' (ibound idx))
      -> P As Bs Cs idx _ (ith_Bounded _ Bs idx)
           (i2th_Bounded Cs idx)
           (i2th_Bounded Cs' idx)
      := fun As idx Bs Cs Cs' H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith_Bounded' projAD As e_eq b_opt)),
                 i2th_error_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith_error Bs (ibound idx))
             (i2th_error' Cs (ibound idx))
             (i2th_error' Cs' (ibound idx))
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error_eq _ _) (i2th_error_eq _ _) H.

    Definition Dep_Option_elim2_T2
             {B : A -> Type}
             {C C' : forall a, B a -> Type}
             (P : forall a b, C a b -> C' a b -> Type)
             (a_opt : option A)
    := match a_opt return
             forall (b : Dep_Option B a_opt),
               Dep_Option_elim_P C (a_opt := a_opt) b
               -> Dep_Option_elim_P C' (a_opt := a_opt) b -> Type with
         | Some a => fun b => P a (Dep_Option_elim b)
         | None => fun _ _ _ => True
       end .

    Program Definition i2th_Bounded_rect
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist B As) (Cs : i2list C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Type)
    : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (c : C' (nth_Bounded _ As idx) (ith_Bounded _ Bs idx)),
        Dep_Option_elim2_T2 (P As Bs Cs idx)
                          (ith_error Bs (ibound idx))
                          (i2th_error' Cs (ibound idx))
                          (Some_Dep_Option_elim_P Bs idx c)
        -> P As Bs Cs idx _ (ith_Bounded _ Bs idx) (i2th_Bounded Cs idx) c
      := fun As idx Bs Cs c H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith_Bounded' projAD As e_eq b_opt)),
                 i2th_error_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_T2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith_error Bs (ibound idx))
             (i2th_error' Cs (ibound idx))
             (Some_Dep_Option_elim_P _ _ c)
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error_eq _ _) (i2th_error_eq' _ _ _) H.

  Variable D_eq_dec : forall d d' : D, {d = d'} + {d <> d'}.

  Lemma i2th_replace_BoundIndex_neq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist B As)
      (Cs : i2list C Bs)
      (idx idx' : BoundedIndex (map projAD As))
      (new_c : C _ (ith_Bounded projAD Bs idx')),
      idx <> idx'
      -> i2th_Bounded (replace_BoundedIndex2 Cs idx' new_c) idx =
         i2th_Bounded Cs idx.
  Proof.
    intros.
    eapply (i2th_Bounded_ind2
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace_BoundedIndex2.
    rewrite i2th_replace_Index'_neq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed.

  Lemma i2th_replace_BoundIndex_eq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist B As)
      (Cs : i2list C Bs)
      (idx : BoundedIndex (map projAD As))
      (new_c : C _ (ith_Bounded projAD Bs idx)),
      i2th_Bounded (replace_BoundedIndex2 Cs idx new_c) idx =
      new_c.
  Proof.
    intros.
    eapply (i2th_Bounded_ind
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace_BoundedIndex2.
    rewrite i2th_replace_Index'_eq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed.

End i2thIndexBound.

Section ith2IndexBound.

  Require Import ADTSynthesis.Common.ilist2.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {C : Set}.
  Variable (projAC : A -> C).

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition ith2_Bounded'
          {B : A -> Type}
          (As : list A)
          (d : C)
          (a_opt : option A)
  : forall (nth_n : option_map projAC a_opt = Some d),
      Dep_Option B a_opt
      -> B (nth_Bounded' projAC As a_opt nth_n) :=
    match a_opt as a'
          return
          forall (f : option_map projAC a' = Some d),
            Dep_Option B a' ->
            B (nth_Bounded' projAC As _ f) with
      | Some a => fun nth_n b => Dep_Option_elim b
      | None => fun nth_n b => None_neq_Some _ nth_n
    end.

  Definition ith2_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist2 B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded projAC Bound idx) :=
    ith2_Bounded' Bound (nth_error_map _ _ _ (boundi idx))
                 (ith2_error il (ibound idx)).

  (*match (nth_error Bound (ibound idx)) as a'
                  return
                  Dep_Option B a' ->
                  forall (f : option_map _ a' = Some (bindex idx)),
                    B (nth_Bounded' Bound _ f) with
        | Some a => fun b _ => Dep_Option_elim b
        | None => fun _ f => None_neq_Some _ f
    end (ith2_error il (ibound idx)) (nth_error_map _ _ (boundi idx)). *)

  (* To build a reasoning principle for ith2_Bounded, we need to
     show that option types are shuffled around by [Dep_Option_elim] *)
    Definition ith2_error_eq_P
               {B : A -> Type}
               (Bound : list A)
               (idx : BoundedIndex (map projAC Bound))
               e' b c d :=
      match e' as e'
        return
        (Dep_Option B e' ->
         forall c : option_map _ e' = Some (bindex idx),
           B (nth_Bounded' projAC Bound _ c) -> Type)
      with
        | Some e =>
          fun b c d => Dep_Option_elim b = d
        | None => fun b c d => True
      end b c d.

    Lemma ith2_error_eq
          {B : A -> Type}
    : forall (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
              (il : ilist2 B Bound),
        ith2_error_eq_P Bound idx
        (ith2_error il (ibound idx))
        (nth_error_map _ _ _ (boundi idx))
        (ith2_Bounded il idx).
    Proof.
      unfold ith2_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n; induction Bound; destruct n;
      simpl; eauto; intros.
      eapply IHBound.
    Defined.

    (* [ith2_Bounded_rect] builds a function whose type depends
     on [ith2_Bounded] by reducing to a case with [ith2_error],
     which is easier to work/reason with. *)

    Definition ith2_Bounded_rect
            {B : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As -> forall a : A, B a -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound),
      Dep_Option_elim_P (P Bound idx il) (ith2_error il (ibound idx))
      -> P Bound idx il _ (ith2_Bounded il idx) :=
      fun Bound idx il =>
                match (nth_error Bound (ibound idx)) as e
                      return
                      forall (b : Dep_Option B e)
                             (c : option_map _ e = Some (bindex idx))
                             d,
                        (ith2_error_eq_P Bound idx b c d)
                        -> Dep_Option_elim_P (P Bound idx il) b ->
                        P _ _ _ (@nth_Bounded' _ _ projAC _ _ e c) d with
                  | Some a => fun b e_eq d c_eq =>
                                match c_eq with
                                  | eq_refl => fun b_opt => b_opt
                                end
                  | None => fun _ e_eq _ _ _ => None_neq_Some _ e_eq
                end (ith2_error il (ibound idx))
                    _
                    (ith2_Bounded il idx)
                    (ith2_error_eq idx il).

    Definition ith2_Bounded_rect2
               {B B' : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As
                        -> ilist2 B' As
                        -> forall a : A, B a -> B' a -> Type)
        (Bound : list A)
        (idx : BoundedIndex (map projAC Bound))
        (il : ilist2 B Bound)
        (il' : ilist2 B' Bound)
    : Dep_Option_elim_T2 (P Bound idx il il')
                         (ith2_error il (ibound idx))
                         (ith2_error il' (ibound idx))
      -> P Bound idx il il' _
           (ith2_Bounded il idx)
           (ith2_Bounded il' idx) :=
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith2_error_eq_P Bound idx b c d)
                   -> (ith2_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_T2 (P Bound idx il il') b b' ->
                   P _ _ _ _ (@nth_Bounded' _ _ projAC _ _ _ c) d d' with
        | Some a => fun b b' e_eq d d' d_eq d'_eq =>
                      match d_eq, d'_eq with
                        | eq_refl, eq_refl => fun b_opt => b_opt
                      end
        | None => fun b b' e_eq d d' d_eq d'_eq => None_neq_Some _ e_eq
           end (ith2_error il (ibound idx))
               (ith2_error il' (ibound idx) )
               _
               (ith2_Bounded il idx)
               (ith2_Bounded il' idx)
               (ith2_error_eq idx il)
               (ith2_error_eq idx il').

    (* [ith2_Bounded_ind] builds a proof whose type depends
     on both [nth_Bounded] and an occurence of [ith2_Bounded] by reducing
     it to a case with an [ith2_error], which is easier to reason with. *)

    Program Definition ith2_Bounded_ind
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (b : B' (nth_Bounded projAC Bound idx)),
      Dep_Option_elim_P2 (P Bound idx il) (ith2_error il (ibound idx))
                      (Some_Dep_Option projAC Bound idx b)
      -> P Bound idx il _ (ith2_Bounded il idx) b :=
      fun Bound idx il b =>
        match (nth_error Bound (ibound idx)) as e
              return
              forall (b : Dep_Option B e)
                     (b' : Dep_Option B' e)
                     (c : option_map _ e = Some (bindex idx))
                     d d',
                (ith2_error_eq_P Bound idx b c d)
                -> (ith2_error_eq_P Bound idx b' c d')
                -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                P _ _ _ (@nth_Bounded' _ _ projAC _ _ _ c) d d' with
          | Some a => _
          | None => _
        end (ith2_error il (ibound idx))
            (Some_Dep_Option projAC Bound idx b)
            _
            (ith2_Bounded il idx)
            b
            (ith2_error_eq idx il)
            _.
    Next Obligation.
      unfold ith2_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      unfold Some_Dep_Option; simpl.
      intros; eapply IHBound.
    Qed.

    (* [ith2_Bounded_ind2] builds a proof whose type depends
     on *two* occurences of [ith2_Bounded] by reducing  it to a case
     with two [ith2_error]s, which is easier to reason with. *)

    Program Definition ith2_Bounded_ind2
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (il' : ilist2 B' Bound),
      Dep_Option_elim_P2 (P Bound idx il)
                      (ith2_error il (ibound idx))
                      (ith2_error il' (ibound idx) )
      -> P Bound idx il _ (ith2_Bounded il idx) (ith2_Bounded il' idx) :=
    fun Bound idx il il' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith2_error_eq_P Bound idx b c d)
                   -> (ith2_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                   P _ _ _ (@nth_Bounded' _ _ projAC _ _ _ c) d d' with
          | Some a => _
          | None => _
           end (ith2_error il (ibound idx))
               (ith2_error il' (ibound idx) )
               _
               (ith2_Bounded il idx)
               (ith2_Bounded il' idx)
               (ith2_error_eq idx il)
               (ith2_error_eq idx il').

    Program Definition ith2_Bounded_ind3
            {B B' B'' : A -> Type}
            (P : forall As,
                   BoundedIndex (map projAC As)
                   -> ilist2 B As
                   -> ilist2 B' As
                   -> ilist2 B'' As
                   -> forall a : A,
                        B a -> B' a -> B'' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (il' : ilist2 B' Bound)
           (il'' : ilist2 B'' Bound),
      Dep_Option_elim_P3 (P Bound idx il il' il'')
                      (ith2_error il (ibound idx))
                      (ith2_error il' (ibound idx))
                      (ith2_error il'' (ibound idx))
      -> P Bound idx il il' il'' _
           (ith2_Bounded il idx)
           (ith2_Bounded il' idx)
           (ith2_Bounded il'' idx) :=
    fun Bound idx il il' il'' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (b'' : Dep_Option B'' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d' d'',
                   (ith2_error_eq_P Bound idx b c d)
                   -> (ith2_error_eq_P Bound idx b' c d')
                   -> (ith2_error_eq_P Bound idx b'' c d'')
                   -> Dep_Option_elim_P3 (P Bound idx il il' il'') b b' b'' ->
                   P Bound idx il il' il''
                     (@nth_Bounded' _ _ _ _ _ _ c)
                     d d' d'' with
          | Some a => _
          | _  => _
           end (ith2_error il (ibound idx))
               (ith2_error il' (ibound idx) )
               (ith2_error il'' (ibound idx) )
               _
               (ith2_Bounded il idx)
               (ith2_Bounded il' idx)
               (ith2_Bounded il'' idx)
               (ith2_error_eq idx il)
               (ith2_error_eq idx il')
               (ith2_error_eq idx il'').

  Lemma ith2_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound),
      f _ (ith2_Bounded il idx) =
      ith2_Bounded (imap2 B' f il) idx.
  Proof.
    intros.
    eapply ith2_Bounded_ind2 with (idx0 := idx) (il0 := il) (il' := imap2 B' f il).
    destruct idx as [idx [n nth_n] ]; simpl in *; subst.
    revert Bound nth_n il;
      induction n; destruct Bound; simpl; eauto;
    intros; icons2_invert; simpl; auto.
  Qed.

  Definition replace2_BoundedIndex
           {B : A -> Type}
           (Bound : list A)
           (il : ilist2 B Bound)
           (idx : BoundedIndex (map projAC Bound))
           (new_b : B (nth_Bounded projAC Bound idx))
  : ilist2 B Bound :=
    replace_Index2 (ibound idx) il (Dep_Option_elim (Some_Dep_Option _ _ _ new_b)).

  Variable C_eq_dec : forall c c' : C, {c = c'} + {c <> c'}.

  Lemma ith2_replace_BoundIndex_neq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist2 _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded projAC Bound idx')),
      idx <> idx'
      -> ith2_Bounded (replace2_BoundedIndex il idx' new_b) idx =
         ith2_Bounded il idx.
  Proof.
    intros.
    eapply ith2_Bounded_ind2 with (idx0 := idx) (il0 := replace2_BoundedIndex il idx' new_b)
                                                (il' := il).
    eapply ith2_replace_Index2_neq; eauto using idx_ibound_eq.
  Qed.

  Lemma ith2_replace_BoundIndex_eq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist2 _ Bound)
      (idx : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded projAC Bound idx)),
      ith2_Bounded (replace2_BoundedIndex il idx new_b) idx = new_b.
  Proof.
    intros.
    eapply ith2_Bounded_ind with (idx0 := idx)
                                  (il0 := replace2_BoundedIndex il idx new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    eapply ith2_replace_Index2_eq; eauto.
  Qed.

  Lemma ith2_replace_BoundedIndex_ind
        {B : A -> Type}
        (P : forall As (idx : BoundedIndex (map projAC As)),
               B (nth_Bounded projAC As idx)
               -> B (nth_Bounded projAC As idx) -> Prop)
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (new_b : B (nth_Bounded projAC Bound idx')),
      (forall idx :  BoundedIndex (map projAC Bound),
         ibound idx <> ibound idx'
         -> P _ idx (ith2_Bounded il idx)
              (ith2_Bounded il idx))
      -> P _ idx' (ith2_Bounded il idx') new_b
      -> P _ idx
           (ith2_Bounded il idx)
           (ith2_Bounded (replace2_BoundedIndex il idx' new_b) idx).
  Proof.
    intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx'); subst.
    + rewrite ith2_replace_BoundIndex_eq; assumption.
    + rewrite ith2_replace_BoundIndex_neq;
      unfold not; eauto using idx_ibound_eq.
  Qed.

  Lemma ilist2_eq {B : A -> Type}
  : forall (Bound : list A)
           (il il' : ilist2 B Bound),
      (forall idx, ith2_Bounded il idx = ith2_Bounded il' idx) -> il = il'.
  Proof.
    induction Bound; intros.
    - rewrite (ilist2_invert il), (ilist2_invert il'); reflexivity.
    - icons2_invert; f_equal.
      generalize (H {| bindex := projAC a |}).
      unfold ith2_Bounded; simpl; auto.
      apply IHBound; intros.
      generalize (H  {| bindex := bindex idx;
                       indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}).
      unfold ith2_Bounded; simpl; auto.
  Qed.

  Lemma imap2_replace2_BoundedIndex
        {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           b,
      imap2 B' f (replace2_BoundedIndex il idx b) =
      replace2_BoundedIndex (imap2 B' f il) idx (f _ b).
  Proof.
    intros; apply ilist2_eq; intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx0); subst;
    rewrite <- ith2_Bounded_imap.
    - repeat rewrite ith2_replace_BoundIndex_eq; reflexivity.
    - repeat rewrite ith2_replace_BoundIndex_neq; auto.
      rewrite <- ith2_Bounded_imap; auto.
  Qed.

End ith2IndexBound.

Section i2th2IndexBound.

  Require Import ADTSynthesis.Common.i2list2.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {D : Set}.
  Variable (projAD : A -> D).

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition i2th2_Bounded
          {B B' : A -> Type}
          {C : forall a, B a -> B' a -> Type}
          {As}
          (Bs : ilist B As)
          (Bs' : ilist B' As)
          (Cs : i2list2 C Bs Bs')
          (idx : BoundedIndex (map projAD As))
  : C (nth_Bounded _ As idx)
      (ith_Bounded projAD Bs idx)
      (ith_Bounded projAD Bs' idx) :=
    ith_Bounded_rect2 projAD (fun _ _ _ _ => C) idx Bs Bs'
                       (i2th_error2' Cs (ibound idx)).

  (*Definition Some_Dep_Option_elim_P2
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (Bs : ilist2 B As)
             (idx : BoundedIndex (map projAD As))
             (c_opt : C (nth_Bounded projAD As idx) (ith2_Bounded projAD Bs idx))
  : Dep_Option_elim_P C (ith2_error Bs (ibound idx)) :=
    match (nth_error As (ibound idx)) as e return
          forall nth_n
                 (b : B (@nth_Bounded' _ _ _ _ _ e nth_n))
                 b_opt,
            ith_error_eq_P projAD As idx
                           b_opt
                           nth_n
                           b
            -> C _ b
            -> Dep_Option_elim_P C (a_opt := e) b_opt with
      | Some a => fun nth_n b b_opt b_eq c =>
                    match b_eq in _ = b'
                          return C _ b' -> _ with
                      | eq_refl => fun c => c
                    end c
      | None => fun nth_n b b_opt b_eq c => I
    end (nth_error_map _ _ _ (boundi idx))
        _ _ (ith2_error_eq _ _ _) c_opt.

  Definition replace2_BoundedIndex2
           {B : A -> Type}
           {C : forall a, B a -> Type}
           {As}
           (Bs : ilist2 B As)
           (Cs : i2list2 C Bs)
           (idx : BoundedIndex (map projAD As))
           (new_c : C _ (ith2_Bounded projAD Bs idx))
  : i2list2 C Bs :=
    replace_2Index2' (ibound idx) Cs
                   (Some_Dep_Option_elim_P2 Bs idx new_c).

  Definition Dep_Option_2elim2_P2
             {B : A -> Type}
             {C C' : forall a, B a -> Type}
             (P : forall a b, C a b -> C' a b -> Prop)
             (a_opt : option A)
    := match a_opt return
             forall (b : Dep_Option B a_opt),
               Dep_Option_elim_P C (a_opt := a_opt) b
               -> Dep_Option_elim_P C' (a_opt := a_opt) b -> Prop with
         | Some a => fun b => P a (Dep_Option_elim b)
         | None => fun _ _ _ => True
       end .

  Lemma Dep_Option_2elim2_P2_refl
        {B : A -> Type}
        {C C' : forall a, B a -> Type}
  : forall a_opt b_opt c_opt,
      Dep_Option_2elim2_P2 (fun (a : A) (b : B a) (c c' : C a b) => c = c')
                          (a_opt := a_opt) b_opt c_opt c_opt.
    unfold Dep_Option_2elim2_P2; destruct a_opt; eauto.
  Qed.

  Definition i2th_error2_eq_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (idx : BoundedIndex (map projAD As))
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (c_opt : Dep_Option_elim_P C b_opt)
             (e_eq : option_map projAD a_opt = Some (bindex idx))
             (c_opt' : C (nth_Bounded' projAD As a_opt e_eq)
                         (ith2_Bounded' projAD As e_eq b_opt))
  : Type :=
      match a_opt as a_opt'
        return
        forall (b_opt : Dep_Option B a_opt')
               (e_eq : option_map projAD a_opt' = Some (bindex idx)),
          Dep_Option_elim_P C b_opt ->
          C (nth_Bounded' projAD As a_opt' e_eq)
            (ith2_Bounded' projAD As e_eq b_opt)
          -> Type
      with
        | Some a =>
          fun b_opt e_eq c_opt c_opt' => c_opt = c_opt'
        | None => fun b_opt e_eq c_opt c_opt' => True
      end b_opt e_eq c_opt c_opt'.

    Lemma i2th_error2_eq
          {B : A -> Type}
          {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist2 B As)
             (Cs : i2list2 C Bs),
        i2th_error2_eq_P As idx
        (ith2_error Bs (ibound idx))
        (i2th_error2' Cs (ibound idx))
        (nth_error_map _ _ _ (boundi idx))
        (i2th2_Bounded Cs idx).
    Proof.
      unfold i2th_error2_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Cs; simpl; eauto.
      intros; generalize (IHn As idx In_n (ilist2_tl Bs) Cs); intro H';
      unfold i2th_Bounded, ith2_Bounded_rect; simpl; eauto.
    Qed.

    Definition i2th_error2_eq'
               {B : A -> Type}
               {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist2 B As)
             (c : C (nth_Bounded _ As idx) (ith2_Bounded _ Bs idx)),
        i2th_error2_eq_P As idx (ith2_error Bs (ibound idx))
                        (Some_Dep_Option_elim_P2 Bs idx c)
                        (nth_error_map projAD (ibound idx) As (boundi idx)) c.
    Proof.
      unfold i2th_error2_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Bs; simpl; eauto.
      generalize (IHn As idx In_n Bs);
      unfold i2th_Bounded, ith2_Bounded_rect; simpl; eauto.
    Qed.

    Program Definition i2th_Bounded2_ind
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist2 B As) (Cs : i2list2 C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
    : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist2 B As)
           (Cs : i2list2 C Bs)
           (c : C' (nth_Bounded _ As idx) (ith2_Bounded _ Bs idx)),
        Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith2_error Bs (ibound idx))
                          (i2th_error2' Cs (ibound idx))
                          (Some_Dep_Option_elim_P2 Bs idx c)
        -> P As Bs Cs idx _ (ith2_Bounded _ Bs idx) (i2th2_Bounded Cs idx) c
      := fun As idx Bs Cs c H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith2_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith2_Bounded' projAD As e_eq b_opt)),
                 i2th_error2_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error2_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith2_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith2_error Bs (ibound idx))
             (i2th_error2' Cs (ibound idx))
             (Some_Dep_Option_elim_P2 _ _ c)
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error2_eq _ _) (i2th_error2_eq' _ _ _) H.

    Program Definition i2th_Bounded2_ind2
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist2 B As) (Cs : i2list2 C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
  : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist2 B As)
           (Cs : i2list2 C Bs)
           (Cs' : i2list2 C' Bs),
      Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith2_error Bs (ibound idx))
                          (i2th_error2' Cs (ibound idx))
                          (i2th_error2' Cs' (ibound idx))
      -> P As Bs Cs idx _ (ith2_Bounded _ Bs idx)
           (i2th2_Bounded Cs idx)
           (i2th2_Bounded Cs' idx)
      := fun As idx Bs Cs Cs' H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith2_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith2_Bounded' projAD As e_eq b_opt)),
                 i2th_error2_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error2_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith2_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith2_error Bs (ibound idx))
             (i2th_error2' Cs (ibound idx))
             (i2th_error2' Cs' (ibound idx))
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error2_eq _ _) (i2th_error2_eq _ _) H.

  Variable D_eq_dec : forall d d' : D, {d = d'} + {d <> d'}.

  Lemma i2th_replace2_BoundIndex_neq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist2 B As)
      (Cs : i2list2 C Bs)
      (idx idx' : BoundedIndex (map projAD As))
      (new_c : C _ (ith2_Bounded projAD Bs idx')),
      idx <> idx'
      -> i2th2_Bounded (replace2_BoundedIndex2 Cs idx' new_c) idx =
         i2th2_Bounded Cs idx.
  Proof.
    intros.
    pose (i2th_Bounded2_ind2 (B := B) (C' := C)
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace2_BoundedIndex2.
    unfold i2th2_Bounded.
    rewrite i2th_replace_2Index2'_neq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed.

  Lemma i2th_replace2_BoundIndex_eq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist2 B As)
      (Cs : i2list2 C Bs)
      (idx : BoundedIndex (map projAD As))
      (new_c : C _ (ith2_Bounded projAD Bs idx)),
      i2th2_Bounded (replace2_BoundedIndex2 Cs idx new_c) idx =
      new_c.
  Proof.
    intros.
    eapply (i2th_Bounded2_ind
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace2_BoundedIndex2.
    rewrite i2th_replace_2Index2'_eq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed. *)

End i2th2IndexBound.

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
           (*| |- context [ ``(?R) ] =>
             let idx := fresh in
             set ``(R) as fresh in * *)
         end.
Arguments BoundedString [_].
