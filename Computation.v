Require Import String Ensembles.
Require Import Common.

Reserved Notation "x >>= y" (at level 42, right associativity).
(*Reserved Notation "x <- y ; z" (at level 42, right associativity).
Reserved Notation "x ;; z" (at level 42, right associativity).*)
Reserved Notation "'call' f 'from' funcs [[ x ]]" (at level 35).

Delimit Scope comp_scope with comp.
Delimit Scope long_comp_scope with long_comp.

Inductive Comp : Type -> Type :=
| Return : forall A, A -> Comp A
| Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
| Pick : forall A, Ensemble A -> Comp A.

Bind Scope comp_scope with Comp.
Arguments Bind A%type B%type _%comp _.

(*Notation "x >>= y" := (Bind x%comp y%comp) : comp_scope.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp)) : comp_scope.
Notation "x ;; z" := (Bind x%comp (fun _ => z%comp)) : comp_scope.
Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick A%type (fun x => P)) : comp_scope.*)
Notation ret := Return.

Notation "x >>= y" := (Bind x%comp y%comp) : comp_scope.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp))
                           (at level 42, right associativity,
                            format "'[v' x  <-  y ; '/' z ']'") : comp_scope.
Notation "x ;; z" := (Bind x%comp (fun _ => z%comp))
                       (at level 42, right associativity,
                        format "'[v' x ;; '/' z ']'") : comp_scope.
Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick A%type (fun x => P)) : comp_scope.

Section comp.
  Definition List A B (f : A -> B) : Comp A -> Comp B
    := fun x => (x' <- x;
                 Return (f x'))%comp.

  Definition Or : Comp bool -> Comp bool -> Comp bool
    := fun c1 c2 =>
         (b1 <- c1;
          if b1
          then Return true
          else c2)%comp.

  Section computes_to.
    Inductive computes_to
    : forall A : Type, Comp A -> A -> Prop :=
    | ReturnComputes : forall A v, @computes_to A (Return v) v
    | BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                       @computes_to A comp_a comp_a_value
                       -> @computes_to B (f comp_a_value) comp_b_value
                       -> @computes_to B (Bind comp_a f) comp_b_value
    | PickComputes : forall A (P : Ensemble A) v, P v -> @computes_to A (Pick P) v.

    Theorem computes_to_inv A (c : Comp A) v
    : computes_to c v -> match c with
                           | Return _ x => fun v => v = x
                           | Bind _ _ x f => fun v => exists comp_a_value,
                                                        computes_to x comp_a_value
                                                        /\ computes_to (f comp_a_value) v
                           | Pick _ P => P
                         end v.
    Proof.
      destruct 1; eauto.
    Qed.
  End computes_to.

  Section is_computational.
    (** A [Comp] is maximally computational if it could be written without [Pick] *)
    Inductive is_computational : forall A, Comp A -> Prop :=
    | Return_is_computational : forall A (x : A), is_computational (Return x)
    | Bind_is_computational : forall A B (cA : Comp A) (f : A -> Comp B),
                                is_computational cA
                                -> (forall a,
                                      computes_to cA a -> is_computational (f a))
                                -> is_computational (Bind cA f).

    Theorem is_computational_inv A (c : Comp A)
    : is_computational c
      -> match c with
           | Return _ _ => True
           | Bind _ _ x f => is_computational x
                             /\ forall v, computes_to x v
                                          -> is_computational (f v)
           | Pick _ _ => False
         end.
    Proof.
      destruct 1; eauto.
    Qed.

    (* It's possible to extract the value from a fully detiministic computation *)
    Fixpoint is_computational_val A (c : Comp A) {struct c}
    : is_computational c -> { a | computes_to c a }.
    Proof.
      refine match c as c' return is_computational c' -> { a | computes_to c' a } with
               | Return _ v => fun _ => exist _ v _
               | Pick _ _ => fun H => match is_computational_inv H : False with end
               | Bind _ _ x f => fun H => let H' := is_computational_inv H in
                                          let x' := is_computational_val _ _ (proj1 H') in
                                          let x'' := is_computational_val _ _ (proj2 H' _ (proj2_sig x')) in
                                          exist _ (proj1_sig x'') _

             end;
      repeat match goal with
               | [ H := _ |- _ ] => clearbody H
             end;
      clear is_computational_val;
      abstract (
          destruct_head_hnf sig;
          econstructor;
          try eassumption
        ).
    Defined.

  End is_computational.

  Section monad.
    Local Ltac t :=
      split;
      intro;
      repeat match goal with
               | [ H : _ |- _ ]
                 => inversion H; clear H; subst; [];
                    repeat match goal with
                             | [ H : _ |- _ ] => apply inj_pair2 in H; subst
                           end
             end;
      repeat first [ eassumption
                   | solve [ constructor ]
                   | eapply BindComputes; (eassumption || (try eassumption; [])) ].

    Lemma bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x v
    : computes_to (Bind (Bind x f) g) v
      <-> computes_to (Bind x (fun u => Bind (f u) g)) v.
    Proof.
      t.
    Qed.

    Lemma bind_unit X Y (f : X -> Comp Y) x v
    : computes_to (Bind (Return x) f) v
      <-> computes_to (f x) v.
    Proof.
      t.
    Qed.

    Lemma unit_bind X (x : Comp X) v
    : computes_to (Bind x (@Return X)) v
      <-> computes_to x v.
    Proof.
      t.
    Qed.

    Lemma computes_under_bind X Y (f g : X -> Comp Y) x
    : (forall x v, computes_to (f x) v <-> computes_to (g x) v) ->
      (forall v, computes_to (Bind x f) v <-> computes_to (Bind x g) v).
    Proof.
      t; split_iff; eauto.
    Qed.

  End monad.

  (** The old program might be non-deterministic, and the new program
      less so.  This means we want to say that if [new] can compute to
      [v], then [old] should be able to compute to [v], too. *)
  Definition refine {A} (old new : Comp A)
    := forall v, computes_to new v -> computes_to old v.

  (** Define a symmetrized version of [refine] for ease of rewriting *)
  Definition refineEquiv {A} (old new : Comp A)
    := refine old new /\ refine new old.

  Global Instance refine_PreOrder A
  : PreOrder (@refine A).
  Proof.
    split; compute in *; eauto.
  Qed.

  Global Instance refineEquiv_Equivalence A
  : Equivalence (@refineEquiv A).
  Proof.
    repeat (split || intro); compute in *; split_and; eauto.
  Qed.

  Section monad_refine.
    Lemma refineEquiv_bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x
    : refineEquiv (Bind (Bind x f) g)
                  (Bind x (fun u => Bind (f u) g)).
    Proof.
      split; intro; apply bind_bind.
    Qed.

    Lemma refineEquiv_bind_unit X Y (f : X -> Comp Y) x
    : refineEquiv (Bind (Return x) f)
                  (f x).
    Proof.
      split; intro; apply bind_unit.
    Qed.

    Lemma refineEquiv_unit_bind X (x : Comp X)
    : refineEquiv (Bind x (@Return X))
                  x.
    Proof.
      split; intro; apply unit_bind.
    Qed.

    Lemma refineEquiv_under_bind X Y (f g : X -> Comp Y) x
          (eqv_f_g : forall x, refineEquiv (f x) (g x))
    : refineEquiv (Bind x f)
                  (Bind x g).
      Proof.
        split; unfold refine; intros; eapply computes_under_bind;
        eauto; split; eapply eqv_f_g.
      Qed.

  End monad_refine.
End comp.

Hint Constructors computes_to.

Ltac inversion_by rule :=
  progress repeat first [ progress destruct_ex
                        | progress split_and
                        | apply_in_hyp_no_cbv_match rule ].

Add Parametric Relation A : (Comp A) (@refine A)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refine_rel.

Add Parametric Relation A : (Comp A) (@refineEquiv A)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineEquiv_rel.

Add Parametric Morphism A : (@refine A)
  with signature
  (@refineEquiv A) --> (@refineEquiv A) ++> impl
    as refine_refine.
Proof.
  unfold impl.
  intros.
  repeat (eapply_hyp || etransitivity).
Qed.

Add Parametric Morphism A B : (@Bind A B)
  with signature
  (@refine A)
    ==> (pointwise_relation _ (@refine B))
    ==> (@refine B)
    as refine_bind.
Proof.
  intros.
  unfold pointwise_relation, refine in *.
  intros.
  inversion_by computes_to_inv.
  eauto.
Qed.

Add Parametric Morphism A B : (@Bind A B)
  with signature
  (@refineEquiv A)
    ==> (pointwise_relation _ (@refineEquiv B))
    ==> (@refineEquiv B)
    as refineEquiv_bind.
Proof.
  intros.
  unfold pointwise_relation, refineEquiv, refine in *.
  split_and.
  split; intros;
  inversion_by computes_to_inv;
  eauto.
Qed.

Add Parametric Morphism A B : (@Bind A B)
  with signature
  (@refineEquiv A)
    ==> (pointwise_relation _ (@refineEquiv B))
    ==> (@refine B)
    as refineEquiv_refine_bind.
Proof.
  intros.
  refine (proj1 (_ : refineEquiv _ _)).
  setoid_rewrite_hyp.
  reflexivity.
Qed.

Section general_refine_lemmas.

  Lemma refine_is_computational A
  : forall (c : Comp A) (CompC : is_computational c),
      refine c (ret ((proj1_sig (is_computational_val CompC)))).
  Proof.
    unfold refine; intros; rewrite (computes_to_inv H);
    apply (proj2_sig _).
  Qed.

  Lemma refine_pick_pair A B (PA : A -> Prop) (PB : B -> Prop)
  : refine { x : A * B | PA (fst x) /\ PB (snd x) }%comp
           (a <- { a : A | PA a };
            b <- { b : B | PB b };
            ret (a, b))%comp.
  Proof.
    intros (a, b) H.
    repeat match goal with
             | _ => constructor; tauto
             | _ => progress destruct_ex
             | _ => progress intuition
             | [ H : (_, _) = (_, _) |- _ ] => inversion_clear H
             | [ H : _ |- _ ] => apply computes_to_inv in H
           end.
  Qed.
End general_refine_lemmas.

Create HintDb refine_monad discriminated.

(*Hint Rewrite refine_bind_bind refine_bind_unit refine_unit_bind : refine_monad.
Hint Rewrite <- refine_bind_bind' refine_bind_unit' refine_unit_bind' : refine_monad.*)
Hint Rewrite refineEquiv_bind_bind refineEquiv_bind_unit refineEquiv_unit_bind : refine_monad.
(* Ideally we would throw refineEquiv_under_bind in here as well, but it gets stuck *)


Ltac interleave_autorewrite_refine_monad_with tac :=
  repeat first [ reflexivity
               | progress tac
               | progress autorewrite with refine_monad
               (*| rewrite refine_bind_bind'; progress tac
               | rewrite refine_bind_unit'; progress tac
               | rewrite refine_unit_bind'; progress tac
               | rewrite <- refine_bind_bind; progress tac
               | rewrite <- refine_bind_unit; progress tac
               | rewrite <- refine_unit_bind; progress tac ]*)
               | rewrite <- !refineEquiv_bind_bind; progress tac
               | rewrite <- !refineEquiv_bind_unit; progress tac
               | rewrite <- !refineEquiv_unit_bind; progress tac
               (*| rewrite <- !refineEquiv_under_bind; progress tac *)].
