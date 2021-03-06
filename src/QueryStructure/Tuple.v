Require Import List String FunctionalExtensionality Ensembles
        Common.ilist ADTNotation.StringBound Program Heading
        QueryStructure.Notations.

(* A tuple is a map from attributes to values. *)
Definition Tuple {Heading : Heading} :=
  forall (i : Attributes Heading), Domain Heading i.

(* Notations for tuple field. *)

Record Component (Heading : Attribute) :=
  { value : attrType Heading }.

Notation "id :: value" :=
  (Build_Component {| attrName := id;
                      attrType := _ |}
                   value) : Component_scope.

Bind Scope Component_scope with Component.

(* Notation-friendly tuple definition. *)

Definition BuildTuple
        (attrs : list Attribute)
        (components : ilist Component attrs)
: @Tuple (BuildHeading attrs) :=
  fun idx =>
    value (ith_Bounded _ components idx).

(* Notation for tuples built from [BuildTuple]. *)

Notation "< col1 , .. , coln >" :=
  (@BuildTuple _ (icons _ col1%Component .. (icons _ coln%Component (inil _)) ..))
  : Tuple_scope.

Definition GetAttribute
           {heading}
           (tup : @Tuple heading)
           (attr : Attributes heading)
: Domain heading attr :=
  tup attr.

Definition getHeading {Bound} (tup : @Tuple (BuildHeading Bound))
: list string := map attrName Bound.

Definition GetAttribute'
           {heading}
           (tup : @Tuple (BuildHeading heading))
           (attr : @BoundedString (map attrName heading))
: Domain (BuildHeading heading) attr :=
  tup attr.

Notation "t ! R" :=
  (GetAttribute' t%Tuple (@Build_BoundedIndex _ _ R%string _))
  : Tuple_scope.

Record IndexedTuple {heading} :=
  { tupleIndex : nat;
    indexedTuple :> @Tuple heading
  }.
