Require Import List.
Require Import System.
Require Import LeafIlitiesClass.
Import ListNotations.

(** This is the main inductive type for creating a hierarchy of ilities
    There are two type of ilities
    1. Leaf - a low-level ilities, is created by an instance of typeclass LeafIlities.
                                   See LeafIlitiesClass.v for more details
    2. NonLeaf - a higher-level ilities, is created by specifying a list of lower-level ilities that it depends on
                                         This represent means-ends relatioship between ilities
*)
Inductive ilities {s : SystemType} : Type :=
  | Leaf {A : Type}: LeafIlities A s -> ilities
  | NonLeaf : list ilities -> ilities.

(** Functions to represent whether an ilities is a Leaf, a NonLeaf with empty listm or a NonLeaf with non-empty list *)
Definition isLeaf {s : SystemType} (n : (@ilities s)) : Prop :=
  match n with
    | Leaf _ => True
    | NonLeaf _ => False
  end.
Definition isMTNonLeaf {s : SystemType} (n : (@ilities s)) : Prop :=
  match n with
    | Leaf _ => False
    | NonLeaf nil => True
    | NonLeaf _ => False
  end.
Definition isNonMTNonLeaf {s : SystemType} (n : (@ilities s)) : Prop :=
  match n with
    | Leaf _ => False
    | NonLeaf nil => False
    | NonLeaf _ => True
  end.

(** This is just a stub return value
    We need this because Coq require all functions to be total *)
Definition blackHole : Type. Admitted.
Instance blackHoleInstance {s : SystemType} : LeafIlities blackHole s :=
{
  requirement := fun _ _ _ _ => False
}.
Admitted.
Definition blackHoleLeaf {s : SystemType} : (@ilities s) := Leaf (@blackHoleInstance s).

(** Functions to access head and tail of the list inside a NonLeaf *)
Definition extractHead {s : SystemType} (n : (@ilities s)) : ilities :=
  match n with
    | Leaf _ => blackHoleLeaf
    | NonLeaf nil => blackHoleLeaf
    | NonLeaf (cons h t) => h
  end.
Definition removeHead {s : SystemType} (n : (@ilities s)) : ilities :=
  match n with
    | Leaf _ => blackHoleLeaf
    | NonLeaf nil => blackHoleLeaf
    | NonLeaf (cons h t) => NonLeaf t
  end.

(** Function to determine the level of a ilities, and functions related to it
    These are just proof in ProofIlities.v; this is no other meaning *)
Fixpoint levelIlities {s : SystemType} (n : (@ilities s)) : nat :=
  match n with
    | Leaf _ => 0
    | NonLeaf nil => 0
    | NonLeaf l => (fold_right max 0 (map levelIlities l)) + 1
  end.
Theorem existsMaxFunction : forall (a b : nat), exists k, k = max a b.
Proof.
  intros a.
  induction a.
  - intros. exists b. reflexivity.
  - destruct b.
    + exists (S a). reflexivity.
    + simpl. assert (exists k : nat, k = Nat.max a b).
      apply IHa. inversion H. rewrite <- H0.
      exists (S x). reflexivity.
Qed.
Theorem existsLevelIlities : forall (s : SystemType) (n : ilities), exists k, (@levelIlities s) n <= k.
Proof.
  intros.
  induction n.
  - exists 0. reflexivity.
  - induction l.
    + exists 0. reflexivity.
    + simpl. inversion IHl.
      assert (exists k, k = max (levelIlities a) (fold_right Nat.max 0 (map levelIlities l))).
      apply existsMaxFunction. inversion H0.
      exists (x0 + 1). rewrite <- H1. reflexivity.
Qed.

(** Main propositional logic for representing means-ends hierarchy of ilities
    1. If an ilities is a Leaf, then we do not need to prove anything because a proof is already needed
                                when we create an instance of typeclass LeafIlities.
                                See LeafIlitiesClass.v for more details
    2. If an ilities is a NonLeaf with empty list, then we do not need to do anything 
                                                   because it does not depend on anything
    3. If an ilities is a NonLeaf with non-empty list, then we need evidence for all of it dependents
                                                       in order to construct an evidence for this ilities
                                                       Note that this is done by extracting head and tail of the list,
                                                                 get evidence of the head and then recursively
                                                                 get evidences of the tail *)
Inductive ilitiesProp {s : SystemType} (n : (@ilities s)) : Prop :=
| LeafProp : isLeaf n -> ilitiesProp n
| MTNonLeafProp : isMTNonLeaf n -> ilitiesProp n
| NonMTNonLeafProp : isNonMTNonLeaf n -> 
                     ilitiesProp (extractHead n) ->
                     ilitiesProp (removeHead n) -> ilitiesProp n.
