Require Import List.
Require Import System.
Require Import LeafIlitiesClass.

Inductive ilities {s : SystemType} : Type :=
  | Leaf {A : Type}: LeafIlities A s -> ilities
  | NonLeaf : list ilities -> ilities.

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

Definition blackHole : Type. Admitted.

Instance blackHoleInstance {s : SystemType} : LeafIlities blackHole s :=
{
  requirement := fun _ _ _ _ => False
}.
Admitted.

Definition blackHoleLeaf {s : SystemType} : (@ilities s) := Leaf (@blackHoleInstance s).

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

Inductive ilitiesProp {s : SystemType} (n : (@ilities s)) : Prop :=
| LeafProp : isLeaf n -> ilitiesProp n
| MTNonLeafProp : isMTNonLeaf n -> ilitiesProp n
| NonMTNonLeafProp : isNonMTNonLeaf n -> ilitiesProp (extractHead n) -> ilitiesProp (removeHead n) -> ilitiesProp n.
