Require Import Structure.
Require Import System.

(** Lemmas that are needed in order to prove the main theorem *)
Lemma plus_comm : forall n m, n + m = m + n.
Proof.
intros n m; elim n; simpl in |- *; auto with arith.
intros y H; elim (plus_n_Sm m y); auto with arith.
Qed.
Lemma maxLessThan : forall a b k, max a b <= k -> a <= k.
Proof.
  intros a.
  induction a.
  - intros. apply le_0_n.
  - intros. destruct k.
    destruct a,b; inversion H.
    destruct b. simpl in H. apply H.
    simpl in H. apply le_n_S. apply IHa with (b:=b).
    apply le_S_n. apply H.
Qed.
Lemma max_comm : forall a b, max a b = max b a.
Proof.
  intros a.
  induction a.
  - simpl. destruct b;reflexivity.
  - destruct b. reflexivity.
    simpl. rewrite IHa. reflexivity.
Qed.

(** The main theorem saying that
    We have evidence for all the ilities in the hierarchy
    as long as the hierarchy is created the way we define
    (All the Leaf ilities require a proof of their requirements when instancing *)
Theorem proofIlities : forall (s : SystemType) (n : ilities), (@ilitiesProp s) n.
Proof.
  intros.
  assert (exists k, levelIlities n <= k).
  apply existsLevelIlities.
  inversion H.
  clear H.
  generalize dependent n.
  induction x.
  - intros. destruct n. apply LeafProp. apply I.
    destruct l. apply MTNonLeafProp. apply I.
    simpl in H0. rewrite plus_comm in H0. inversion H0.
  - intros. destruct n.
    + apply LeafProp. apply I.
    + induction l.
      * apply MTNonLeafProp. apply I.
      * apply NonMTNonLeafProp. apply I.
        simpl. apply IHx.
        simpl in H0. rewrite plus_comm in H0.
        apply le_S_n in H0. apply maxLessThan in H0. apply H0.
        simpl. apply IHl. destruct l. apply le_0_n.
        simpl. rewrite plus_comm. apply le_n_S.
        simpl in H0. rewrite plus_comm in H0.
        apply le_S_n in H0. rewrite max_comm in H0.
        apply maxLessThan in H0. apply H0.
Qed.