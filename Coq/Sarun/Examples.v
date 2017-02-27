Require Import Example_Car.
Require Import Structure.
Require Import ProofIlities.
Require Import System.
Require Import LeafIlitiesClass.

Definition Prop1Type : Type. Admitted.

Definition default_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop :=
  match c, p, s, st with
       | _, _, _, _ => True
  end.

Instance Prop1Instance : LeafIlities Prop1Type CarSystemType :=
{
  requirement := default_reqs
}.
Proof.
  intros.
  destruct c,p,s,st;apply I.
Qed.

Definition Prop1 : (@ilities CarSystemType) :=
Leaf Prop1Instance.

Definition Prop2Type : Type. Admitted.

Instance Prop2Instance : LeafIlities Prop2Type CarSystemType :=
{
  requirement := default_reqs
}.
Admitted.

Definition Prop2 : (@ilities CarSystemType) :=
Leaf Prop2Instance.

Definition Prop3Type : Type. Admitted.

Instance Prop3Instance : LeafIlities Prop3Type CarSystemType :=
{
  requirement := default_reqs
}.
Proof.
  intros.
  destruct c,p,s,st;apply I.
Qed.

Definition Prop3 : (@ilities CarSystemType) :=
Leaf Prop3Instance.

Definition Satisfactory : ilities :=
NonLeaf (cons Prop1 (cons Prop2 (cons Prop3 nil))).

Theorem SatisfactoryProof : ilitiesProp Satisfactory.
Proof.
  apply proofIlities.
Qed.

