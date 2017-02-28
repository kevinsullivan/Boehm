Require Import CarSystem.
Require Import Structure.
Require Import ProofIlities.
Require Import System.
Require Import LeafIlitiesClass.
Require Import List.
Import ListNotations.

(** This file generate a small hierarchy with 4 ilities (The main ilities that depends on the other 3)

                  Satisfactory
                /      |      \
             Prop1   Prop2   Prop3
*)

(** default requirement *)
Definition default_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop :=
  match c, p, s, st with
       | _, _, _, _ => True
  end.

(** Prop1 *)
Definition Prop1Type : Type. Admitted. (** An identity type for constructing an instance of LeafIlities class *)
Instance Prop1Instance : LeafIlities Prop1Type CarSystemType := (** creating an instance of LeafIlities class *)
{
  requirement := default_reqs (** requirement of this ilities *)
}.
Proof. (** Proof is needed when instancing *)
  intros.
  destruct c,p,s,st;apply I.
Qed.
Definition Prop1 : (@ilities CarSystemType) := (** Creating a Leaf ilities Prop1 *)
Leaf Prop1Instance.

(** Prop2 *)
Definition Prop2Type : Type. Admitted. (** An identity type for constructing an instance of LeafIlities class *)
Instance Prop2Instance : LeafIlities Prop2Type CarSystemType := (** creating an instance of LeafIlities class *)
{
  requirement := default_reqs (** requirement of this ilities *)
}.
Admitted. (** Proof is needed when instancing, but if we don't have a proof yet, we can 'Admit' it for now.
              Comeback to fill this when we have a proof *)
Definition Prop2 : (@ilities CarSystemType) := (** Creating a Leaf ilities Prop2 *)
Leaf Prop2Instance.

(** Prop3 *)
Definition Prop3Type : Type. Admitted. (** An identity type for constructing an instance of LeafIlities class *)
Instance Prop3Instance : LeafIlities Prop3Type CarSystemType := (** creating an instance of LeafIlities class *)
{
  requirement := default_reqs (** requirement of this ilities *)
}.
Proof. (** Proof is needed when instancing *)
  intros.
  destruct c,p,s,st;apply I.
Qed.
Definition Prop3 : (@ilities CarSystemType) := (** Creating a Leaf ilities Prop3 *)
Leaf Prop3Instance.

(** Satisfactory *)
Definition Satisfactory : ilities := (** Creating a NonLeaf ilities Satisfactory, that depends on Prop1, Prop2, and Prop3 *)
NonLeaf [Prop1 ; Prop2 ; Prop3 ].

(** By the main theorem that we have in ProofIlities.v, we have evidence of Satisfactory prop *)
Theorem SatisfactoryProof : ilitiesProp Satisfactory.
Proof.
  apply proofIlities.
Qed.

(** If we want to change the structure of our hierarchy by creating a middle ilities that depends on prop1 and prop2

                  Satisfactory
                 /            \
             middleman       Prop3
             /       \
          Prop1     Prop2

    We can simply do this *)

Definition Satisfactory' : ilities := (** Creating a NonLeaf ilities Satisfactory, that depends on Prop1, Prop2, and Prop3 *)
NonLeaf [(NonLeaf [Prop1;Prop2]); Prop3].

(** And without changing anything, we can have evidence of Satisfactory' prop *)
Theorem SatisfactoryProof' : ilitiesProp Satisfactory'.
Proof.
  apply proofIlities.
Qed.
