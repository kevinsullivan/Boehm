(** * Examples to prove that a system has quality attributes. *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(** 
Import [CpdtTactics] moduel to use [crush] tactic. 
*)
Require Import CpdtTactics.
Require Import MissionEffective.
Require Import ResourceUtilization.
Require Import Dependability.
Require Import Flexibility.
Require Import Affordability.
Require Import Resilient.
Require Import System.
Require Import Context.
Require Import Stakeholder.

(*********************************************************************)
(*********************************************************************)
(** ** Asserting and proving that [aSystem] [isMissionEffective]. *)

(** 
We now formally assert the validity of the proposition that [aSystem] [isMissionEffective].
That is, we assert that we can produce a proof/certificate for this claim. Coq shifts into
proof mode, and we execute a sequence of proof-term-building "proof tactics" to construct
such a proof. The proof in this case is by nested case analysis, first on the two [Contexts]
that we have posited, and then for each (and there is only one) [Stakeholder]. Clearly this
is a somewhat tedious but ultimately very simple proof. It could be discharged with less
prose, but we present an expanded proof script here to make clear where we apply each
proof constructor to a proof goal. Doing this reduces the goal to a set of subgoals, namely
subgoals of providing proofs of the propositions needed as inputs to the proof constructors. 
Once the requires arguments are provided, application of the proof constructor "runs" and 
generates the desired proof term. A "Qed" tells Coq to register the proof as a defined term
in the proof system environment for future reference.
*)

Theorem aSystemisMissionEffective: MissionEffective.MissionEffective System.aSystem.
Proof.
(** backwards reasoning from goal to preconditions as subgoals *)
apply MissionEffective.mk_mission_eff.
(** assume antecedent of implication and show that consequent follows *)
intros context stakeholder.
destruct context as [referent state stage].
apply MissionEffective.is_mission_eff_in_context; crush.
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage, stakeholder, sh.
apply MissionEffective.is_stakeholder_mission_effective.
exact (MissionEffective.proofOfPhysicalCapability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfCyberCapability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfHumanUsability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfSpeed System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfEndurability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfManeuverability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfAccuracy System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfImpact System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfScalability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (MissionEffective.proofOfInteroperability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
Qed.

(*********************************************************************)
(*********************************************************************)

(** ** Asserting and proving that [aSystem] [isResourceUtilization]. *)
(** This is an example of proof of a system is [ResourceUtilization]*)
Theorem aSystemisResourceUtilization: ResourceUtilization.ResourceUtilization System.aSystem.
apply ResourceUtilization.mk_resource_utilization.
intro context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (ResourceUtilization.proofOfDevCost System.aSystem).
exact (ResourceUtilization.proofOfCostInContext System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (ResourceUtilization.proofOfDuration System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (ResourceUtilization.proofOfKeyPersonnel System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (ResourceUtilization.proofOfOtherScarceResources System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (ResourceUtilization.proofOfManufacturability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (ResourceUtilization.proofOfSustainability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
Qed.

(*********************************************************************)
(*********************************************************************)
(** ** Asserting and proving that [aSystem] [isDependable]. *)
Theorem aSystemisDependable: Dependable.Dependable System.aSystem.
Proof.
apply Dependable.mk_dependability.
intros context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (Dependable.proofOfSecurity System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Dependable.proofOfSafety System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Dependable.proofOfReliability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Dependable.proofOfMaintainability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Dependable.proofOfAvailability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Dependable.proofOfSurvivability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Dependable.proofOfRobustness System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
Qed.


(*********************************************************************)
(*********************************************************************)
(** ** Asserting and proving that [aSystem] [IsFlexible]. *)
Theorem aSystemIsFlexible: Flexible.Flexible System.aSystem.
apply Flexible.mk_flexibility.
intros context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (Flexible.proofOfModifiability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Flexible.proofOfTailorability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
exact (Flexible.proofOfAdaptability System.aSystem (Context.mk_context Referent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
Qed.


(*********************************************************************)
(*********************************************************************)
(** ** Asserting and proving that [aSystem] [isAffordable]. *)
Theorem aSystemisAffordable : Affordable.Affordable System.aSystem.
apply Affordable.mk_affordability.
(** We here provide proofs for two sub-attributes*)
(** Here we apply the proof that are already proved in module [MissionEffective]*)
apply aSystemisMissionEffective.
(** Here we apply the proof that are already proved in module [ResourceUtilization]*)
apply aSystemisResourceUtilization.
Qed.


(*********************************************************************)
(*********************************************************************)
(** ** Asserting and proving that [aSystem] [isResilient]. *)
Theorem aSystemisResilient : Resilient.Resilient System.aSystem.
apply Resilient.mk_resilient.
(** Here we prove the first sub-attribute: dependable*)
apply aSystemisDependable.
apply aSystemIsFlexible.
Qed.
