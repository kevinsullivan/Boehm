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

(** System definition now is imported here as a seprate module.**)
Require Import System.

(** CONTEXT definition now is imported here as a seprate module.**)
Require Import Context.

(** Stakeholder definition now is imported here as a seprate module.**)
Require Import Stakeholder.

Theorem aSystemisMissionEffective: MissionEffective aSystem.

Proof.
(** backwards reasoning from goal to preconditions as subgoals *)
apply mk_mission_eff.
(** assume antecedent of implication and show that consequent follows *)
intros context stakeholder.
destruct context as [referent state stage].
apply is_mission_eff_in_context; crush.
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage, stakeholder, sh.
apply is_stakeholder_mission_effective.
exact (proofOfPhysicalCapability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfCyberCapability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfHumanUsability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSpeed aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfEndurability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfManeuverability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfAccuracy aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfImpact aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfScalability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfInteroperability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.

(** ** Asserting and proving that [aSystem] [isResourceUtilization]. *)
(** This is an example of proof of a system is [ResourceUtilization]*)
Theorem aSystemisResourceUtilization: ResourceUtilization aSystem.
apply mk_resource_utilization.
intro context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (proofOfDevCost aSystem).
exact (proofOfCostInContext aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfDuration aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfKeyPersonnel aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfOtherScarceResources aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfManufacturability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSustainability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.

(** ** Asserting and proving that [aSystem] [isDependable]. *)
Theorem aSystemisDependable: Dependable aSystem.
Proof.
apply mk_dependability.
intros context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (proofOfSecurity aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSafety aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfReliability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfMaintainability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfAvailability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfSurvivability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfRobustness aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.

(** ** Asserting and proving that [aSystem] [IsFlexible]. *)
Theorem aSystemIsFlexible: Flexible aSystem.
apply mk_flexibility.
intros context.
destruct context as [referent state stage].
destruct referent, state as [internalState externalState].
destruct internalState, externalState, stage. crush.
exact (proofOfModifiability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfTailorability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
exact (proofOfAdaptability aSystem (mk_context aReferent (mk_state anInternalState anExternalState) aStage)).
Qed.

(** ** Asserting and proving that [aSystem] [isAffordable]. *)
Theorem aSystemisAffordable : Affordable aSystem.
apply mk_affordability.
(** We here provide proofs for two sub-attributes*)
(** Here we apply the proof that are already proved in module [MissionEffective]*)
apply aSystemisMissionEffective.
(** Here we apply the proof that are already proved in module [ResourceUtilization]*)
apply aSystemisResourceUtilization.
Qed.

(** ** Asserting and proving that [aSystem] [isResilient]. *)
Theorem aSystemisResilient : Resilient aSystem.
apply mk_resilient.
(** Here we prove the first sub-attribute: dependable*)
apply aSystemisDependable.
apply aSystemIsFlexible.
Qed.
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ferent.aReferent (State.mk_state State.anInternalState State.anExternalState) Stage.aStage)).
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
