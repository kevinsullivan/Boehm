(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March 23, 2015
*)

Require Import CpdtTactics.

(** ** SYSTEM **)

(** 
We can't concretely specify non-functional properties absent a model of the system.
We introduce a data type of system models, currently "stubbed out" as having only
one system model, [aSystem], without any further elaboration.
*)
Inductive System := aSystem.

(** ** CONTEXT *)

(**
Nor can we concretely specify system properties absent a model of its context. We
thus similarly introduce a data type of context models, expanded into multiple dimensions, 
including Referent, Stage and Stage. State can be expanded into two dimensions,
including InternalState and ExternalState, where both of them are currently "stubbed out" as having only
one concrete value, [anInternalStatea] and [anExternalState] respectively, without any further elaboration.
*)

Inductive Referent := aReferent.

Inductive InternalState := anInternalState.
Inductive ExternalState := anExternalState.
Inductive State := mk_state: InternalState -> ExternalState -> State.

Inductive Stage := aStage.

Inductive Context := mk_context: Referent -> State -> Stage -> Context.

(** ** STAKEHOLDERS **)

(** 
An important class of "subjective" properties concerns stakeholder satisfaction or value.
We thus introduce a data type of "stakeholders in a given system, [s]." The [Stakeholder]
data type is thus parameterized by a given system model of concern.
*)

Inductive Stakeholder (s: System) := aStakeholder.

(** ** SYSTEM PROPERTIES AND RELATIONS *)

(**
We now turn from data types to properties of systems and relations involving them. 
We represent a property as a family of propositions, parameterized by a [System].
We represent a context-dependent "system property" as a binary relation over [System]
and [Context] pairs. We represent a subjective, context-dependent "system property"
as a ternary relation over [System], [Context], [Stakeholder] triples. In all cases, for
purposes of producing a simplest possible example, for each property and relation
we define a proof constructor that in effect axiomatically provides a proof of the given
property or relation for all possible values of [System], [Context], [Stakeholder]. 
*)

(** ** Some basic objective but context-dependent system properties *)

(**
Here we define [PhysicalCapability], [CyberCapability], and other "ilities" as
(objective) properties of specific [Systems] in specific [Contexts]. For each 
property we provide a proof constructor that returns a proof of validity of a
proposition that that property holds "axiomatically" -- for any [System] and 
any [Context]. Any genuinely meaningful use of these techniques would 
require more constrained forms of evidence validate such propositions.
Formally speaking we are defining these "ilities" not as "unary properties" 
(e.g., of [Systems] along) but as "binary relations", in this case relations 
over [System]/[Context] pairs. Here these relations are trivially defined to
hold for all such pairs. In real systems, that might not always be the case,
and even if it were, it would in general be harder to prove! 
*)

Inductive hasRequiredPhysicalCapability: System -> Context -> Prop := 
  proofOfPhysicalCapability: forall (s: System), forall (c: Context), 
    hasRequiredPhysicalCapability s c.

Inductive hasRequiredCyberCapability: System -> Context -> Prop := 
  proofOfCyberCapability: forall (s: System), forall (c: Context), 
    hasRequiredCyberCapability s c.

Inductive hasRequiredHumanUsability: System -> Context ->  Prop := 
  proofOfHumanUsability: forall (s: System), forall (c: Context), 
    hasRequiredHumanUsability s c.

Inductive hasRequiredSpeed: System -> Context -> Prop := 
  proofOfSpeed: forall (s: System), forall (c: Context), 
    hasRequiredSpeed s c.

Inductive hasRequiredEndurability: System -> Context -> Prop := 
  proofOfEndurability: forall (s: System), forall (c: Context), 
    hasRequiredEndurability s c.

Inductive hasRequiredManeuverability: System -> Context -> Prop := 
  proofOfManeuverability: forall (s: System), forall (c: Context), 
    hasRequiredManeuverability s c.

Inductive hasRequiredAccuracy: System -> Context -> Prop := 
  proofOfAccuracy: forall (s: System), forall (c: Context), 
    hasRequiredAccuracy s c.

Inductive hasRequiredImpact: System -> Context -> Prop := 
  proofOfImpact: forall (s: System), forall (c: Context), 
    hasRequiredImpact s c.

Inductive hasRequiredScalability: System -> Context -> Prop := 
  proofOfScalability: forall (s: System), forall (c: Context), 
    hasRequiredScalability s c.

Inductive hasRequiredVersatility: System -> Context -> Prop := 
  proofOfVersatility: forall (s: System), forall (c: Context), 
    hasRequiredVersatility s c.

Inductive hasRequiredInteroperability: System -> Context -> Prop := 
  proofOfInteroperability: forall (s: System), forall (c: Context), 
    hasRequiredInteroperability s c.

(**
One potentially important insight that "jumps out" even from this simple 
analysis is that we should not think of "ilities" such as [PhysicalCapability]
as a system properties but as relations over systems and other entities, in
this case, [Contexts].
*)

(** ** Mission-effectiveness as a subjective system property *)

(**
We now formaliz a class of propositions of the form "System s is Mission Effective."
However, we do this in such a way that proof of such a proposition will require a set
of proofs proof that [s] is "subjectively mission effective" from the perspective of each,
and for all [Contexts] in which the system is specified to operate. The "property" of
being mission effective is thus seen to involve, in this formulation, a ternary relation: 
on [Systems], [Contexts], and [Stakeholders]. 

We define the [isMissionEffective] property in three steps:
   - the ternary relation of a system being subjectively effective for a stakeholder in a context
  - the binary relation of being effective (for all stakeholders) in a context
  - the unary property of being effective (for all stakeholders, in all contexts)
*)

(**
This construct defines a ternary relation, an instance of which we interpret as a proposition
that a given [System], [s], in a given [Context], c, is subjectively "mission effective" for a
given [Stakeholder], sh, and that this is provably the case if and only if the required set of
arguments can be provided to the proof constructor, [is_stakeholder_mission_effective]. In
particular, one must provide proofs of all of the constituent propositions, e.g., the system
"has the required physical capability," etc. If the constructor is applied to aguments  of the
required "proof" types, then it will return a proof of stakeholder mission effectiveness for the
given [System] in the given [Context] for the given [Stakeholder].
*)

Inductive Is_stakeholder_effective_in_context (s: System) (sh: Stakeholder s) (c: Context): Prop :=
   is_stakeholder_mission_effective: 
      hasRequiredPhysicalCapability s c -> hasRequiredCyberCapability s c -> 
      hasRequiredHumanUsability s c -> hasRequiredSpeed s c -> hasRequiredEndurability s c -> 
      hasRequiredManeuverability s c -> hasRequiredAccuracy s c -> hasRequiredImpact s c -> 
      hasRequiredScalability s c -> hasRequiredInteroperability s c -> 
          Is_stakeholder_effective_in_context s sh c.

(**
We now express the notion that a [System] is effective in a given [Context], where
constructing a proof that this relation holds requires as input only a proof of the 
proposition that the [System] is subjectively mission effective for all stakeholders
in the given [Context]. 
*)

Inductive MissionEffectiveInContext (s: System) (c: Context): Prop := 
  is_mission_eff_in_context: 
    (forall sh: Stakeholder s, Is_stakeholder_effective_in_context s sh c) -> 
        MissionEffectiveInContext s c.

(**
Finally we can formalize the property of a [System] being mission effective, where a
proof of this property requires as a input a proof that, for all [Contexts], the system is
mission effective (implicitly for all [Stakeholders]) in those [Contexts]. 
*)
Inductive MissionEffective (s: System): Prop := 
  mk_mission_eff: 
    (forall c: Context, forall sh: Stakeholder s, MissionEffectiveInContext s c) -> 
        MissionEffective s.

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

(** ** RESOURCE UTILIZATION **)
(** ** The basic system properties for [ResourceUtilization]*)
(**
We define two types of cost: 1) cost in development phase, and 2) cost of running a system in 
different contexts. The development cost is not related to context, but the cost in running time does.
*)

Inductive CostInDev: System -> Prop := 
    proofOfDevCost: forall (s: System), CostInDev s.

Inductive CostInRunning: System -> Context -> Prop := 
  proofOfCostInContext: forall (s: System), forall (c: Context), CostInRunning s c.

Inductive Duration: System -> Context -> Prop := 
  proofOfDuration: forall (s: System), forall (c: Context), Duration s c.

Inductive KeyPersonnel: System -> Context -> Prop := 
  proofOfKeyPersonnel: forall (s: System), forall (c: Context), KeyPersonnel s c.

Inductive OtherScarceResources: System -> Context -> Prop := 
  proofOfOtherScarceResources: forall (s: System), forall (c: Context), OtherScarceResources s c.

Inductive Manufacturability: System -> Context -> Prop := 
  proofOfManufacturability: forall (s: System), forall (c: Context), Manufacturability s c.

Inductive Sustainability: System -> Context -> Prop := 
  proofOfSustainability: forall (s: System), forall (c: Context), Sustainability s c.

(**
ResouceUtilization is not related to Stakeholder.
We define the [ResourceUtilization] property in two steps:
  - the binary relation of the atrribute [ResourceUtilization]  in a context
  - the unary property of being [ResourceUtilization]
*)
Inductive ResourceUtilization_In_Context (s: System) (c: Context): Prop :=
    mk_resource_utilization_in_context: CostInDev s -> CostInRunning s c -> 
                        Duration s c-> KeyPersonnel s c ->
                        OtherScarceResources s c -> Manufacturability s c ->
                        Sustainability s c -> ResourceUtilization_In_Context s c.

Inductive ResourceUtilization (s: System): Prop :=
    mk_resource_utilization: 
      (forall c: Context, ResourceUtilization_In_Context s c) -> ResourceUtilization s.
(**
We now formally assert the validity of the proposition that [aSystemisResourceUtilization].
*)
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

(** ** DEPENDABILITY**)
(** ** Some basic objective but context-dependent system attibutes for [Dependability]*)
(**
For each attribute we provide a proof constructor that returns a proof for the proposition. 
*)
Inductive Security: System -> Context -> Prop := 
  proofOfSecurity: forall (s: System), forall (c: Context), Security s c.

Inductive Safety: System -> Context -> Prop := 
  proofOfSafety: forall (s: System), forall (c: Context), Safety s c.

Inductive Reliability: System -> Context -> Prop := 
  proofOfReliability: forall (s: System), forall (c: Context), Reliability s c.

Inductive Maintainability: System -> Context -> Prop := 
  proofOfMaintainability: forall (s: System), forall (c: Context), Maintainability s c.

Inductive Availability: System -> Context -> Prop := 
  proofOfAvailability: forall (s: System), forall (c: Context), Availability s c.

Inductive Survivability: System -> Context -> Prop := 
  proofOfSurvivability: forall (s: System), forall (c: Context), Survivability s c.

Inductive Robustness: System -> Context -> Prop := 
  proofOfRobustness: forall (s: System), forall (c: Context), Robustness s c.

(**
Here we define [Dependable] in two steps as earlier.
*)
Inductive Dependable_In_Context (s: System) (c: Context): Prop :=
    mk_dependability_in_context: Security s c -> Safety s c -> Reliability s c ->
                  Maintainability s c -> Availability s c -> Survivability s c ->
                   Robustness s c -> Dependable_In_Context s c.

Inductive Dependable (s: System): Prop :=
    mk_dependability:
      (forall c:Context, Dependable_In_Context s c) -> Dependable s.
(**
Here we assert the validity of the proposition that aSystem is Dependable.
*)
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

(** ** FLEXIBILITY**)
(**
We first define the basic context-dependent system attributes for [Flexibility].
*)
Inductive Modifiability: System -> Context -> Prop := 
  proofOfModifiability: forall (s: System), forall (c: Context), Modifiability s c.

Inductive Tailorability: System -> Context -> Prop := 
  proofOfTailorability: forall (s: System), forall (c: Context), Tailorability s c.

Inductive Adaptability: System -> Context -> Prop := 
  proofOfAdaptability: forall (s: System), forall (c: Context), Adaptability s c.

(**
As we did before, we define [aSystem is Flexible] in two steps:
  - a system is flexible in a context.
  - a system is universally flexible.
*)
Inductive Flexible_In_Context (s: System) (c: Context) : Prop :=
    mk_flexibility_in_context: Modifiability s c -> Tailorability s c -> 
        Adaptability s c -> Flexible_In_Context s c.

Inductive Flexible (s: System) : Prop :=
    mk_flexibility: 
        (forall c: Context, Flexible_In_Context s c) -> Flexible s.

(**
We assert the validity of the proposition that [a system is Flexible].
*)
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

(** ** AFFORDABLE**)
(**
[Affordable] is a composite attribute of [MissionEffective] and [ResourceUtilization].
A system is [Affordable] only if all sub-attributes are achieved in any [context] for any [stakeholder].
*)
Inductive Affordable (s: System): Prop :=
    mk_affordability: MissionEffective s -> ResourceUtilization s -> Affordable s.

(**
We assert a system is [affordable] here.
*)
Theorem aSystemisAffordable : Affordable aSystem.
apply mk_affordability.
(** We here provide proofs for two sub-attributes*)
(** Here is the proof for first sub-attribute: [MissionEffective]*)
apply aSystemisMissionEffective.
(** We here prove second sub-attribute: [ResourceUtilization]*)
apply aSystemisResourceUtilization.
Qed.

(** ** RESILIENT**)
(**
Here we define [Resilient] as another composite attribute.
A system is resilient only if it is dependable and flexible.
*)
Inductive Resilient (s: System): Prop :=
  mk_resilient: Dependable s -> Flexible s -> Resilient s.

Theorem aSystemisResilient : Resilient aSystem.
apply mk_resilient.
(** Here we prove the first sub-attribute: dependable*)
apply aSystemisDependable.
apply aSystemIsFlexible.
Qed.