Require Export System.


(** Mission Effective *)
(**
In the following definition, [MissionEffective] is parameterized by three typeclasses,
[System], [Stakeholder], and [Context], a system, sys, of type [System], and sevaral ternary
relations over [System], [Context], and/or [Stakeholder].
Those ternary relations are associated with its sub-attributes. For example, physicalCapability is a ternary relation,
which is to say, a set of triples, (s, sh, c), between a system, s, a stakeholder, sh, and a context, c,
that we expect to hold (for the proposition to be provable, iff system s satisfies its mission effective
requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [MissionEffective] for all [Contexts], the system is
mission effective implicitly for all [Stakeholders] in those [Contexts], only if all the requirements of the subattributes
are satisfied.
 *)
Inductive Accurate  (sys: System) : Prop :=
  satisfiesAccuracyRequirement:
    (exists accurate: System -> Prop, accurate sys) -> Accurate sys.

Inductive PhysicalCapable (sys: System) : Prop :=
  satisfiesPhysicalCapabilityRequirement:
    (exists physicalCapable: System -> Prop, physicalCapable sys) -> PhysicalCapable sys.

Inductive CyberCapable (sys: System) : Prop :=
  satisfiesCyberCapabilityRequirement:
    (exists cyberCapable: System -> Prop, cyberCapable sys) -> CyberCapable sys.

Inductive HumanUsable (sys: System) : Prop :=
  satisfiesHumanUsabilityRequirement:
    (exists humanUsable: System -> Prop, humanUsable sys) -> HumanUsable sys.

Inductive Speed (sys: System) : Prop :=
  satisfiesSpeedRequirement:
    (exists speed: System -> Prop, speed sys) -> Speed sys.

Inductive Endurable (sys: System) : Prop :=
  satisfiesEndurabilityRequirement:
    (exists endurable: System -> Prop, endurable sys) -> Endurable sys.

Inductive Maneuverable (sys: System) : Prop :=
  satisfiesManeuverabilityRequirement:
    (exists maneuverable: System -> Prop, maneuverable sys) -> Maneuverable sys.

Inductive Impactful (sys: System) : Prop :=
  satisfiesImpactRequirement:
    (exists impactful: System -> Prop, impactful sys) -> Impactful sys.

Inductive Scalable (sys: System) : Prop :=
  satisfiesScalabilityRequirement:
    (exists scalable: System -> Prop, scalable sys) -> Scalable sys.

Inductive Versatile (sys: System) : Prop :=
  satisfiesVersatilityRequirement:
    (exists versatile: System -> Prop, versatile sys) -> Versatile sys.

Inductive Interoperable (sys: System) : Prop :=
  satisfiesInteroperabilityRequirement:
    (exists interoperable: System -> Prop, interoperable sys) -> Interoperable sys.

Inductive MissionEffective (sys: System): Prop :=
  isMissionEffective:
    PhysicalCapable sys ->
    CyberCapable sys ->
    HumanUsable sys ->
    Speed sys ->
    Endurable sys ->
    Maneuverable sys ->
    Accurate sys ->
    Impactful sys ->
    Scalable sys ->
    Versatile sys ->
    Interoperable sys ->
    MissionEffective sys.

(** Efficient *)
(**
[Efficient] is parameterized by a [System] type, a [Context] type,
an instance of type [System], and sevaral binary relations over [System] and [Context]
representing the relationship between the given [System] set, [Context] set, and some
constituent attribute. The constituent attributes of [Efficiency] are
the things it uses efficiently and whether it can be produced and maintained efficiently.
(Note: We have soon see cause to split these up - they aren't really very similar)

The constituent attributes are given by binary relations represent the given system type's ability to satisfy
the specified requirement in the given context.

Informally, in English:
A system [sys] belonging to the set of systems [System] is deemed [Efficient] given the set of contexts [Context]
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
 *)

Inductive Cost (sys: System) : Prop :=
  satisfiesCostRequirement:
    (exists cost: System -> Prop, cost sys) -> Cost sys.

Inductive Duration (sys: System) : Prop :=
  satisfiesDurationRequirement:
    (exists duration: System -> Prop, duration sys) -> Duration sys.

Inductive KeyPersonnel (sys: System) : Prop :=
  satisfiesKeyPersonnelRequirement:
    (exists key_personnel: System -> Prop, key_personnel sys) -> KeyPersonnel sys.

Inductive OtherScarceResources (sys: System) : Prop :=
  satisfiesOtherResourcesRequirement:
    (exists otherResources: System -> Prop, otherResources sys) -> OtherScarceResources sys.

Inductive Manufacturable (sys: System) : Prop :=
  satisfiesManufacturabilityRequirement:
    (exists manufacturable: System -> Prop, manufacturable sys) -> Manufacturable sys.

Inductive Sustainable (sys: System) : Prop :=
  satisfiesSustainabilityRequirement:
    (exists sustainable: System -> Prop, sustainable sys) -> Sustainable sys.

Inductive Efficient (sys: System) : Prop :=
  satisfiesEfficiencyPrerequisites:
    Cost sys ->
    Duration sys ->
    KeyPersonnel sys ->
    OtherScarceResources sys ->
    Manufacturable sys ->
    Sustainable sys ->
    Efficient sys.


(** Affordable *)
(**
[Affordability] is a composite attribute of [MissionEffective] and [Efficient].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [Efficient].

Informally,
A system [sys] belonging to the set of systems [System] is deemed [Affordable] for all stakeholders
in set [Stakeholder] given the set of phases and contexts [Context] and [Phase] if and only if all the
requirements of its sub-attributes ([MissionEffective], and [Efficient]) are satisfied given
the same conditions. *) 

Inductive Affordable (sys: System): Prop :=
  satisfiesAffordabilityPrerequisites:
    MissionEffective sys ->
    Efficient sys ->
    Affordable sys.


(** Dependable *)
(**
[Dependable] is a composite attribute of [Security], [Safety], [Reliability], ..., and [Robustness].

Informally, 
A system [sys] belonging to the set of systems [System] is deemed [Dependable] given the set of contexts [Context]
and phases [Phase] if and only if all the requirements of its sub-attributes ([Security], [Safety], [Reliability],
..., and [Robustness]) are satisfied given the same conditions.
*)
Inductive Secure (sys: System) : Prop :=
  satisfiesSecurityRequirement:
    (exists secure: System -> Prop, secure sys) -> Secure sys.

Inductive Safe (sys: System) : Prop :=
  satisfiesSafetyRequirement:
    (exists safe: System -> Prop, safe sys) -> Safe sys.

Inductive Reliable (sys: System) : Prop :=
  satisfiesReliabilityRequirement:
    (exists reliable: System -> Prop, reliable sys) -> Reliable sys.

Inductive Maintainable (sys: System) : Prop :=
  satisfiesMaintainabilityRequirement:
    (exists maintainable: System -> Prop, maintainable sys) -> Maintainable sys.

Inductive Available (sys: System) : Prop :=
  satisfiesAvailabilityRequirement:
    (exists available: System -> Prop, available sys) -> Available sys.

Inductive Survivable (sys: System) : Prop :=
  satisfiesSurvivabilityRequirement:
    (exists survivable: System -> Prop, survivable sys) -> Survivable sys.

Inductive Robust (sys: System) : Prop :=
  satisfiesRobustnessRequirement:
    (exists robust: System -> Prop, robust sys) -> Robust sys.

Inductive Dependable (sys: System) : Prop :=
  satisfiesDependabilityPrerequisites:
    Secure sys ->
    Safe sys ->
    Reliable sys ->
    Maintainable sys ->
    Available sys ->
    Survivable sys ->
    Robust sys ->
    Dependable sys.

(** Flexible *)
(**
Boehm stipulates that, " ...The three means for achieving the end parent class of
Flexibility are Modifiability, Tailorability, and Adaptability."
*)

(**
Informally, a system [sys] of type [System] is deemed to be [Flexible] (i.e., to satisfy
its flexibility requirements) for all stakeholders, contexts, and phases, if it satisfies its
lower-level modifiability, tailorability, and adaptability requirements across this set of
parameters.
*)

Inductive Modifiable (sys: System) : Prop :=
  satisfiesModifiabilityRequirement:
    (exists modifiable: System -> Prop, modifiable sys) -> Modifiable sys.

Inductive Tailorable (sys: System) : Prop :=
  satisfiesTailorabilityRequirement:
    (exists tailorable: System -> Prop, tailorable sys) -> Tailorable sys.


Inductive Adaptable  (sys: System) : Prop :=
  satisfiesAdaptabilityRequirement:
    (exists adaptable: System -> Prop, adaptable sys) -> Adaptable sys.

Inductive Flexible (sys: System)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable sys ->
    Tailorable sys ->
    Adaptable sys ->
    Flexible sys.

(** Resilient *)
(**
Boehm stipulates that [Resiliency] is a composite quality comprising [Dependability]
and [Flexibility]. That is, a system can be deemed to be resilient across stakeholders,
operational contexts, and lifecycle phases if it is deemed to be dependable and flexible in
all these dimensions.

The definition we give here includes [Changeable] as a sub-quality of resiliency, as
well. We have inserted this node to illustrate how we can begin to combine Boehm's
top-level taxonomy with quality-specific formal theories developed by others.
 *)
Inductive Resilient (sys: System)
: Prop :=
  satisfiesResiliencyPrerequisites:
    Dependable sys ->
    Flexible sys ->
    Resilient sys.


(** Satisfactory *)
(** 
A given system [sys] of type [System] is satisfactory if, and only if, 
for its given set of Stakeholders [Stakeholder], contexts [Context],
and phases [Phase], it is both [Affordable] and [Resilient].  These
system qualities are themselves composites of lower-level system
qualities, as detailed in their respective files.
*)
Inductive Satisfactory (sys: System): Prop :=
  meetsSatisfactoryRequirements: Affordable sys -> Resilient sys -> Satisfactory sys.
