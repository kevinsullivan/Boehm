Inductive Dependable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesDependabilityPrerequisites:
    Secure sys ->
    Safe sys ->
    Reliable sys ->
    Maintainable sys ->
    Available sys ->
    Survivable sys ->
    Robust sys ->
    Dependable sys.

Inductive Duration {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesDurationRequirement:
    (exists duration: System msys -> Prop, duration sys) -> Duration sys.
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
Inductive Efficient {msys: MetaSystem} (sys: System msys) : Prop := 
  satisfiesEfficiencyPrerequisites:
    Cost sys ->
    Duration sys ->
    KeyPersonnel sys ->
    OtherScarceResources sys ->
    Manufacturable sys ->
    Sustainable sys ->
    Efficient sys.

Inductive Endurable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesEndurabilityRequirement:
    (exists endurable: System msys -> Prop, endurable sys) -> Endurable sys.

Inductive Flexible {msys: MetaSystem} (sys: System msys)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable sys ->
    Tailorable sys ->
    Adaptable sys ->
    Flexible sys.


Inductive HumanUsable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesHumanUsabilityRequirement:
    (exists humanUsable: System msys -> Prop, humanUsable sys) -> HumanUsable sys.

Inductive Impactful {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesImpactRequirement:
    (exists impactful: System msys -> Prop, impactful sys) -> Impactful sys.

Inductive Interoperable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesInteroperabilityRequirement:
    (exists interoperable: System msys -> Prop, interoperable sys) -> Interoperable sys.

Inductive KeyPersonnel {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesKeyPersonnelRequirement:
    (exists key_personnel: System msys -> Prop, key_personnel sys) -> KeyPersonnel sys.

Inductive Maintainable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesMaintainabilityRequirement:
    (exists maintainable: System msys -> Prop, maintainable sys) -> Maintainable sys.

Inductive Maneuverable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesManeuverabilityRequirement:
    (exists maneuverable: System msys -> Prop, maneuverable sys) -> Maneuverable sys.

Inductive Manufacturable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesManufacturabilityRequirement:
    (exists manufacturable: System msys -> Prop, manufacturable sys) -> Manufacturable sys.
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
Inductive MissionEffective {msys: MetaSystem} (sys: System msys): Prop :=
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


Inductive Modifiable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesModifiabilityRequirement:
    (exists modifiable: System msys -> Prop, modifiable sys) -> Modifiable sys.


Inductive OtherScarceResources {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesOtherResourcesRequirement:
    (exists otherResources: System msys -> Prop, otherResources sys) -> OtherScarceResources sys.

Inductive PhysicalCapable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesPhysicalCapabilityRequirement:
    (exists physicalCapable: System msys -> Prop, physicalCapable sys) -> PhysicalCapable sys.


Inductive Reliable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesReliabilityRequirement:
    (exists reliable: System msys -> Prop, reliable sys) -> Reliable sys.

(** 
Boehm stipulates that [Resiliency] is a composite quality comprising [Dependability] 
and [Flexibility]. That is, a system can be deemed to be resilient across stakeholders,
operational contexts, and lifecycle phases if it is deemed to be dependable and flexible in
all these dimensions.

The definition we give here includes [Changeable] as a sub-quality of resiliency, as
well. We have inserted this node to illustrate how we can begin to combine Boehm's
top-level taxonomy with quality-specific formal theories developed by others. 
*)
Inductive Resilient {msys: MetaSystem} (sys: System msys)
: Prop :=
  satisfiesResiliencyPrerequisites:
    Dependable sys ->
    Flexible sys ->
    Changeable sys ->
    Changeable_Ross sys ->
    Resilient sys.


Inductive Robust {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesRobustnessRequirement:
    (exists robust: System msys -> Prop, robust sys) -> Robust sys.

Inductive Satisfactory {msys: MetaSystem} (sys: System msys): Prop := 
  meetsSatisfactoryRequirements: Affordable sys -> Resilient sys -> Satisfactory sys.

Inductive Safe {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSafetyRequirement:
    (exists safe: System msys -> Prop, safe sys) -> Safe sys.

Inductive Scalable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesScalabilityRequirement:
    (exists scalable: System msys -> Prop, scalable sys) -> Scalable sys.

Inductive Secure {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSecurityRequirement:
    (exists secure: System msys -> Prop, secure sys) -> Secure sys.

Inductive Speed {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSpeedRequirement:
    (exists speed: System msys -> Prop, speed sys) -> Speed sys.

Inductive Survivable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSurvivabilityRequirement:
    (exists survivable: System msys -> Prop, survivable sys) -> Survivable sys.

Inductive Sustainable (sys: System) : Prop :=
  satisfiesSustainabilityRequirement:
    (exists sustainable: System -> Prop, sustainable sys) -> Sustainable sys.
(** 
Boehm stipulates that, "Tailorability accomplishes Flexibility without changes in the 
system's  overall structure or state, via such mechanisms as generics, design patterns, 
and plug-compatible receptors."

We model [Tailorable] in a completely generic way, providing the user of the taxonomy
with a place to plug in system-specific tailorability requirements for a given system for
each combination of stakeholder, context, and phase. As long as certificates are given
for satisfaction on these system-specific, end-user requirements, the proof constructor
of this type will be able to construct a proof/certificate that a given system is [Tailorable].

Note that at this level, we do not attempt to formalize the notion that tailorability means
flexibility without changes in system structure or state. Nor do we model mechanisms
that support tailorability. Our approach to these issues will have two parts. First, we will
defer specification of such details to quality-specific (e.g., flexibility-specific) languages.
Second, we will elaborate system models to include such concepts as structure and 
state, and we will devise little lanuages that are sensitive to such parameters. We have
not developed this idea as of June 1, 2015.
*)
Inductive Tailorable (sys: System) : Prop :=
  satisfiesTailorabilityRequirement:
    (exists tailorable: System -> Prop, tailorable sys) -> Tailorable sys.

Inductive Versatile (sys: System) : Prop :=
  satisfiesVersatilityRequirement:
    (exists versatile: System -> Prop, versatile sys) -> Versatile sys.

