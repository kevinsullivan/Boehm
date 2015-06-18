Require Export System.
Require Export Changeable.


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
Inductive Accurate (sys_type: SystemType): Prop :=
  satisfiesAccuracyRequirements:
    (exists accurate: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, accurate c p s st) ->
        Accurate sys_type.

Inductive PhysicalCapable (sys_type: SystemType) : Prop :=
  satisfiesPhysicalCapabilityRequirements:
    (exists physicalCapable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, physicalCapable c p s st) ->
        PhysicalCapable sys_type.

Inductive CyberCapable (sys_type: SystemType) : Prop :=
  satisfiesCyberCapabilityRequirements:
    (exists cyberCapable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, cyberCapable c p s st) ->
        CyberCapable sys_type.

Inductive HumanUsable (sys_type: SystemType) : Prop :=
  satisfiesHumanUsabilityRequirements:
    (exists humanUsable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, humanUsable c p s st) ->
        HumanUsable sys_type.

Inductive Speed (sys_type: SystemType) : Prop :=
  satisfiesSpeedRequirements:
    (exists speed: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, speed c p s st) ->
        Speed sys_type.

Inductive Endurable (sys_type: SystemType) : Prop :=
  satisfiesEndurabilityRequirements:
    (exists endurable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, endurable c p s st) ->
        Endurable sys_type.

Inductive Maneuverable (sys_type: SystemType) : Prop :=
  satisfiesManeuverabilityRequirements:
    (exists maneuverable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, maneuverable c p s st) ->
        Maneuverable sys_type.

Inductive Impactful (sys_type: SystemType) : Prop :=
  satisfiesImpactRequirements:
    (exists impactful: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, impactful c p s st) ->
        Impactful sys_type.

Inductive Scalable (sys_type: SystemType) : Prop :=
  satisfiesScalabilityRequirements:
    (exists scalable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, scalable c p s st) ->
        Scalable sys_type.

Inductive Versatile (sys_type: SystemType) : Prop :=
  satisfiesVersatilityRequirements:
    (exists versatile: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, versatile c p s st) ->
        Versatile sys_type.

Inductive Interoperable (sys_type: SystemType) : Prop :=
  satisfiesInteroperabilityRequirements:
    (exists interoperable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, interoperable c p s st) ->
        Interoperable sys_type.

Inductive MissionEffective (sys_type: SystemType): Prop :=
  satisfiesMissionEffectivenessPrerequisites:
    PhysicalCapable sys_type ->
    CyberCapable sys_type ->
    HumanUsable sys_type ->
    Speed sys_type ->
    Endurable sys_type ->
    Maneuverable sys_type ->
    Accurate sys_type ->
    Impactful sys_type ->
    Scalable sys_type ->
    Versatile sys_type ->
    Interoperable sys_type ->
    MissionEffective sys_type.

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

Inductive Cost (sys_type: SystemType) : Prop :=
  satisfiesCostRequirements:
    (exists cost: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, cost c p s st) ->
        Cost sys_type.

Inductive Duration (sys_type: SystemType) : Prop :=
  satisfiesDurationRequirements:
    (exists duration: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, duration c p s st) ->
        Duration sys_type.

Inductive KeyPersonnel (sys_type: SystemType) : Prop :=
  satisfiesKeyPersonnelRequirements:
    (exists keyPersonnel: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, keyPersonnel c p s st) ->
        KeyPersonnel sys_type.

Inductive OtherScarceResources (sys_type: SystemType) : Prop :=
  satisfiesOtherResourcesRequirements:
    (exists otherScarceResources: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, otherScarceResources c p s st) ->
        OtherScarceResources sys_type.

Inductive Manufacturable (sys_type: SystemType) : Prop :=
  satisfiesManufacturabilityRequirements:
    (exists manufacturable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, manufacturable c p s st) ->
        Manufacturable sys_type.

Inductive Sustainable (sys_type: SystemType) : Prop :=
  satisfiesSustainabilityRequirements:
    (exists sustainable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, sustainable c p s st) ->
        Sustainable sys_type.

Inductive Efficient (sys_type: SystemType) : Prop :=
  satisfiesEfficiencyPrerequisites:
    Cost sys_type ->
    Duration sys_type ->
    KeyPersonnel sys_type ->
    OtherScarceResources sys_type ->
    Manufacturable sys_type ->
    Sustainable sys_type ->
    Efficient sys_type.


(** Affordable *)
(**
[Affordability] is a composite attribute of [MissionEffective] and [Efficient].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [Efficient].

Informally,
A system [sys] belonging to the set of systems [System] is deemed [Affordable] for all stakeholders
in set [Stakeholder] given the set of phases and contexts [Context] and [Phase] if and only if all the
requirements of its sub-attributes ([MissionEffective], and [Efficient]) are satisfied given
the same conditions. *) 

Inductive Affordable (sys_type: SystemType): Prop :=
  satisfiesAffordabilityPrerequisites:
    MissionEffective sys_type ->
    Efficient sys_type ->
    Affordable sys_type.


(** Dependable *)
(**
[Dependable] is a composite attribute of [Security], [Safety], [Reliability], ..., and [Robustness].

Informally, 
A system [sys] belonging to the set of systems [System] is deemed [Dependable] given the set of contexts [Context]
and phases [Phase] if and only if all the requirements of its sub-attributes ([Security], [Safety], [Reliability],
..., and [Robustness]) are satisfied given the same conditions.
*)
Inductive Secure (sys_type: SystemType) : Prop :=
  satisfiesSecurityRequirements:
    (exists secure: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, secure c p s st) ->
        Secure sys_type.

Inductive Safe (sys_type: SystemType) : Prop :=
  satisfiesSafetyRequirements:
    (exists safe: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, safe c p s st) ->
        Safe sys_type.

Inductive Reliable (sys_type: SystemType) : Prop :=
  satisfiesReliabilityRequirements:
    (exists reliable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, reliable c p s st) ->
        Reliable sys_type.

Inductive Maintainable (sys_type: SystemType) : Prop :=
  satisfiesMaintainabilityRequirements:
    (exists maintainable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, maintainable c p s st) ->
        Maintainable sys_type.

Inductive Available (sys_type: SystemType) : Prop :=
  satisfiesAvailabilityRequirements:
    (exists available: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, available c p s st) ->
        Available sys_type.

Inductive Survivable (sys_type: SystemType) : Prop :=
  satisfiesSurvivabilityRequirements:
    (exists survivable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, survivable c p s st) ->
        Survivable sys_type.

Inductive Robust (sys_type: SystemType) : Prop :=
  satisfiesRobustnessRequirements:
    (exists robust: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, robust c p s st) ->
        Robust sys_type.

Inductive Dependable (sys_type: SystemType) : Prop :=
  satisfiesDependabilityPrerequisites:
    Secure sys_type ->
    Safe sys_type ->
    Reliable sys_type ->
    Maintainable sys_type ->
    Available sys_type ->
    Survivable sys_type ->
    Robust sys_type ->
    Dependable sys_type.

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

Inductive Modifiable (sys_type: SystemType) : Prop :=
  satisfiesModifiabilityRequirements:
    (exists modifiable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, modifiable c p s st) ->
        Modifiable sys_type.

Inductive Tailorable (sys_type: SystemType) : Prop :=
  satisfiesTailorabilityRequirements:
    (exists tailorable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, tailorable c p s st) ->
        Tailorable sys_type.


Inductive Adaptable (sys_type: SystemType) : Prop :=
  satisfiesAdaptabilityRequirements:
    (exists adaptable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, adaptable c p s st) ->
        Adaptable sys_type.

Inductive Flexible (sys_type: SystemType)
: Prop :=
  satisfiesFlexibilityPrerequisites:
    Modifiable sys_type ->
    Tailorable sys_type ->
    Adaptable sys_type ->
    Flexible sys_type.

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
Inductive Resilient (sys_type: SystemType)
: Prop :=
  satisfiesResiliencyPrerequisites:
    Dependable sys_type ->
    Flexible sys_type ->
    Changeable sys_type ->
    Resilient sys_type.


(** Satisfactory *)
(** 
A given system [sys] of type [System] is satisfactory if, and only if, 
for its given set of Stakeholders [Stakeholder], contexts [Context],
and phases [Phase], it is both [Affordable] and [Resilient].  These
system qualities are themselves composites of lower-level system
qualities, as detailed in their respective files.
*)
Inductive Satisfactory (sys_type: SystemType): Prop :=
  meetsSatisfactoryRequirementss: Affordable sys_type -> Resilient sys_type -> Satisfactory sys_type.
