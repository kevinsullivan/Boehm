(** * MissionEffective General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross

March, 2015
*)

Add Rec LoadPath "./ContributeQA".
Require Export PhysicalCapable.
Require Export CyberCapable.
Require Export HumanUsable.
Require Export Speed.
Require Export Endurable.
Require Export Maneuverable.
Require Export Accurate.
Require Export Impact.
Require Export Scalable.
Require Export Versatile.
Require Export Interoperable.

(** ** Mission Effective **)

(**
In the following definition, [MissionEffective] is parameterized by three typeclasses,
[System], [Stakerholder], and [Context], a system, sys, of type [System], and sevaral ternary
relations over [System], [Context], and/or [Stakeholder].
Those ternary relations are associated with its sub-attributes. For example, physicalCapability is a ternary relation,
which is to say, a set of triples, (s, sh, c), between a system, s, a stakeholder, sh, and a context, c,
that we expect to hold (for the proposition to be provable, iff system s satisfies its mission effective
requirement (which isn't represented explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [MissionEffective] for all [Contexts], the system is
mission effective implicitly for all [Stakeholders] in those [Contexts], only if all the requirements of the subattributes
are satisfied.
*)

Inductive MissionEffective (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                           (physicalCapability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (cyberCapability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (humanUsability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (speed: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (endurability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (maneuverability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (accuracy: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (impact: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (scalability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (versatility: System -> Stakeholder -> Context -> Phase -> Prop) 
                           (interoperability: System -> Stakeholder -> Context -> Phase -> Prop) 
                           : Prop :=
  isMissionEffective:
    PhysicalCapable System Stakeholder Context Phase sys physicalCapability ->
    CyberCapable System Stakeholder Context Phase sys cyberCapability ->
    HumanUsable System Stakeholder Context Phase sys humanUsability ->
    Speed System Stakeholder Context Phase sys speed ->
    Endurable System Stakeholder Context Phase sys endurability ->
    Maneuverable System Stakeholder Context Phase sys maneuverability ->
    Accurate System Stakeholder Context Phase sys accuracy ->
    Impact System Stakeholder Context Phase sys impact ->
    Scalable System Stakeholder Context Phase sys scalability ->
    Versatile System Stakeholder Context Phase sys versatility ->
    Interoperable System Stakeholder Context Phase sys interoperability ->
    MissionEffective System Stakeholder Context Phase sys physicalCapability cyberCapability
        humanUsability speed endurability maneuverability accuracy impact scalability versatility interoperability.
