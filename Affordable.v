Add Rec LoadPath "./ContributeQA".

Require Import MissionEffective.
Require Import ResourceUtilization.

(** ** AFFORDABLE**)
(**
[Affordability] is a composite attribute of [MissionEffective] and [ResourceUtilization].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [ResourceUtilization].

In the following definition, [Affordable] is parameterized by three typeclasses, [System], [Stakeholder],
and [Context], a system, sys, of type [System], and sevaral ternary relations and binary relations
over [System], [Context], and/or [Stakeholder].
Those ternary and binary relations are associated with its two sub-attributes, [MissionEffective] and [ResourceUtilization],
and their sub-attributes.

Informally, in English:
A system [sys] belonging to the set of systems [System] is deemed [Affordable] for all stakeholders in set [Stakeholder] given
the set of contexts [Context] if and only if all the requirements of its sub-attributes ([MissionEffectiveness], and [Affordability])
are satisfied given the same conditions, i.e., the same [System], [Stakeholder], [Context], and relevant attribute relations over them.
*)

Inductive Affordable 
            (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
            (physicalCapability: System -> Stakeholder -> Context -> Prop)
            (cyberCapability: System -> Stakeholder -> Context -> Prop)
            (humanUsability: System -> Stakeholder -> Context -> Prop)
            (speed: System -> Stakeholder -> Context -> Prop)
            (endurability: System -> Stakeholder -> Context -> Prop)
            (maneuverability: System -> Stakeholder -> Context -> Prop)
            (accuracy: System -> Stakeholder -> Context -> Prop)
            (impact: System -> Stakeholder -> Context -> Prop)
            (scalability: System -> Stakeholder -> Context -> Prop)
            (versability: System -> Stakeholder -> Context -> Prop)
            (interoperability: System -> Stakeholder -> Context -> Prop)
            (cost: System -> Context -> Prop)
            (duration: System -> Context -> Prop)
            (keyPersonnel: System -> Context -> Prop)
            (otherScareResources: System -> Context -> Prop)
            (manufacturability: System -> Context -> Prop)
            (sustainability: System -> Context -> Prop):=

          isAffordable: 
             MissionEffective System Stakeholder Context sys 
                 physicalCapability cyberCapability humanUsability speed 
                 endurability maneuverability accuracy impact scalability versability interoperability->
             ResourceUtilization System Context sys cost duration keyPersonnel otherScareResources manufacturability sustainability ->
             Affordable System Stakeholder Context sys 
                 physicalCapability cyberCapability humanUsability speed 
                 endurability maneuverability accuracy impact scalability versability interoperability
                 cost duration keyPersonnel otherScareResources manufacturability sustainability.
