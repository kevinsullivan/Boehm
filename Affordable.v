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
            (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
            (physicalCapability: System -> Stakeholder -> Context -> Phase -> Prop)
            (cyberCapability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (humanUsability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (speed: System -> Stakeholder -> Context -> Phase -> Prop) 
            (endurability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (maneuverability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (accuracy: System -> Stakeholder -> Context -> Phase -> Prop) 
            (impact: System -> Stakeholder -> Context -> Phase -> Prop) 
            (scalability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (versability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (interoperability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (cost: System -> Stakeholder -> Context -> Phase -> Prop) 
            (duration: System -> Stakeholder -> Context -> Phase -> Prop) 
            (keyPersonnel: System -> Stakeholder -> Context -> Phase -> Prop) 
            (otherScareResources: System -> Stakeholder -> Context -> Phase -> Prop) 
            (manufacturability: System -> Stakeholder -> Context -> Phase -> Prop) 
            (sustainability: System -> Stakeholder -> Context -> Phase -> Prop) 
            : Prop :=

          isAffordable: 
             MissionEffective System Stakeholder Context Phase sys 
                 physicalCapability cyberCapability humanUsability speed 
                 endurability maneuverability accuracy impact scalability versability interoperability->
             ResourceUtilization System Stakeholder Context Phase sys cost duration keyPersonnel otherScareResources manufacturability sustainability ->
             Affordable System Stakeholder Context Phase sys
                 physicalCapability cyberCapability humanUsability speed 
                 endurability maneuverability accuracy impact scalability versability interoperability
                 cost duration keyPersonnel otherScareResources manufacturability sustainability.
