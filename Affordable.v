Add Rec LoadPath "./ContributeQA".

Require Import MissionEffective.
Require Import ResourceUtilization.

(** ** AFFORDABLE**)
(**
[Affordability] is a composite attribute of [MissionEffective] and [ResourceUtilization].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [ResourceUtilization].

In the following definition, [Affordable] is parameterized by three typeclasses, [System], [Stakerholder],
and [Context], a system, sys, of type [System], and sevaral tenary relations and binary relations 
over [System], [Context], and/or [Stakeholder].
Those tenary and binary relations are associated with its two sub-attributes, [MissionEffective] and [ResourceUtilization],
and their sub-attributes. For example, me_sh_cx represents a tenary relation, which is to say, a set of tripples, (s, sh, c), 
between a system, s, a stakerholder, sh, and a context, c, that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its mission effecitive requirement (which isn't represented
explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [Affordable] for all [Contexts], the system is
mission effective implicitly for all [Stakeholders] in those [Contexts], only if a system is 
both [MissionEffective] and [ResourceUtilization] in those [Contexts]. That is, all the requirements of the subattributes of 
both [MissionEffective] and [ResourceUtilization] are satisfied.
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
