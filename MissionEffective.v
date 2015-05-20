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


(** ** MISSIONEFFECTIVE**)
(**
In the following definition, [MissionEffective] is parameterized by three typeclasses, [System], [Stakerholder],
and [Context], a system, sys, of type [System], and sevaral tenary relations
over [System], [Context], and/or [Stakeholder].
Those tenary are associated with its sub-attributes. For example, pc_sh_cx represents a tenary relation, 
which is to say, a set of tripples, (s, sh, c), between a system, s, a stakerholder, sh, and a context, c, 
that we  intend to hold (for the proposition to be provable, 
iff system s satisfies its mission effecitive requirement (which isn't represented
explicitly here) in context, c.)

Its definition indicates that the property of a [System] being [MissionEffective] for all [Contexts], the system is
mission effective implicitly for all [Stakeholders] in those [Contexts], only if all the requirements of the subattributes
are satisfied.
*)

Inductive MissionEffective (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
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
                           : Prop := 
  mk_mission_eff:
    PhysicalCapable System Stakeholder Context sys physicalCapability -> 
    CyberCapable System Stakeholder Context sys cyberCapability ->
    HumanUsable System Stakeholder Context sys humanUsability ->
    Speed System Stakeholder Context sys speed ->
    Endurable System Stakeholder Context sys endurability ->
    Maneuverable System Stakeholder Context sys maneuverability ->
    Accurate System Stakeholder Context sys accuracy ->
    Impact System Stakeholder Context sys impact ->
    Scalable System Stakeholder Context sys scalability ->
    Versatile System Stakeholder Context sys versability ->
    Interoperable System Stakeholder Context sys interoperability ->
    MissionEffective System Stakeholder Context sys physicalCapability cyberCapability 
        humanUsability speed endurability maneuverability accuracy impact scalability versability interoperability.