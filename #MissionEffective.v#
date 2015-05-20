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
                           (me_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (pc_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (cc_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (hu_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (sp_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (ed_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (mv_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (ac_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (ip_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (sc_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (vs_sh_cx: System -> Stakeholder -> Context -> Prop)
                           (io_sh_cx: System -> Stakeholder -> Context -> Prop)
                           : Prop := 
  mk_mission_eff:
    PhysicalCapable System Stakeholder Context sys pc_sh_cx -> 
    CyberCapable System Stakeholder Context sys cc_sh_cx ->
    HumanUsable System Stakeholder Context sys hu_sh_cx ->
    Speed System Stakeholder Context sys sp_sh_cx ->
    Endurable System Stakeholder Context sys ed_sh_cx ->
    Maneuverable System Stakeholder Context sys mv_sh_cx ->
    Accurate System Stakeholder Context sys ac_sh_cx ->
    Impact System Stakeholder Context sys ip_sh_cx ->
    Scalable System Stakeholder Context sys sc_sh_cx ->
    Versatile System Stakeholder Context sys vs_sh_cx ->
    Interoperable System Stakeholder Context sys io_sh_cx ->
    MissionEffective System Stakeholder Context sys me_sh_cx pc_sh_cx cc_sh_cx 
        hu_sh_cx sp_sh_cx ed_sh_cx mv_sh_cx ac_sh_cx ip_sh_cx sc_sh_cx vs_sh_cx io_sh_cx.