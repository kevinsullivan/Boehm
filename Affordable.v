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
            (ru_cx: System -> Context -> Prop)
            (cs_cx: System -> Context -> Prop)
            (dr_cx: System -> Context -> Prop)
            (kp_cx: System -> Context -> Prop)
            (osr_cx: System -> Context -> Prop)
            (mf_cx: System -> Context -> Prop)
            (sust_cx: System -> Context -> Prop):=

          isAffordable: 
             MissionEffective System Stakeholder Context sys 
                 me_sh_cx pc_sh_cx cc_sh_cx hu_sh_cx sp_sh_cx 
                 ed_sh_cx mv_sh_cx ac_sh_cx ip_sh_cx sc_sh_cx vs_sh_cx io_sh_cx->
             ResourceUtilization System Context sys ru_cx cs_cx 
                 dr_cx kp_cx osr_cx mf_cx sust_cx ->
             Affordable System Stakeholder Context sys 
                 me_sh_cx pc_sh_cx cc_sh_cx hu_sh_cx sp_sh_cx 
                 ed_sh_cx mv_sh_cx ac_sh_cx ip_sh_cx sc_sh_cx vs_sh_cx io_sh_cx
                 ru_cx cs_cx dr_cx kp_cx osr_cx mf_cx sust_cx.
