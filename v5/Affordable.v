Add Rec LoadPath "./ContributeQA".

Require Import MissionEffective.
Require Import ResourceUtilization.

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
