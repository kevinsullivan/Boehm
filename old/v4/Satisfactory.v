(** * System Quality General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)
Add Rec LoadPath "./ContributeQA".

Require Export MissionEffective.
Require Export ResourceUtilization.
Require Export Dependable.
Require Export Flexible.
Require Export Affordable.
Require Export Resilient.

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) := {
      sys: System

    ; me_sh_cx : System -> Stakeholder -> Context -> Prop
    ; pc_sh_cx : System -> Stakeholder -> Context -> Prop 
    ; cc_sh_cx : System -> Stakeholder -> Context -> Prop
    ; hu_sh_cx : System -> Stakeholder -> Context -> Prop
    ; sp_sh_cx : System -> Stakeholder -> Context -> Prop
    ; ed_sh_cx : System -> Stakeholder -> Context -> Prop
    ; mv_sh_cx : System -> Stakeholder -> Context -> Prop
    ; ac_sh_cx : System -> Stakeholder -> Context -> Prop
    ; ip_sh_cx : System -> Stakeholder -> Context -> Prop
    ; sc_sh_cx : System -> Stakeholder -> Context -> Prop
    ; vs_sh_cx : System -> Stakeholder -> Context -> Prop
    ; io_sh_cx : System -> Stakeholder -> Context -> Prop

    ; ru_cx : System -> Context -> Prop
    ; cs_cx : System -> Context -> Prop
    ; dr_cx : System -> Context -> Prop
    ; kp_cx : System -> Context -> Prop
    ; osr_cx : System -> Context -> Prop
    ; mf_cx : System -> Context -> Prop
    ; sust_cx : System -> Context -> Prop

    ; dp_cx : System -> Context -> Prop
    ; sec_cx : System -> Context -> Prop
    ; sf_cx : System -> Context -> Prop
    ; rl_cx : System -> Context -> Prop
    ; mt_cx : System -> Context -> Prop
    ; avl_cx : System -> Context -> Prop
    ; svv_cx : System -> Context -> Prop

    ; fl_cx : System -> Context -> Prop
    ; md_cx : System -> Context -> Prop
    ; tl_cx : System -> Context -> Prop
    ; adp_cx : System -> Context -> Prop

    ; me: MissionEffective System Stakeholder Context sys me_sh_cx pc_sh_cx cc_sh_cx hu_sh_cx sp_sh_cx 
              ed_sh_cx mv_sh_cx ac_sh_cx ip_sh_cx sc_sh_cx vs_sh_cx io_sh_cx
    ; ru: ResourceUtilization System Context sys ru_cx cs_cx dr_cx kp_cx osr_cx mf_cx sust_cx
    ; dp: Dependable System Context sys dp_cx sec_cx sf_cx rl_cx mt_cx avl_cx svv_cx
    ; fl: Flexible System Context sys fl_cx md_cx tl_cx adp_cx
    (* affordable is a composite property of "MissionEffective" and "ResourceUtilization"*)
    ; af: Affordable System Stakeholder Context sys 
              me_sh_cx pc_sh_cx cc_sh_cx hu_sh_cx sp_sh_cx 
              ed_sh_cx mv_sh_cx ac_sh_cx ip_sh_cx sc_sh_cx vs_sh_cx io_sh_cx
              ru_cx cs_cx dr_cx kp_cx osr_cx mf_cx sust_cx
    (* Resillient is a composite property of "Dependable" and "Flexible"*)
    ; rs: Resilient System Context sys dp_cx sec_cx sf_cx rl_cx mt_cx avl_cx svv_cx 
                                       fl_cx md_cx tl_cx adp_cx
}.