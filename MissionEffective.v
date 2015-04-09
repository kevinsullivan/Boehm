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


Inductive MissionEffective (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                           (me_sh_cx pc_sh_cx cc_sh_cx hu_sh_cx sp_sh_cx ed_sh_cx
                            mv_sh_cx ac_sh_cx ip_sh_cx sc_sh_cx vs_sh_cx io_sh_cx
                              : System -> Stakeholder -> Context -> Prop)
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