(** * Examples to prove that a system has quality attributes. *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)
Add Rec LoadPath "./ContributeQA".

Require Import Satisfactory.
(*Require Import MissionEffective.
Require Import ResourceUtilization.
Require Import Dependable.
Require Import Flexible.
*)
(**
Example to create an instance for the TypeClass
**)

Definition Example_System_Type := bool.
Inductive Example_Stakeholder_Type := s1 | s2.
Definition Example_Context_Type := nat.

Inductive me_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_me: sys = true -> me_sh_cx_example sys sh cx.

Inductive pc_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_pc: sys = true -> pc_sh_cx_example sys sh cx.

Inductive cc_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_cc: sys = true -> cc_sh_cx_example sys sh cx.

Inductive hu_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_hu: sys = true -> hu_sh_cx_example sys sh cx.

Inductive sp_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_sp: sys = true -> sp_sh_cx_example sys sh cx.

Inductive ed_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_ed: sys = true -> ed_sh_cx_example sys sh cx.

Inductive mv_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_mv: sys = true -> mv_sh_cx_example sys sh cx.

Inductive ac_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_ac: sys = true -> ac_sh_cx_example sys sh cx.

Inductive ip_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_ip: sys = true -> ip_sh_cx_example sys sh cx.

Inductive sc_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_sc: sys = true -> sc_sh_cx_example sys sh cx.

Inductive vs_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_vs: sys = true -> vs_sh_cx_example sys sh cx.

Inductive io_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_io: sys = true -> io_sh_cx_example sys sh cx.

Inductive ru_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_ru: sys = true -> ru_cx_example sys cx.

Inductive cs_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_cs: sys = true -> cs_cx_example sys cx.

Inductive dr_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_dr: sys = true -> dr_cx_example sys cx.

Inductive kp_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_kp: sys = true -> kp_cx_example sys cx.

Inductive osr_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_osr: sys = true -> osr_cx_example sys cx.

Inductive mf_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_mf: sys = true -> mf_cx_example sys cx.

Inductive sust_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_sust: sys = true -> sust_cx_example sys cx.

Inductive dp_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_dp: sys = true -> dp_cx_example sys cx.

Inductive sec_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_sec: sys = true -> sec_cx_example sys cx.

Inductive sf_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_sf: sys = true -> sf_cx_example sys cx.

Inductive rl_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_rl: sys = true -> rl_cx_example sys cx.

Inductive mt_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_mt: sys = true -> mt_cx_example sys cx.

Inductive avl_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_avl: sys = true -> avl_cx_example sys cx.

Inductive svv_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_svv: sys = true -> svv_cx_example sys cx.

Inductive fl_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_fl: sys = true -> fl_cx_example sys cx.

Inductive md_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_md: sys = true -> md_cx_example sys cx.

Inductive tl_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_tl: sys = true -> tl_cx_example sys cx.

Inductive adp_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_adp: sys = true -> adp_cx_example sys cx.

Instance Sys_is_good: Satisfactory Example_System_Type Example_Stakeholder_Type Example_Context_Type  := {
    sys := true
  ; me_sh_cx := me_sh_cx_example
  ; pc_sh_cx := pc_sh_cx_example
  ; cc_sh_cx := cc_sh_cx_example
  ; hu_sh_cx := hu_sh_cx_example
  ; sp_sh_cx := sp_sh_cx_example
  ; ed_sh_cx := ed_sh_cx_example
  ; mv_sh_cx := mv_sh_cx_example
  ; ac_sh_cx := ac_sh_cx_example
  ; ip_sh_cx := ip_sh_cx_example
  ; sc_sh_cx := sc_sh_cx_example
  ; vs_sh_cx := vs_sh_cx_example
  ; io_sh_cx := io_sh_cx_example

  ; ru_cx := ru_cx_example
  ; cs_cx := cs_cx_example
  ; dr_cx := dr_cx_example
  ; kp_cx := kp_cx_example
  ; osr_cx := osr_cx_example
  ; mf_cx := mf_cx_example
  ; sust_cx := sust_cx_example

  ; dp_cx := dp_cx_example
  ; sec_cx := sec_cx_example
  ; sf_cx := sf_cx_example
  ; rl_cx := rl_cx_example
  ; mt_cx := mt_cx_example
  ; avl_cx := avl_cx_example
  ; svv_cx := svv_cx_example

  ; fl_cx := fl_cx_example
  ; md_cx := md_cx_example
  ; tl_cx := tl_cx_example
  ; adp_cx := adp_cx_example

}.
Proof.
apply mk_mission_eff.
apply mk_physical_capable.
intros; apply true_is_pc; reflexivity.
apply mk_cyber_capable.
intros; apply true_is_cc; reflexivity.
apply mk_human_usable.
intros; apply true_is_hu; reflexivity.
apply mk_speed.
intros; apply true_is_sp; reflexivity.
apply mk_endurable.
intros; apply true_is_ed; reflexivity.
apply mk_maneuverable.
intros; apply true_is_mv; reflexivity.
apply mk_accurate.
intros; apply true_is_ac; reflexivity.
apply mk_impact.
intros; apply true_is_ip; reflexivity.
apply mk_scalable.
intros; apply true_is_sc; reflexivity.
apply mk_versatile.
intros; apply true_is_vs; reflexivity.
apply mk_interoperable.
intros; apply true_is_io; reflexivity.
apply mk_resource_utl.
apply mk_cost.
intros; apply true_system_cs; reflexivity.
apply mk_duration.
intros; apply true_system_dr; reflexivity.
apply mk_key_personnel.
intros; apply true_system_kp; reflexivity.
apply mk_other_scarce_resources.
intros; apply true_system_osr; reflexivity.
apply mk_manufacturability.
intros; apply true_system_mf; reflexivity.
apply mk_sustainability.
intros; apply true_system_sust; reflexivity.
apply mk_dependability.
apply mk_secure.
intros; apply true_system_sec; reflexivity.
apply mk_safe.
intros; apply true_system_sf; reflexivity.
apply mk_reliability.
intros; apply true_system_rl; reflexivity.
apply mk_maintainability.
intros; apply true_system_mt; reflexivity.
apply mk_availability.
intros; apply true_system_avl; reflexivity.
apply mk_survivability.
intros; apply true_system_svv; reflexivity.
apply isFlexible.
apply mk_modifiability.
intros; apply true_system_md; reflexivity.
apply mk_tailorability.
intros; apply true_system_tl; reflexivity.
apply mk_adaptability.
intros; apply true_system_adp; reflexivity.
apply isAffordable.
apply mk_mission_eff.
apply mk_physical_capable.
intros; apply true_is_pc; reflexivity.
apply mk_cyber_capable.
intros; apply true_is_cc; reflexivity.
apply mk_human_usable.
intros; apply true_is_hu; reflexivity.
apply mk_speed.
intros; apply true_is_sp; reflexivity.
apply mk_endurable.
intros; apply true_is_ed; reflexivity.
apply mk_maneuverable.
intros; apply true_is_mv; reflexivity.
apply mk_accurate.
intros; apply true_is_ac; reflexivity.
apply mk_impact.
intros; apply true_is_ip; reflexivity.
apply mk_scalable.
intros; apply true_is_sc; reflexivity.
apply mk_versatile.
intros; apply true_is_vs; reflexivity.
apply mk_interoperable.
intros; apply true_is_io; reflexivity.
apply mk_resource_utl.
apply mk_cost.
intros; apply true_system_cs; reflexivity.
apply mk_duration.
intros; apply true_system_dr; reflexivity.
apply mk_key_personnel.
intros; apply true_system_kp; reflexivity.
apply mk_other_scarce_resources.
intros; apply true_system_osr; reflexivity.
apply mk_manufacturability.
intros; apply true_system_mf; reflexivity.
apply mk_sustainability.
intros; apply true_system_sust; reflexivity.
apply isResilient.
apply mk_dependability.
apply mk_secure.
intros; apply true_system_sec; reflexivity.
apply mk_safe.
intros; apply true_system_sf; reflexivity.
apply mk_reliability.
intros; apply true_system_rl; reflexivity.
apply mk_maintainability.
intros; apply true_system_mt; reflexivity.
apply mk_availability.
intros; apply true_system_avl; reflexivity.
apply mk_survivability.
intros; apply true_system_svv; reflexivity.
apply isFlexible.
apply mk_modifiability.
intros; apply true_system_md; reflexivity.
apply mk_tailorability.
intros; apply true_system_tl; reflexivity.
apply mk_adaptability.
intros; apply true_system_adp; reflexivity.
Defined.