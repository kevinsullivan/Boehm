(** * Examples to prove that a system has quality attributes. *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Require Import Satisfactory.
Require Import MissionEffective.
Require Import ResourceUtilization.
Require Import Dependable.
Require Import Flexible.

(**
Example to create an instance for the TypeClass
**)

Definition Example_System_Type := bool.
Inductive Example_Stakeholder_Type := s1 | s2.
Definition Example_Context_Type := nat.

Inductive me_sh_cx_example (sys: Example_System_Type) (sh: Example_Stakeholder_Type) (cx: Example_Context_Type): Prop :=
  true_is_ok: sys = true -> me_sh_cx_example sys sh cx.

Inductive ru_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_ru: sys = true -> ru_cx_example sys cx.

Inductive dp_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_dp: sys = true -> dp_cx_example sys cx.

Inductive fl_cx_example (sys: Example_System_Type) (cx: Example_Context_Type): Prop :=
  true_system_fl: sys = true -> fl_cx_example sys cx.


Instance sys_is_good: Satisfactory Example_System_Type Example_Stakeholder_Type Example_Context_Type  := {
    sys := true
  ; me_sh_cx := me_sh_cx_example
  ; ru_cx := ru_cx_example
  ; dp_cx := dp_cx_example
  ; fl_cx := fl_cx_example
}.
Proof.
apply mk_mission_eff.
intros.
apply true_is_ok.
reflexivity.
apply mk_resource_utl.
intros.
apply true_system_ru.
reflexivity.
apply mk_dependable.
intros.
apply true_system_dp.
reflexivity.
apply mk_flexible.
intros.
apply true_system_fl.
reflexivity.
split.
apply mk_mission_eff.
intros.
apply true_is_ok.
reflexivity.
apply mk_resource_utl.
intros.
apply true_system_ru.
reflexivity.
split.
apply mk_dependable.
intros.
apply true_system_dp.
reflexivity.
apply mk_flexible.
intros.
apply true_system_fl.
reflexivity.
Defined.