(** * System Quality General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Require Import MissionEffective.
Require Import ResourceUtilization.
Require Import Dependable.
Require Import Flexible.

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) := {
      sys: System
    ; me_sh_cx: System -> Stakeholder -> Context -> Prop
    ; ru_cx: System -> Context -> Prop
    ; dp_cx: System -> Context -> Prop
    ; fl_cx: System -> Context -> Prop
    ; me: MissionEffective System Stakeholder Context sys me_sh_cx
    ; ru: ResourceUtilization System Context sys ru_cx
    ; dp: Dependable System Context sys dp_cx
    ; fl: Flexible System Context sys fl_cx
    (* affordable is a composite property of "MissionEffective" and "ResourceUtilization"*)
    ; af: MissionEffective System Stakeholder Context sys me_sh_cx /\
           ResourceUtilization System Context sys ru_cx
    (* affordable is a composite property of "Dependable" and "Flexible"*)
    ; rs: Dependable System Context sys dp_cx  /\
           Flexible System Context sys fl_cx 
}.