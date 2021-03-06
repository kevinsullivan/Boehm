(** * AFFORDABLE *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(**
 [Affordability] is a composite attribute of [MissionEffective] and [ResourceUtilization].
 A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [ResourceUtilization].
*)
Require Import System.
Require Import MissionEffective.
Require Import ResourceUtilization.

Module Affordable.
  Inductive Affordable (s: System.System): Prop :=
    mk_affordability: 
        MissionEffective.MissionEffective s -> ResourceUtilization.ResourceUtilization s -> Affordable s.

End Affordable.
