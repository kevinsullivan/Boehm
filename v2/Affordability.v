(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Load MissionEffective.
Load ResourceUtilization.

(** ** AFFORDABLE**)
(**
[Affordability] is a composite attribute of [MissionEffective] and [ResourceUtilization].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [ResourceUtilization].
*)
Inductive Affordable (s: System.System): Prop :=
    mk_affordability: MissionEffective.MissionEffective s -> ResourceUtilization.ResourceUtilization s -> Affordable s.

                           