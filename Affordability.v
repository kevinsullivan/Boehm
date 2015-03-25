(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(** 
Import [CpdtTactics] moduel to use [crush] tactic. 
*)
Require Import CpdtTactics.

Require Import DataType.
Require Import MissionEffective.
Require Import ResourceUtilization.

(** ** AFFORDABLE**)
(**
[Affordability] is a composite attribute of [MissionEffective] and [ResourceUtilization].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [ResourceUtilization].
*)
Inductive Affordable (s: System): Prop :=
    mk_affordability: MissionEffective s -> ResourceUtilization s -> Affordable s.

(** ** Asserting and proving that [aSystem] [isAffordable]. *)
Theorem aSystemisAffordable : Affordable aSystem.
apply mk_affordability.
(** We here provide proofs for two sub-attributes*)
(** Here we apply the proof that are already proved in module [MissionEffective]*)
apply aSystemisMissionEffective.
(** Here we apply the proof that are already proved in module [ResourceUtilization]*)
apply aSystemisResourceUtilization.
Qed.