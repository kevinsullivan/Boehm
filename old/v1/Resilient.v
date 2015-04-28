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

Require Import Dependability.

Require Import Flexibility.

(** ** RESILIENT**)
(**
Here we define [Resilient] as another composite attribute.
A system is resilient only if it is dependable and flexible.
*)
Inductive Resilient (s: System): Prop :=
  mk_resilient: Dependable s -> Flexible s -> Resilient s.

(** ** Asserting and proving that [aSystem] [isResilient]. *)
Theorem aSystemisResilient : Resilient aSystem.
apply mk_resilient.
(** Here we prove the first sub-attribute: dependable*)
apply aSystemisDependable.
apply aSystemIsFlexible.
Qed.