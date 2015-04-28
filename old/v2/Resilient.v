(** ** RESILIENT MODULE*)
(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(** Modules are imported here for defining a composite attribute, [Resilient].**)
Require Import System.
Require Import Context.
Require Import Stakeholder.
Require Import Dependability.
Require Import Flexibility.

Module Resilient.
(**
Here we define [Resilient] as a composite attribute.
A system is resilient only if it is dependable and flexible.
*)
  Inductive Resilient (s: System.System): Prop :=
    mk_resilient: Dependable.Dependable s -> Flexible.Flexible s -> Resilient s.

End Resilient.
