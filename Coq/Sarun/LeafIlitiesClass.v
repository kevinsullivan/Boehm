Require Import System.

(** This is a class to represent a low-level ilities (Leaf)
    In order to construct a Leaf ilities, we need to provide
      1) requirement of the ilities
      2) proof that the requirement of the ilities is satified
*)
Class LeafIlities (R : Type) (sys_type : SystemType) :=
{
  requirement: Contexts sys_type ->
               Phases sys_type ->
               Stakeholders sys_type ->
               @SystemInstance sys_type -> Prop;
  proof : forall c: Contexts sys_type,
          forall p: Phases sys_type,
          forall s: Stakeholders sys_type,
          forall st: @SystemInstance sys_type,
              requirement c p s st
}.