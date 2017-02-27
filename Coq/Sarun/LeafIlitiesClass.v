Require Import System.
Class LeafIlities (R : Type) (sys_type : SystemType) :=
{
  requirement: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop;
  proof : forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, 
            requirement c p s st
}.