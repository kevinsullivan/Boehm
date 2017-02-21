-- OtherScarceResources
/-
[OtherScarceResources] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Efficient].
-/

import ..System.System

inductive OtherScarceResources (sys_type: SystemType): Prop
| intro : (exists otherScarceResources: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, otherScarceResources c p s st) ->
          OtherScarceResources
