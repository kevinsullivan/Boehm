-- Manufacturable 
/-
[Manufacturable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Efficient].
An instance of type [SystemType] is deemed [Manufacturable] if and only if all the requirements are satisfied.
-/

import SystemModel.System

inductive Manufacturable (sys_type: SystemType): Prop
| intro : (exists manufacturable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, manufacturable c p s st) ->
          Manufacturable
