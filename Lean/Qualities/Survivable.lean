-- Survivable
/-
[Survivable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Dependable].
An instance of type [SystemType] is deemed [Survivable] if and only if all the requirements are satisfied.
-/

import SystemModel.System

inductive Survivable (sys_type: SystemType): Prop
| intro : (exists survivable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, survivable c p s st) ->
          Survivable
