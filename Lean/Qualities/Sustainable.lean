-- Sustainable 
/-
[Sustainable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Efficient].
An instance of type [SystemType] is deemed [Sustainable] if and only if all the requirements are satisfied.
-/

import System.System

inductive Sustainable (sys_type: SystemType): Prop
| intro : (exists sustainable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, sustainable c p s st) ->
          Sustainable
