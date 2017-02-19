-- Modifiable
/-
[Modifiable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Flexible].
An instance of type [SystemType] is deemed [Modifiable] if and only if all the requirements are satisfied.
-/

import System

inductive Modifiable (sys_type: SystemType): Prop
| intro : (exists modifiable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, modifiable c p s st) ->
          Modifiable
