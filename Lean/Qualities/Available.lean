-- Available 
/-
[Available] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Dependable].
An instance of type [SystemType] is deemed [Available] if and only if all the requirements are satisfied.
-/

import System

inductive Available (sys_type: SystemType): Prop
| intro : (exists available: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, available c p s st) ->
          Available
