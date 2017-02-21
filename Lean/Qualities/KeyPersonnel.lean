-- KeyPersonnel 
/-
[KeyPersonnel] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Efficient].
-/

import System

inductive KeyPersonnel (sys_type: SystemType): Prop
| intro : (exists keyPersonnel: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, keyPersonnel c p s st) ->
          KeyPersonnel
