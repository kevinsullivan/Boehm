-- Speed 
/-
[Speed] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [MissionEffective].
-/


import SystemModel.System

inductive Speed (sys_type: SystemType): Prop
| intro : (exists speed: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, speed c p s st) ->
          Speed
