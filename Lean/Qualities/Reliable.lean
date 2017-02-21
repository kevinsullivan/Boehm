import ..System.System

inductive Reliable (sys_type: SystemType): Prop
| intro : (exists reliable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, reliable c p s st) ->
          Reliable
