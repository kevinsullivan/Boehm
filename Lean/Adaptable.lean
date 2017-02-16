import System

inductive Adaptable (sys_type: SystemType): Prop
| intro : (exists adaptable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, adaptable c p s st) ->
          Adaptable
