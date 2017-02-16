import System

inductive CyberCapable (sys_type: SystemType): Prop
| intro : (exists cyberCapable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, cyberCapable c p s st) ->
          CyberCapable
