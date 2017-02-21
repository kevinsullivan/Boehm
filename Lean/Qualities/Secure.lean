-- Secure 
/-
[Secure] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Dependable].
An instance of type [SystemType] is deemed [Secure] if and only if all the requirements are satisfied.
-/

import SystemModel.System

inductive Secure (sys_type: SystemType): Prop
| intro : (exists secure: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, secure c p s st) ->
          Secure
