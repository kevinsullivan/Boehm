-- Endurable 
/-
[Endurable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [MissionEffective].
An instance of type [SystemType] is deemed [Endurable] if and only if all the requirements are satisfied.
-/

import System.System

inductive Endurable (sys_type: SystemType): Prop
| intro : (exists endurable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, endurable c p s st) ->
          Endurable
