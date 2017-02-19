(**  Cost *)
(**
[Cost] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Efficient].
*)

Require Export System.

Inductive Cost (sys_type: SystemType) : Prop :=
  satisfiesCostRequirements:
    (exists cost: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, cost c p s st) ->
        Cost sys_type.
