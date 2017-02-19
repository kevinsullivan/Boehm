(** Modifiable *)
(**
[Modifiable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Flexible].
An instance of type [SystemType] is deemed [Modifiable] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Modifiable (sys_type: SystemType) : Prop :=
  satisfiesModifiabilityRequirements:
    (exists modifiable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, modifiable c p s st) ->
        Modifiable sys_type.