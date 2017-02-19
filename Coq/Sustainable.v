(** Sustainable *)
(**
[Sustainable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Efficient].
An instance of type [SystemType] is deemed [Sustainable] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Sustainable (sys_type: SystemType) : Prop :=
  satisfiesSustainabilityRequirements:
    (exists sustainable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, sustainable c p s st) ->
        Sustainable sys_type.