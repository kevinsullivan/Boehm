(** Maintainable *)
(**
[Maintainable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Dependable].
An instance of type [SystemType] is deemed [Maintainable] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Maintainable (sys_type: SystemType) : Prop :=
  satisfiesMaintainabilityRequirements:
    (exists maintainable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, maintainable c p s st) ->
        Maintainable sys_type.