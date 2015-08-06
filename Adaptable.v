(** Adaptable *)
(**
[Adaptable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Flexible].
An instance of type [SystemType] is deemed [Adaptable] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Adaptable (sys_type: SystemType) : Prop :=
  satisfiesAdaptabilityRequirements:
    (exists adaptable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, adaptable c p s st) ->
        Adaptable sys_type.