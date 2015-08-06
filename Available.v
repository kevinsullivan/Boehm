(** Available *)
(**
[Available] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Dependable].
An instance of type [SystemType] is deemed [Available] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Available (sys_type: SystemType) : Prop :=
  satisfiesAvailabilityRequirements:
    (exists available: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, available c p s st) ->
        Available sys_type.