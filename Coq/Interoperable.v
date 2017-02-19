(** Interoperable *)
(**
[Interoperable] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [MissionEffective].
An instance of type [SystemType] is deemed [Interoperable] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Interoperable (sys_type: SystemType) : Prop :=
  satisfiesInteroperabilityRequirements:
    (exists interoperable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, interoperable c p s st) ->
        Interoperable sys_type.