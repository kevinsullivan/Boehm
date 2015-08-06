(** Safe *)
(**
[Safe] is parameterized by an instance of type [SystemType], and it's a sub-attribute to [Dependable].
An instance of type [SystemType] is deemed [Safe] if and only if all the requirements are satisfied.
*)

Require Export System.

Inductive Safe (sys_type: SystemType) : Prop :=
  satisfiesSafetyRequirements:
    (exists safe: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, safe c p s st) ->
        Safe sys_type.