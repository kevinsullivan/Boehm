(**
"<who> needs to be able to change <what> <when> <why>"
*)
Require Export System.

Section Changeable.

  Variable msys : MetaSystem.

  (** Convenience Aliasing *)
  Definition stakeholders := (stakeholders msys).
  Definition resources := (resources msys).
  Definition phases := (phases msys).
  Definition contexts := (contexts msys).
  Definition system_type := (system_type msys).
  
  (** TODO: Some sort of quantifying value in Cost and Benefit? *)
  Inductive Cost := 
    | cost_simple: resources -> Cost.

  Inductive Benefit :=
    | benefit_simple: resources -> Benefit.

  Record Value := mk_value {
    cost: Cost;
    benefit: Benefit 
  }.

  Definition Assertion := system_type -> Prop.

  Definition Action := system_type -> system_type.

  Record Change := mk_change {
    changePrecondition: Assertion;
    changeAction: Action;
    changePostcondition: Assertion
  }.

  Record ChangeRequirement : Type := mkChangeRequirement {
    trigger: Assertion;
    sh: stakeholders;
    change: Change;
    value: Value -> Prop
  }.

  Inductive Changeable (sys: System msys) : Prop :=
    satisfiesChangeabilityRequirement:
      (exists changeable: System msys -> Prop, changeable sys) ->
      Changeable sys.

End Changeable.
