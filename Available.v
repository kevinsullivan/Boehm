(** Available General Theory *)
Require Export System.

Inductive Available {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesAvailabilityRequirement:
    (exists available: System msys -> Prop, available sys) ->
    Available sys.
