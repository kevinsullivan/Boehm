(** Manufacturable General Theory *)
Require Export System.

Inductive Manufacturable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesManufacturabilityRequirement:
    (exists manufacturable: System msys -> Prop, manufacturable sys) -> Manufacturable sys.