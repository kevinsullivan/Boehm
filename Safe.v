(** Safety General Theory *)
Require Export System.

Inductive Safe {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSafetyRequirement:
    (exists safe: System msys -> Prop, safe sys) -> Safe sys.
