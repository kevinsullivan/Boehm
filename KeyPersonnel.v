(** Key Personnel General Theory *)
Require Export System.

Inductive KeyPersonnel {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesKeyPersonnelRequirement:
    (exists key_personnel: System msys -> Prop, key_personnel sys) -> KeyPersonnel sys.