(** Sustainability General Theory *)
Require Export System.

Inductive Sustainable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSustainabilityRequirement:
    (exists sustainable: System msys -> Prop, sustainable sys) -> Sustainable sys.