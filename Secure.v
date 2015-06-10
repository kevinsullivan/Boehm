(** Security General Theory *)
Require Export System.

Inductive Secure {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSecurityRequirement:
    (exists secure: System msys -> Prop, secure sys) ->
    Secure sys.
