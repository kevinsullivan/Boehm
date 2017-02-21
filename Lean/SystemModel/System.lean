-- System Model

record SystemType :=
mk :: (Contexts : Type) (Stakeholders : Type) (Phases : Type) (ArtifactType: Type) (ValueType: Type)

/-
A system instance models a system of a particular type in a particular state.
The state includes the current context and phase, the current state of the 
artifact itself, and the current accounting/value state of the artifact.
Note that an individual stakeholder is not part of the system state, but
rather someone or something that could effect a change or be affected by 
one.
-/

record SystemInstance {sys_type: SystemType} := 
mk :: (context: (sys_type^.Contexts)) (phase: (sys_type^.Phases)) (artifact: (sys_type^.ArtifactType)) (value: (sys_type^.ValueType))
