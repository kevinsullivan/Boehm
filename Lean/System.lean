record SystemType :=
mk :: (Contexts : Type) (Stakeholders : Type) (Phases : Type) (ArtifactType: Type) (ValueType: Type)

record SystemInstance {sys_type: SystemType} := 
mk :: (context: (sys_type^.Contexts)) (phase: (sys_type^.Phases)) (artifact: (sys_type^.ArtifactType)) (value: (sys_type^.ValueType))
