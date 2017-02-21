import SystemModel.System

/- Convenience Aliasing -/
definition valueType {sys_type : SystemType} := sys_type^.ValueType
record Value {sys_type : SystemType} := 
mk :: (value_cost: (@valueType sys_type)) (value_benefit: (@valueType sys_type))

/-
 - Note that what we really need here is a more sophisticated accounting system.
 -/
