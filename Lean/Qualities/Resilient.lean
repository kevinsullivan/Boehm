import ..System.System
import .Dependable
import .Flexible
import .Changeable

/- Resilient -/
/-
Boehm stipulates that [Resiliency] is a composite quality comprising [Dependability]
and [Flexibility]. That is, a system can be deemed to be resilient across stakeholders,
operational contexts, and lifecycle phases if it is deemed to be dependable and flexible in
all these dimensions.
The definition we give here includes [Changeable] as a sub-quality of resiliency, as
well. We have inserted this node to illustrate how we can begin to combine Boehm's
top-level taxonomy with quality-specific formal theories developed by others.
-/

inductive Resilient (sys_type: SystemType): Prop
| intro : Dependable sys_type ->
          Flexible sys_type ->
          Changeable sys_type ->
	  Resilient
