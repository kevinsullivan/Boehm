import SystemModel.System
import Qualities.Affordable
import Qualities.Resilient

/- Satisfactory -/
/-
An instance of type [SystemType]  is satisfactory if, and only if,
 it is both [Affordable] and [Resilient].  These
system qualities are themselves composites of lower-level system
qualities, as detailed in their respective files.
-/

inductive Satisfactory (sys_type: SystemType) : Prop
| intro : Affordable sys_type -> 
	      Resilient sys_type ->
          Satisfactory

