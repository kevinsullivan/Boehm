import System.System
import Qualities.MissionEffective
import Qualities.Efficient

/- Affordable -/
/-
[Affordability] is a composite attribute of [MissionEffective] and [Efficient].
A system is [Affordable] only if it meets the requirements of both [MissionEffective] and [Efficient].
-/

inductive Affordable (sys_type: SystemType): Prop
| intro : MissionEffective sys_type ->
	      Efficient sys_type ->
          Affordable
