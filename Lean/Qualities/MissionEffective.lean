import ..System.System
import .PhysicalCapable
import .CyberCapable
import .HumanUsable
import .Speed
import .Endurable
import .Maneuverable
import .Accurate
import .Impactful
import .Scalable
import .Versatile
import .Interoperable

-- Mission Effective 
/-
[MissionEffective] is parameterized by an instance of type [SystemType]. The constituent attributes of [MissionEffective] are
the things whether it can be produced and maintained in a mission effective way.
Informally, in English:
An instance of type [SystemType] is deemed [MissionEffective] 
if and only if all the requirements of its sub-attributes are satisfied given the same conditions.
-/

inductive MissionEffective (sys_type: SystemType): Prop
| intro:
    PhysicalCapable sys_type ->
    CyberCapable sys_type ->
    HumanUsable sys_type ->
    Speed sys_type ->
    Endurable sys_type ->
    Maneuverable sys_type ->
    Accurate sys_type ->
    Impactful sys_type ->
    Scalable sys_type ->
    Versatile sys_type ->
    Interoperable sys_type ->
    MissionEffective