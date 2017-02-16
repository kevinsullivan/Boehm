import System
import PhysicalCapable
import CyberCapable
import HumanUsable
import Speed
import Endurable
import Maneuverable
import Accurate
import Impactful
import Scalable
import Versatile
import Interoperable

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