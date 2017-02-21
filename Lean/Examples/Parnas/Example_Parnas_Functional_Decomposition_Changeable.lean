import Qualities.Satisfactory
import System.Value
import Examples.Parnas.Example_Parnas_Functional_Decomposition

definition corpusChangeActionSpec (trigger: kwicAssertion) (agent: kwicStakeholders) (pre post: kwicSystemState): Prop  :=  
        --isModular_wrt corpus pre /\ 
        (trigger = corpusPreState /\ agent = kwicStakeholders.customer /\ corpusPre pre /\ inMaintenancePhase pre ->
        corpusPost post /\ post^.value^.modulesChanged <= pre^.value^.modulesChanged + 1)

theorem verifyChangeCorpus: ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre kwicStakeholders.customer) costomerChangeCorpus :=
sorry