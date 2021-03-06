import Qualities.Satisfactory
import SystemModel.Value
import Examples.Parnas.Functional_Decomposition

definition corpusChangeActionSpec (trigger: kwicAssertion) (agent: kwicStakeholders) (pre post: kwicSystemState): Prop  :=  
        isModular_wrt kwicParameter.corpus pre /\ 
        (trigger = corpusPreState /\ agent = kwicStakeholders.customer /\ corpusPre pre /\ inMaintenancePhase pre ->
        corpusPost post /\ post^.value^.modulesChanged <= pre^.value^.modulesChanged + 1)

theorem verifyChangeCorpus: ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre kwicStakeholders.customer) costomerChangeCorpus :=
sorry