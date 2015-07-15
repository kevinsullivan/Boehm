Require Export Quality.
Require Export Value.
Require Export Example_Parnas_Functional_Decomposition.
Require Export BoehmTactics.

Definition corpusChangeActionSpec (trigger: kwicAssertion) (agent: kwicStakeholders) (pre post: kwicSystemState): Prop  :=  
        isModular_wrt corpus pre /\ (trigger = corpusPreState /\ agent = customer /\ corpusPre pre /\ inMaintenancePhase pre ->
        corpusPost post /\ modulesChanged (value post) <= modulesChanged (value pre) + 1).

Theorem verifyChangeCorpus: ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre customer) costomerChangeCorpus.
Proof.
(* Should not be proved *)