include "../abstr/DistributedSystem_A.dfy"
include "UBosco_S.dfy"
include "Network_S.dfy"

abstract module DistributedSystem_S refines DistributedSystem_A {

	import opened UBosco : UBosco_S
	import Network : Network_S

	/* Network step */
	
	predicate network_step(S : seq<Process>, QS : QuorumSystem, S' : seq<Process>)
	{
		Network.step(S, S')
	}

	lemma network_step_preserves_invariants(S : seq<Process>, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires network_step(S, QS, S')
		ensures valid_distributed_system(S', QS)
		ensures valid_distributed_system_impl(S', QS)
	{
		Network.step_preserves_invariants(S, S');
		assume valid_distributed_system_impl(S', QS);
	}

	method network_step_impl(S : seq<Process>, QS : QuorumSystem) returns (S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		ensures network_step(S, QS, S')
	{
		S' := Network.step_impl(S);
	}

	/* Non-Byzantine process step */
	
	predicate nonbyzantine_process_step(S : seq<Process>, i : nat, QS : QuorumSystem, S' : seq<Process>, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires 0 <= i < |S|
	{
		|S| == |S'|
		&& (forall j :: 0 <= j < |S'| && i != j ==> S'[j] == S[j])
		&& UBosco.step(S[i], S'[i], pr, q, oq)	
	}

	lemma nonbyzantine_process_step_preserves_invariants(S : seq<Process>, i : nat,  QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires exists pr, q, oq :: nonbyzantine_process_step(S, i, QS, S', pr, q, oq)
		ensures valid_distributed_system(S', QS)
		ensures valid_distributed_system_impl(S', QS)
	{
		forall j | 0 <= j < |S'|
			//ensures Network.valid_network_single(S', S'[j], j)
			ensures valid_distributed_system_single(S', QS, S'[j], j)
		{
			if i == j {
				assert exists pr, q, oq :: UBosco.step(S[i], S'[i], pr, q, oq);
				var pr, q, oq :| UBosco.step(S[i], S'[i], pr, q, oq);
		
				UBosco.step_preserves_invariants(S[i], S'[i], pr, q, oq);
			} else {
				assert S'[j] == S[j];
			}
		}		
		assume valid_distributed_system_impl(S', QS);
	}

	method nonbyzantine_process_step_impl(S : seq<Process>, i : nat, QS : QuorumSystem) returns (S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires S[i].NBProcess?
		ensures exists pr, q, oq :: nonbyzantine_process_step(S, i, QS, S', pr, q, oq)
	{
		S' := S;
		var ub', pr, q, oq := UBosco.step_impl(S[i]);
		S' := S'[i := ub'];
		assert nonbyzantine_process_step(S, i, QS, S', pr, q, oq);
	}
}