include "../Types.dfy"
include "Defs_L.dfy"
include "DistributedSystem_L.dfy"

abstract module Execution_L {

	import opened Types
	import opened Defs_L
	import opened DistributedSystem : DistributedSystem_L
	//import Network : DistributedSystem.Network

	/* System step */

	predicate system_step(S : seq<Process>, S' : seq<Process>)
	{
		// use the safe network step to specify valid executions
		// (we don't want to expose the details of how Network_L implements the network step)
		Network.safe_step(S, S') 
		|| (exists i | nonbyzantine_process_step_enabled(S, i) :: nonbyzantine_process_step(S, i, S'))
	}

	/* Proofs */

	lemma {:opaque} system_step_valid_qR(S : seq<Process>, S' : seq<Process>, QS : QuorumSystem, qR : set<nat>)
		requires system_step(S, S')
		requires valid_qR(S, QS, qR)
		ensures valid_qR(S', QS, qR)
	{
		if (Network.safe_step(S, S')) {
			
		} else {
			assert exists i | nonbyzantine_process_step_enabled(S, i) :: nonbyzantine_process_step(S, i, S');
		}
	}
	
	lemma {:opaque} system_step_preserves_invariants(S : seq<Process>, S' : seq<Process>, QS : QuorumSystem)
		requires system_step(S, S')
		requires DistributedSystem.valid_distributed_system(S, QS)
		requires DistributedSystem.valid_distributed_system_impl(S, QS)
		ensures DistributedSystem.valid_distributed_system(S', QS)
		ensures DistributedSystem.valid_distributed_system_impl(S', QS)
	{
		if (Network.safe_step(S, S')) {
			safe_network_step_preserves_invariants(S, QS, S');
		} else {
			assert exists i | nonbyzantine_process_step_enabled(S, i) :: nonbyzantine_process_step(S, i, S');
			var i :| nonbyzantine_process_step_enabled(S, i) && nonbyzantine_process_step(S, i, S');
			nonbyzantine_process_step_preserves_invariants(S, i, QS, S');
		}
	}
	
	/* Valid execution */

	predicate valid_execution(S : seq<Process>, S' : seq<Process>, Exec : seq<seq<Process>>, QS : QuorumSystem)
	{
		|Exec| >= 1
		&& Exec[0] == S
		&& Exec[|Exec| - 1] == S'
	  && DistributedSystem.valid_distributed_system(S, QS)
		&& DistributedSystem.valid_distributed_system_impl(S, QS)
	  && (forall n :: 0 <= n < |Exec| - 1 ==> system_step(Exec[n], Exec[n + 1]))
	}

	/* Proofs */

	lemma 
	{:fuel system_step<T, S>, 0, 0} 
	{:opaque} 
	valid_execution_append<T, S>(Exec : seq<seq<Process>>, S0 : seq<Process>, S1 : seq<Process>, S2 : seq<Process>, QS : QuorumSystem)
		requires valid_execution(S0, S1, Exec, QS)
		requires system_step(S1, S2)
		ensures valid_execution(S0, S2, Exec + [S2], QS)
	{}

	lemma
	{:fuel system_step<T, S>, 0, 0} 
	{:opaque} 
	valid_execution_pop<T, S>(Exec : seq<seq<Process>>, S0 : seq<Process>, S1 : seq<Process>, QS : QuorumSystem)
		requires valid_execution(S0, S1, Exec, QS)
		requires |Exec| > 1
		ensures valid_execution(Exec[1], S1, Exec[1..], QS)
	{
		assert system_step(S0, Exec[1]);
		system_step_preserves_invariants(S0, Exec[1], QS);
	}

	lemma
	{:fuel system_step<T, S>, 0, 0}
	valid_execution_concat<T, S>(Exec0 : seq<seq<Process>>, Exec1: seq<seq<Process>>, S0 : seq<Process>, S1 : seq<Process>, S2 : seq<Process>, QS : QuorumSystem)
		requires valid_execution(S0, S1, Exec0, QS)
		requires valid_execution(S1, S2, Exec1, QS)
		ensures valid_execution(S0, S2, Exec0 + Exec1[1..], QS)
		decreases |Exec1|
	{
		if |Exec1| == 1 {

		} else {
			assert Exec0[|Exec0| - 1] == Exec1[0] == S1;
			valid_execution_pop(Exec1, S1, S2, QS);
			valid_execution_concat(Exec0 + [Exec1[1]], Exec1[1..], S0, Exec1[1], S2, QS);
		}
	}


	lemma
	{:opaque}
	{:fuel system_step<T, S>, 0, 0}
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel valid_qR<T, S>, 0, 0}
		valid_execution_lemma<T, S>(S : seq<Process>, S' : seq<Process>, Exec : seq<seq<Process>>, QS : QuorumSystem, qR : set<nat>)
		requires valid_execution(S, S', Exec, QS)
		requires valid_qR(S, QS, qR)
		ensures forall n :: 0 <= n <= |Exec| - 1 ==> DistributedSystem.valid_distributed_system(Exec[n], QS)
		ensures forall n :: 0 <= n <= |Exec| - 1 ==> DistributedSystem.valid_distributed_system_impl(Exec[n], QS)
		ensures forall n :: 0 <= n <= |Exec| - 1 ==> valid_qR(Exec[n], QS, qR)
		ensures forall n :: 0 <= n <= |Exec| - 1 ==> same_ids_nondecr_rnds(S, Exec[n])
	{
		var n := 0;
		while n < |Exec| - 1
			invariant 0 <= n <= |Exec| - 1
			invariant forall i :: 0 <= i <= n ==> DistributedSystem.valid_distributed_system(Exec[i], QS)
			invariant forall i :: 0 <= i <= n ==> DistributedSystem.valid_distributed_system_impl(Exec[i], QS)
			invariant forall i :: 0 <= i <= n ==> valid_qR(Exec[i], QS, qR)
			invariant forall i :: 0 <= i <= n ==> same_ids_nondecr_rnds(S, Exec[i])
			decreases (|Exec| - 1) - n
		{
			assert system_step(Exec[n], Exec[n + 1]);
			system_step_preserves_invariants(Exec[n], Exec[n + 1], QS);
			system_step_valid_qR(Exec[n], Exec[n + 1], QS, qR);
			system_step_same_ids_nondecr_rnds(Exec[n], Exec[n + 1]);
			n := n + 1;
		}
	}

	lemma
	{:opaque}
	{:fuel system_step<T, S>, 0, 0}
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel valid_qR<T, S>, 0, 0}
		valid_execution_tl_lemma<T, S>(S : seq<Process>, S' : seq<Process>, Exec : seq<seq<Process>>, QS : QuorumSystem, qR : set<nat>)
		requires valid_execution(S, S', Exec, QS)
		requires valid_qR(S, QS, qR)
		ensures DistributedSystem.valid_distributed_system(S', QS)
		ensures DistributedSystem.valid_distributed_system_impl(S', QS)
		ensures valid_qR(S', QS, qR)
		ensures same_ids_nondecr_rnds(S, S')
	{
		valid_execution_lemma(S, S', Exec, QS, qR);
	}

	/* Helpers */

	predicate same_ids_rnds(S : seq<Process>, S' : seq<Process>) 
	{
		|S| == |S'|
		&& (forall i :: 0 <= i < |S| ==> S[i].id == S'[i].id)
		&& (forall i :: 0 <= i < |S| ==> (S[i].NBProcess? <==> S'[i].NBProcess?))
		&& (forall i :: 0 <= i < |S| && S[i].NBProcess? ==> S[i].rnd == S'[i].rnd)
	}

	lemma safe_network_step_same_ids_rnds(S : seq<Process>, QS : QuorumSystem, S' : seq<Process>) 
		requires valid_distributed_system(S, QS)
		requires DistributedSystem.Network.safe_step(S, S')
		ensures same_ids_rnds(S, S')
	{}

	predicate same_ids_rnds_incr_single(S : seq<Process>, j : nat, S' : seq<Process>)
	{
		|S| == |S'|
		&& 0 <= j < |S|
		&& S[j].NBProcess?
		&& (forall i :: 0 <= i < |S| ==> S[i].id == S'[i].id)
		&& (forall i :: 0 <= i < |S| ==> (S[i].NBProcess? <==> S'[i].NBProcess?))
		&& (forall i :: 0 <= i < |S| && S[i].NBProcess? && i != j ==> S[i].rnd == S'[i].rnd)
		&& S'[j].rnd == S[j].rnd + 1
	}

	lemma process_step_same_ids_rnds_incr_single(S : seq<Process>, j : nat, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires nonbyzantine_process_step_enabled(S, j)
		requires nonbyzantine_process_step(S, j, S')
		ensures same_ids_rnds_incr_single(S, j, S')
	{}

	predicate same_ids_nondecr_rnds(S : seq<Process>, S' : seq<Process>)
	{
		|S| == |S'|
		&& (forall i :: 0 <= i < |S| ==> S[i].id == S'[i].id)
		&& (forall i :: 0 <= i < |S| ==> (S[i].NBProcess? <==> S'[i].NBProcess?))
		&& (forall i :: 0 <= i < |S| && S[i].NBProcess? ==> S[i].rnd <= S'[i].rnd)
	}

	lemma {:opaque} system_step_same_ids_nondecr_rnds(S : seq<Process>, S' : seq<Process>)
		requires system_step(S, S')
		ensures same_ids_nondecr_rnds(S, S')
	{
		if (Network.safe_step(S, S')) {
			
		} else {
			assert exists i | nonbyzantine_process_step_enabled(S, i) :: nonbyzantine_process_step(S, i, S');
		}
	}
}
