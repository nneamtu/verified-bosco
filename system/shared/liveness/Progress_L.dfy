include "../Types.dfy"
include "Defs_L.dfy"
include "Execution_L.dfy"

/* This module is used to demonstrate that at any point in the execution,
   there exists a sequence of steps that can be taken which results in
   any given correct process having messages from a quorum (for its current
   round) in its inbox. */
abstract module Progress_L {

	/* The proof that establishes the existence of such a sequence of steps works 
	   as follows:
		 - begin with a correct process i, to which we would like to have the 
		   messages from a quorum delivered 
		 - take a quorum qR that contains only correct processes (which is guaranteed
		   to exist)
		 - now take the subset of processes in qR that have a lower round number
		   than process i: allow them to "catch up" until they all have reached
			 the same round as i (see below for more)
		 - now deliver the messages for i's current round from qR to i; thus, process
		   has messages from a quorum */

	/* The ability of the processes in qR to "play catch up" to process i rests on
	   the fact (i) that all of the processes in qR are non-faulty, and (ii) the 
		 network is assumed to be reliable. 
		 
		 So, the process with the lowest round number in qR (referred to as process j) 
		 will eventually receive enough messages so that it can complete its current
		 round (since it is guaranteed to at least receive messages from all of the 
		 processes in qR). Once this is done, qR will have gotten a bit closer to 
		 catching up to process i. Thus, all of the processes in qR will eventually
		 catch up to process i, as the above sequence of events will simply be 
		 repeated with the new process with the lowest round number in qR. */

	import opened Types
	import opened Defs_LProof
	import opened Execution : Execution_L
	
	/* Instantiate process id of a process in qR that has the minimum round number in qR. */
	method instantiate_j(S0 : seq<Process>, QS : QuorumSystem, qR : set<nat>, ghost i : nat, ghost rnd_i : nat)
		returns (j : nat)
		requires DistributedSystem.valid_distributed_system(S0, QS)
		requires sum_rnd_subset(S0, qR) < sum_rnd_replace_subset(S0, qR, rnd_i)
		requires valid_qR(S0, QS, qR)
		requires 0 <= i < |S0|
		requires S0[i].NBProcess?
		requires S0[i].rnd == rnd_i
		ensures 0 <= j < |S0|
		ensures S0[j].NBProcess?
		ensures j in qR
		ensures S0[j].id == j
		ensures S0[j].rnd == min_rnd_subset(S0, qR)
		ensures j != i
	{
		Defs_LProof.min_rnd_lt_if_sum_rnd_lt(S0, qR, rnd_i);
		var p_j := Defs_LProof.instantiate_min_rnd_subset(S0, qR);
		j := p_j.id;
		assert j in qR;
	}

	/* Step S0 so that j receives messages for its current round from the processes in qR.  */
	method
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel has_msgs_from_quorum<T, S>, 0, 0}
	{:fuel DistributedSystem.Network.step<T, S>, 0, 0}
	{:fuel DistributedSystem.Network.safe_step<T, S>, 0, 0}
		step_S0<T(==), S>(S0 : seq<Process>, j : nat, qR : set<nat>, QS : QuorumSystem) returns (S1 : seq<Process>)
		requires DistributedSystem.valid_distributed_system(S0, QS)
		requires DistributedSystem.valid_distributed_system_impl(S0, QS)
		requires valid_qR(S0, QS, qR)
		requires 0 <= j < |S0|
		requires S0[j].NBProcess?
		requires j in qR
		requires S0[j].rnd == min_rnd_subset(S0, qR)
		ensures same_ids_rnds(S0, S1)
		ensures system_step(S0, S1)
		ensures has_msgs_from_quorum(S1[j], QS.C.Q)
	{
		S1 := DistributedSystem.network_step_impl(S0, j, qR, QS);
		DistributedSystem.network_step_ensures_msgs_from_quorum(S0, j, qR, QS, S1);
		DistributedSystem.live_network_step_refines_safe_network_step(S0, j, qR, QS, S1);
		Execution.safe_network_step_same_ids_rnds(S0, QS, S1);
	}


	/* Step S1 so that j takes a process step (i.e. completes its current round). */
	method
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel has_msgs_from_quorum<T, S>, 0, 0}
		step_S1<T(==), S>(S0 : seq<Process>, S1 : seq<Process>, j : nat, qR : set<nat>, QS : QuorumSystem) returns (S2 : seq<Process>)
		requires DistributedSystem.valid_distributed_system(S0, QS)
		requires DistributedSystem.valid_distributed_system_impl(S0, QS)
		requires 0 <= j < |S1|
		requires S1[j].NBProcess?
		requires j in qR
		requires same_ids_rnds(S0, S1)
		requires system_step(S0, S1)
		requires has_msgs_from_quorum(S1[j], QS.C.Q)
		ensures same_ids_rnds_incr_single(S1, j, S2)
		ensures system_step(S1, S2)
	{
		Execution.system_step_preserves_invariants(S0, S1, QS);
		S2 := DistributedSystem.nonbyzantine_process_step_impl(S1, j, QS);
		Execution.process_step_same_ids_rnds_incr_single(S1, j, QS, S2);
	}
	
	method update_exec(Exec : seq<seq<Process>>, ghost S : seq<Process>, ghost S0 : seq<Process>, S1 : seq<Process>, S2 : seq<Process>, ghost QS : QuorumSystem, ghost j : nat)
		returns (Exec' : seq<seq<Process>>) 
		requires system_step(S0, S1)
		requires system_step(S1, S2)
		requires valid_execution(S, S0, Exec, QS)
		ensures valid_execution(S, S2, Exec', QS)
	{
		valid_execution_append(Exec, S, S0, S1, QS);
		Exec' := Exec + [S1];
		valid_execution_append(Exec', S, S1, S2, QS);
		Exec' := Exec' + [S2];
	}

	/* Step S0 to S2 such that j completes its current round; append new steps to the execution. */
	method
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel valid_qR<T, S>, 0, 0}
	{:fuel valid_execution<T, S>, 0, 0}
	{:fuel has_msgs_from_quorum<T, S>, 0, 0}
		step_j<T(==), S>(S0 : seq<Process>, j : nat, qR : set<nat>, QS : QuorumSystem, Exec : seq<seq<Process>>, ghost S : seq<Process>)
		returns (S2 : seq<Process>, Exec' : seq<seq<Process>>)
		requires DistributedSystem.valid_distributed_system(S0, QS)
		requires DistributedSystem.valid_distributed_system_impl(S0, QS)
		requires valid_qR(S0, QS, qR)
		requires 0 <= j < |S0|
		requires S0[j].NBProcess?
		requires j in qR
		requires S0[j].id == j
		requires S0[j].rnd == min_rnd_subset(S0, qR)
		requires valid_execution(S, S0, Exec, QS)
		ensures same_ids_rnds_incr_single(S0, j, S2)
		ensures valid_execution(S, S2, Exec', QS)
	{
		var S1 := step_S0(S0, j, qR, QS);
		S2 := step_S1(S0, S1, j, qR, QS);
		Exec' := update_exec(Exec, S, S0, S1, S2, QS, j);
	}

	lemma {:opaque} sum_rnd_help(S0 : seq<Process>, S2 : seq<Process>, QS : QuorumSystem, j : nat, qR : set<nat>, rnd : nat)
		requires same_ids_rnds_incr_single(S0, j, S2)
		requires 0 <= j < |S0|
		requires S0[j].NBProcess?
		requires j in qR
		requires S0[j].id == j
		requires sum_rnd_subset(S0, qR) < sum_rnd_replace_subset(S0, qR, rnd)
		requires S0[j].rnd == min_rnd_subset(S0, qR)
		ensures sum_rnd_replace_subset(S2, qR, rnd) == sum_rnd_replace_subset(S0, qR, rnd)
		ensures sum_rnd_subset(S2, qR) == sum_rnd_subset(S0, qR) + 1
	{
		Defs_LProof.min_rnd_lt_if_sum_rnd_lt(S0, qR, rnd);
		assert S0[j].rnd < rnd;
		Defs_LProof.sum_rnd_replace_subset_incr(S0, S2, j, qR, rnd);
		Defs_LProof.sum_rnd_incr(S0, S2, qR, j);
	}

	lemma {:opaque} min_rnd_subset_help(S0 : seq<Process>, S2 : seq<Process>, QS : QuorumSystem, j : nat, qR : set<nat>, rnd_i : nat)
		requires same_ids_rnds_incr_single(S0, j, S2)
		requires 0 <= j < |S0|
		requires S0[j].NBProcess?
		requires j in qR
		requires S0[j].id == j
		requires sum_rnd_subset(S0, qR) < sum_rnd_replace_subset(S0, qR, rnd_i)
		requires S0[j].rnd == min_rnd_subset(S0, qR)
		ensures min_rnd_subset(S2, qR) <= rnd_i
	{
		Defs_LProof.min_rnd_lt_if_sum_rnd_lt(S0, qR, rnd_i);
		assert S0[j].rnd < rnd_i;
		assert min_rnd_subset(S2, qR) <= S2[j].rnd;
	}

	method
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel min_rnd_subset<T, S>, 0, 0}
	{:fuel sum_rnd_replace_subset<T, S>, 0, 0}
	{:fuel sum_rnd_subset<T, S>, 0, 0}
	{:fuel DistributedSystem.network_step<T, S>, 0, 0}
	{:fuel DistributedSystem.nonbyzantine_process_step<T, S>, 0, 0}
	{:fuel valid_execution<T, S>, 0, 0}
	catch_up_qR<T(==), S>(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem)
		returns (S0 : seq<Process>, Exec : seq<seq<Process>>)
		requires DistributedSystem.valid_distributed_system(S, QS)
		requires DistributedSystem.valid_distributed_system_impl(S, QS)
		requires valid_execution(S, S, [S], QS)
		requires 0 <= i < |S| 
		requires S[i].NBProcess?
		requires i in QS.R
		requires valid_qR(S, QS, qR)
		requires min_rnd_subset(S, qR) < S[i].rnd
		ensures |S0| == |S|
		ensures S0[i].NBProcess?
		ensures DistributedSystem.valid_distributed_system(S0, QS)
		ensures DistributedSystem.valid_distributed_system_impl(S0, QS)
		//ensures DistributedSystem.network_step_enabled(S0, i, qR, QS);
		ensures valid_qR(S0, QS, qR)
		ensures valid_execution(S, S0, Exec, QS)
		ensures S0[i].rnd == min_rnd_subset(S0, qR)
	{
		var sum_S := sum_rnd_replace_subset(S, qR, S[i].rnd);
		var rnd_i := S[i].rnd;
		S0 := S;
		Exec := [S];
		while sum_rnd_replace_subset(S0, qR, rnd_i) > sum_rnd_subset(S0, qR)
			invariant |S0| == |S|
			invariant S0[i].NBProcess?
			invariant sum_rnd_replace_subset(S0, qR, rnd_i) == sum_S
			invariant valid_qR(S0, QS, qR);
			invariant DistributedSystem.valid_distributed_system(S0, QS)
			invariant DistributedSystem.valid_distributed_system_impl(S0, QS)
			invariant min_rnd_subset(S0, qR) <= rnd_i
			invariant S0[i].rnd == rnd_i
			invariant valid_execution(S, S0, Exec, QS)
			decreases sum_rnd_replace_subset(S0, qR, rnd_i) - sum_rnd_subset(S0, qR)
		{	
			var j := instantiate_j(S0, QS, qR, i, rnd_i);
			var S2, Exec' := step_j(S0, j, qR, QS, Exec, S); 
			sum_rnd_help(S0, S2, QS, j, qR, rnd_i);
			min_rnd_subset_help(S0, S2, QS, j, qR, rnd_i);
			S0 := S2;
			Exec := Exec';
			Execution.valid_execution_lemma(S, S0, Exec, QS, qR);
			assert valid_qR(S0, QS, qR);
			assert DistributedSystem.valid_distributed_system(S0, QS);
		}
		assert sum_rnd_replace_subset(S0, qR, rnd_i) <= sum_rnd_subset(S0, qR);
		Defs_LProof.sum_rnd_replace_subset_lte(S0, qR, rnd_i);
		Defs_LProof.sum_rnd_replace_subset_eq_iff_min_eq(S0, qR, rnd_i);
		assert S0[i].rnd == min_rnd_subset(S0, qR);
	}

	lemma encapsulate_ntk_step_enabled(S0 : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem)
		requires DistributedSystem.valid_distributed_system(S0, QS)
		requires 0 <= i < |S0|
		requires S0[i].NBProcess?
		requires valid_qR(S0, QS, qR)
		requires S0[i].rnd <= min_rnd_subset(S0, qR)
		requires i in QS.R
		ensures DistributedSystem.network_step_enabled(S0, i, qR, QS);
	{}

	method
	{:fuel DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel has_msgs_from_quorum<T, S>, 0, 0}
	{:fuel DistributedSystem.network_step_enabled<T, S>, 0, 0}
	{:fuel DistributedSystem.Network.step<T, S>, 0, 0}
	{:fuel DistributedSystem.Network.safe_step<T, S>, 0, 0}
	{:fuel valid_execution<T, S>, 0, 0}
		run_until_has_msgs_from_quorum'<T(==), S>(S : seq<Process>, i : nat, QS : QuorumSystem)
		returns (S' : seq<Process>, Exec : seq<seq<Process>>)
		requires DistributedSystem.valid_distributed_system(S, QS)
		requires DistributedSystem.valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S| 
		requires S[i].NBProcess?
		requires i in QS.R
		ensures same_ids_nondecr_rnds(S, S')
		ensures DistributedSystem.valid_distributed_system(S', QS)
		ensures DistributedSystem.valid_distributed_system_impl(S', QS)
		ensures has_msgs_from_quorum(S'[i], QS.C.Q)
		ensures valid_execution(S, S', Exec, QS)
	{
		var S0 : seq<Process>;
		var qR := DistributedSystem.instantiate_qR(S, QS);
		if (min_rnd_subset(S, qR) < S[i].rnd) {
			S0, Exec := catch_up_qR(S, i, qR, QS);
			encapsulate_ntk_step_enabled(S0, i, qR, QS);
		} else {
			S0 := S;
			Exec := [S];
			encapsulate_ntk_step_enabled(S0, i, qR, QS);
		}
		
		S' := DistributedSystem.network_step_impl(S0, i, qR, QS);
		DistributedSystem.network_step_ensures_msgs_from_quorum(S0, i, qR, QS, S');
		DistributedSystem.live_network_step_refines_safe_network_step(S0, i, qR, QS, S');
		
		valid_execution_append(Exec, S, S0, S', QS);
		Exec := Exec + [S'];
		valid_execution_tl_lemma(S, S', Exec, QS, qR);
	}

	// hide the actual value of Exec from clients
	method run_until_has_msgs_from_quorum(S : seq<Process>, i : nat, QS : QuorumSystem)
		returns (S' : seq<Process>)
		requires DistributedSystem.valid_distributed_system(S, QS)
		requires DistributedSystem.valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S| 
		requires S[i].NBProcess?
		requires i in QS.R
		ensures same_ids_nondecr_rnds(S, S')
		ensures DistributedSystem.valid_distributed_system(S', QS)
		ensures DistributedSystem.valid_distributed_system_impl(S', QS)
		ensures has_msgs_from_quorum(S'[i], QS.C.Q)
		ensures exists Exec :: valid_execution(S, S', Exec, QS)
	{
		var Exec;
		S', Exec := run_until_has_msgs_from_quorum'(S, i, QS);
	}	
}
