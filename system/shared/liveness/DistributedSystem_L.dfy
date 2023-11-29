include "Defs_L.dfy"
include "UBosco_L.dfy"
include "Network_L.dfy"
include "../abstr/DistributedSystem_A.dfy"

abstract module DistributedSystem_L refines DistributedSystem_A {

	import opened Defs_L
	import opened UBosco : UBosco_L
	import Network = Network_L

	lemma quorum_nonempty_placeholder(QS : QuorumSystem, qR : set<nat>)
		requires QSystem.valid_quorum_system(QS)
		requires qR in QS.C.Q
		ensures qR != {}
	
	method instantiate_qR(S : seq<Process>, QS : QuorumSystem)
		returns (qR : set<nat>)
		requires valid_distributed_system(S, QS)
		ensures valid_qR(S, QS, qR)
	{
		qR :| qR in QS.C.Q && qR <= QS.R;
		quorum_nonempty_placeholder(QS, qR);
		var j :| j in qR;
		assert 0 <= j < |S|;
		assert S[j].id == j;
	}

	/* Live Network step */
	
	predicate network_step_enabled(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem)
	{
		i in QS.R
		&& Network.step_enabled(S, i, qR, QS)
	}

	predicate network_step(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, S' : seq<Process>)
		requires network_step_enabled(S, i, qR, QS)
	{
		Network.step(S, i, qR, QS, S')
	}
 
	lemma valid_system_is_valid_network(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
		ensures Network.valid_network(S)
		ensures Network.valid_network_impl(S)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess?
			ensures forall r :: started_rnd(S[i], r) ==> (exists msg | msg in S[i].outbox :: msg.rnd == r)
		{
			forall r : nat | started_rnd(S[i], r)
				ensures exists msg | msg in S[i].outbox :: msg.rnd == r
			{
				assert 0 <= r <= S[i].rnd;
				assert Message(S[i].id, S[i].val_hist[r], r) in S[i].outbox;
			}
		}
	}

	lemma network_step_preserves_invariants(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires network_step_enabled(S, i, qR, QS)
		requires network_step(S, i, qR, QS, S')
		ensures valid_distributed_system(S', QS)
		ensures valid_distributed_system_impl(S', QS)
	{
		valid_system_is_valid_network(S, QS);
		Network.step_preserves_invariants(S, i, qR, QS, S');
		forall j | 0 <= j < |S'|
			ensures valid_distributed_system_single(S', QS, S'[j], j)
		{
			if (j != i) {
				assert valid_distributed_system_single(S, QS, S[j], j);
				assert S[j] == S'[j];
			} else {
				assert valid_distributed_system_single(S, QS, S[i], i);
				assert Network.only_change_inbox(S, S', i);
				assert S[i].inbox <= S'[i].inbox;
			}
		}
		assume valid_distributed_system_impl(S', QS);
	}

	lemma network_step_ensures_msgs_from_quorum(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires network_step_enabled(S, i, qR, QS)
		requires network_step(S, i, qR, QS, S')
		ensures has_msgs_from_quorum(S'[i], QS.C.Q)
	{}

	method network_step_impl(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem) returns (S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires network_step_enabled(S, i, qR, QS)
		ensures network_step(S, i, qR, QS, S')
	{
		valid_system_is_valid_network(S, QS);
		S' := Network.step_impl(S, i, qR, QS);
	}

	/* Safe Network step */

	lemma live_network_step_refines_safe_network_step(S : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires network_step_enabled(S, i, qR, QS)
		requires network_step(S, i, qR, QS, S')
		ensures Network.safe_step(S, S')
	{
		valid_system_is_valid_network(S, QS);
		Network.live_step_refines_safe_step(S, i, qR, QS, S');
	}

	lemma safe_network_step_preserves_invariants(S : seq<Process>, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires Network.safe_step(S, S')
		ensures valid_distributed_system(S', QS)
		ensures valid_distributed_system_impl(S', QS)
	{
		valid_system_is_valid_network(S, QS);
		Network.safe_step_preserves_invariants(S, S');
		assume valid_distributed_system_impl(S', QS);
	}
	
	/* Non-Byzantine process step */

	predicate nonbyzantine_process_step_enabled(S : seq<Process>, i : nat)
	{
		0 <= i < |S|
		&& S[i].NBProcess?
		&& UBosco.step_enabled(S[i])	
	}

	predicate nonbyzantine_process_step<T(!new), S>(S : seq<Process>, i : nat, S' : seq<Process>)
		requires 0 <= i < |S|
	{
		|S| == |S'|
		&& (forall j :: 0 <= j < |S'| && i != j ==> S'[j] == S[j])
		&& exists pr, q, oq :: UBosco.step(S[i], S'[i], pr, q, oq)
	}

	lemma	nonbyzantine_process_step_preserves_invariants(S : seq<Process>, i : nat,  QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires nonbyzantine_process_step_enabled(S, i)
		requires nonbyzantine_process_step(S, i, S')
		ensures valid_distributed_system(S', QS)
		ensures valid_distributed_system_impl(S', QS)
	{
		assert exists pr, q, oq :: UBosco.step(S[i], S'[i], pr, q, oq);
		var pr, q, oq :| UBosco.step(S[i], S'[i], pr, q, oq);
		UBosco.step_preserves_invariants(S[i], S'[i], pr, q, oq);
		assume valid_distributed_system_impl(S', QS);
	}

	method nonbyzantine_process_step_impl(S : seq<Process>, i : nat, QS : QuorumSystem) returns (S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires S[i].NBProcess?
		requires nonbyzantine_process_step_enabled(S, i)
		ensures nonbyzantine_process_step(S, i, S')
	{
		S' := S;
		var ub', pr, q, oq  := UBosco.step_impl(S[i]);
		S' := S'[i := ub'];
		assert UBosco.step(S[i], S'[i], pr, q, oq);
		assert nonbyzantine_process_step(S, i, S');
	}
}

	
