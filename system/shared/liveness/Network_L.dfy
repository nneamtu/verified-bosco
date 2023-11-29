include "Defs_L.dfy"	
include "../abstr/Network_A.dfy"

module Network_L refines Network_A {

	import opened Defs_L

	/* Invariants */

	predicate valid_network_impl(ntk : seq<Process>) 
	{
		forall i :: 0 <= i < |ntk| && ntk[i].NBProcess? ==> 
		(forall r :: started_rnd(ntk[i], r) ==> (exists msg | msg in ntk[i].outbox :: msg.rnd == r))
	}

	/* Step */

	predicate step_enabled(ntk : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem)
	{
		0 <= i < |ntk|
		&& ntk[i].NBProcess?
		&& valid_qR(ntk, QS, qR)
		&& ntk[i].rnd <= min_rnd_subset(ntk, qR)	
	}

	predicate step(ntk : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, ntk' : seq<Process>)
	  requires step_enabled(ntk, i, qR, QS)
	{
		|ntk'| == |ntk|
		&& only_change_inbox(ntk, ntk', i)
		&& ntk[i].inbox <= ntk'[i].inbox
		&& (forall msg :: msg in ntk'[i].inbox ==> 0 <= msg.src < |ntk'|)
		&& (forall msg :: msg in ntk'[i].inbox ==> (exists j :: 0 <= j < |ntk'| && msg in ntk'[j].outbox))
		&& (forall msg :: msg in ntk'[i].inbox && ntk'[msg.src].NBProcess? ==> msg in ntk'[msg.src].outbox)
		&& has_msgs_from_quorum(ntk'[i], QS.C.Q)
		&& (forall j :: 0 <= j < |ntk'| && i != j ==> ntk'[j] == ntk[j])
	}

	lemma sent_msgs_for_started_rnds(ntk : seq<Process>, ntk' : seq<Process>)
		requires |ntk| == |ntk'|
		requires forall i :: 0 <= i < |ntk'| ==> only_change_inbox(ntk, ntk', i)
		requires valid_network_impl(ntk)
		ensures valid_network_impl(ntk')
	{
		forall i | 0 <= i < |ntk'| && ntk'[i].NBProcess?
			ensures forall r :: started_rnd(ntk'[i], r) ==> (exists msg | msg in ntk'[i].outbox :: msg.rnd == r)
		{
			assert only_change_inbox(ntk, ntk', i);
			assert forall r :: started_rnd(ntk[i], r) ==> (exists msg | msg in ntk[i].outbox :: msg.rnd == r);
			assert forall r :: started_rnd(ntk[i], r) <==> started_rnd(ntk'[i], r);
			assert forall r :: started_rnd(ntk'[i], r) ==> (exists msg | msg in ntk'[i].outbox :: msg.rnd == r);
		}
	}

	lemma step_preserves_invariants(ntk : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, ntk' : seq<Process>)
		requires valid_network(ntk)
		requires valid_network_impl(ntk)
		requires step_enabled(ntk, i, qR, QS)
		requires step(ntk, i, qR, QS, ntk')
		ensures valid_network(ntk')
		ensures valid_network_impl(ntk')
	{
		sent_msgs_for_started_rnds(ntk, ntk');
	}

	function method incoming_messages...
		ensures forall j :: 0 <= j < |ntk| ==> forall msg :: msg in ntk[j].outbox ==> msg in incoming_messages(ntk)

	lemma process_has_msgs_from_quorum(ntk : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, ntk' : seq<Process>)
		requires valid_network(ntk)
		requires valid_network_impl(ntk)
		requires step_enabled(ntk, i, qR, QS)
		requires |ntk| == |ntk'|
		requires only_change_inbox(ntk, ntk', i)
		requires ntk'[i] == ntk[i].(inbox := ntk[i].inbox + incoming_messages(ntk))
		requires forall j :: 0 <= j < |ntk'| && i != j ==> ntk'[j] == ntk[j]
		ensures has_msgs_from_quorum(ntk'[i], QS.C.Q)
	{
		sent_msgs_for_started_rnds(ntk, ntk');
		assert valid_qR(ntk, QS, qR);
		forall j | j in qR
			ensures exists msg | msg in ntk'[i].inbox :: msg.rnd == ntk'[i].rnd && msg.src == j
		{
			assert 0 <= j < |ntk|;
			assert ntk[j].NBProcess?;
			assert ntk'[j].outbox <= ntk'[i].inbox;
			assert ntk'[i].rnd <= ntk'[j].rnd;
			assert started_rnd(ntk'[j], ntk'[i].rnd);
			assert exists msg | msg in ntk'[j].outbox :: msg.rnd == ntk'[i].rnd;
			var msg :| msg in ntk'[j].outbox && msg.rnd == ntk'[i].rnd;
			assert msg in ntk'[i].inbox;
		}
		assert forall j :: j in qR ==> j in (set msg | msg in ntk'[i].inbox && msg.rnd == ntk'[i].rnd :: msg.src);
		assert qR <= (set msg | msg in ntk'[i].inbox && msg.rnd == ntk'[i].rnd :: msg.src);
	}

	function method step_single(ntk : seq<Process>, i : nat, messages : set<Message>) : seq<Process>
		requires 0 <= i < |ntk|
		requires valid_network(ntk)
		ensures |ntk| == |step_single(ntk, i, messages)|
		ensures forall j :: 0 <= j < |ntk| && j != i ==> ntk[j] == step_single(ntk, i, messages)[j]
		ensures step_single(ntk, i, messages)[i].inbox == messages
	{
		ntk[i := ntk[i].(inbox := messages)]
	}

	method step_impl(ntk : seq<Process>, i : nat, ghost qR : set<nat>, ghost QS : QuorumSystem)
		returns (ntk' : seq<Process>)
		requires valid_network(ntk)
		requires valid_network_impl(ntk)
		requires step_enabled(ntk, i, qR, QS)
		ensures step(ntk, i, qR, QS, ntk')
	{
		var messages := incoming_messages(ntk);
		messages := messages + ntk[i].inbox;
		ntk' := step_single(ntk, i, messages);
		process_has_msgs_from_quorum(ntk, i, qR, QS, ntk');
	}

	/* Safe step */

	predicate safe_step(ntk : seq<Process>, ntk' : seq<Process>)
	{
		|ntk'| == |ntk|
		&& (forall i :: 0 <= i < |ntk'| ==>
			only_change_inbox(ntk, ntk', i)
			&& ntk[i].inbox <= ntk'[i].inbox
			&& (forall msg :: msg in ntk'[i].inbox ==> 0 <= msg.src < |ntk'|)
			&& (forall msg :: msg in ntk'[i].inbox ==> (exists j :: 0 <= j < |ntk'| && msg in ntk'[j].outbox))
			&& (forall msg :: msg in ntk'[i].inbox && ntk'[msg.src].NBProcess? ==> msg in ntk'[msg.src].outbox))
	}

	lemma live_step_refines_safe_step(ntk : seq<Process>, i : nat, qR : set<nat>, QS : QuorumSystem, ntk' : seq<Process>)
		requires valid_network(ntk)
		requires valid_network_impl(ntk)
		requires step_enabled(ntk, i, qR, QS)
		requires step(ntk, i, qR, QS, ntk')
		ensures safe_step(ntk, ntk')
	{
		forall j | 0 <= j < |ntk'|
			ensures only_change_inbox(ntk, ntk', j)
		{
			if (i == j) {
				assert only_change_inbox(ntk, ntk', i);
			} else {
				assert ntk'[j] == ntk[j];
			}
		}
	}

	lemma safe_step_preserves_invariants(ntk : seq<Process>, ntk' : seq<Process>)
		requires valid_network(ntk)
		requires valid_network_impl(ntk)
		requires safe_step(ntk, ntk')
		ensures valid_network(ntk')
		ensures valid_network_impl(ntk')
	{
		sent_msgs_for_started_rnds(ntk, ntk');
	}
}
