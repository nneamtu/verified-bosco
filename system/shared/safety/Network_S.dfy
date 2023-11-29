include "../abstr/Network_A.dfy"

module Network_S refines Network_A {

	/* Step */

	predicate step(ntk : seq<Process>, ntk' : seq<Process>)
	{
		|ntk'| == |ntk|
		&& (forall i :: 0 <= i < |ntk'| ==>
			only_change_inbox(ntk, ntk', i)
			&& ntk[i].inbox <= ntk'[i].inbox
			&& (forall msg :: msg in ntk'[i].inbox ==> 0 <= msg.src < |ntk'|)
			&& (forall msg :: msg in ntk'[i].inbox ==> (exists j :: 0 <= j < |ntk'| && msg in ntk'[j].outbox))
			&& (forall msg :: msg in ntk'[i].inbox && ntk'[msg.src].NBProcess? ==> msg in ntk'[msg.src].outbox))
	}

	lemma step_preserves_invariants(ntk : seq<Process>, ntk' : seq<Process>)
		requires valid_network(ntk)
		requires step(ntk, ntk')
		ensures valid_network(ntk')
	{}

	function method {:opaque} step_single(ntk : seq<Process>, i : nat, messages : set<Message>) : seq<Process>
		requires 0 <= i < |ntk|
		ensures |ntk| == |step_single(ntk, i, messages)|
		ensures forall j :: 0 <= j < |ntk| && j != i ==> ntk[j] == step_single(ntk, i, messages)[j]
		ensures step_single(ntk, i, messages)[i].inbox == messages
		ensures only_change_inbox(ntk, step_single(ntk, i, messages), i)
	{
		ntk[i := ntk[i].(inbox := messages)]
	}

	method step_impl(ntk : seq<Process>) returns (ntk' : seq<Process>)
		requires valid_network(ntk)
		ensures step(ntk, ntk')
	{
		ntk' := ntk;
		assert step(ntk, ntk');
		var i := 0;
		while i < |ntk|
			invariant 0 <= i <= |ntk|
			invariant |ntk'| == |ntk|
			invariant forall j :: 0 <= j < i ==> ntk'[j] == ntk[j].(inbox := incoming_messages(ntk) + ntk[j].inbox)
			invariant forall j :: 0 <= j < i ==> only_change_inbox(ntk, ntk', j)
			invariant forall k :: i <= k < |ntk| ==> ntk'[k] == ntk[k]
			invariant valid_network(ntk)
		{
			var messages := incoming_messages(ntk);
			messages := messages + ntk[i].inbox;
			ntk' := step_single(ntk', i, messages);
			i := i + 1;
		}
		assert step(ntk, ntk');
	}
}
