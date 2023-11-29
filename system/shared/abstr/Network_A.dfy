include "../Types.dfy"

module Network_A {

	import opened Types

  /* Invariants */

	predicate valid_network_single(ntk : seq<Process>, p : Process, i : nat) 
	{
		p.id == i
		&& (forall msg :: msg in p.inbox ==> 0 <= msg.src < |ntk|)
		&& (forall msg :: msg in p.outbox ==> 0 <= msg.src < |ntk|)
		&& (forall msg :: msg in p.inbox ==> (exists j :: 0 <= j < |ntk| && msg in ntk[j].outbox))
		&& (forall msg :: msg in p.inbox && ntk[msg.src].NBProcess? ==> msg in ntk[msg.src].outbox)
		&& (p.NBProcess? ==> (forall msg :: msg in p.outbox ==> msg.src == p.id))
		&& (p.BProcess? ==> (forall msg :: msg in p.outbox ==> ntk[msg.src].BProcess?))
	}

	predicate valid_network(ntk : seq<Process>)
	{
		forall i :: 0 <= i < |ntk| ==> valid_network_single(ntk, ntk[i], i)
	}

  /* Shared definitions */

	function method incoming_messages(ntk : seq<Process>) : set<Message>
		ensures forall msg :: msg in incoming_messages(ntk) ==> (exists j :: 0 <= j < |ntk| && msg in ntk[j].outbox)		
	{
		if ntk == [] then {}
		else (set msg | msg in ntk[0].outbox) + incoming_messages(ntk[1..])
	}

	predicate only_change_inbox(ntk : seq<Process>, ntk' : seq<Process>, i : nat)
		requires 0 <= i < |ntk|
		requires i < |ntk'|
	{
		(ntk[i].NBProcess? ==>
			(ntk'[i].NBProcess?
			&& ntk[i].id == ntk'[i].id
			&& ntk[i].C == ntk'[i].C
			&& ntk[i].status == ntk'[i].status
			&& ntk[i].val == ntk'[i].val
			&& ntk[i].rnd == ntk'[i].rnd
			&& ntk[i].outbox == ntk'[i].outbox
			&& ntk[i].val_hist == ntk'[i].val_hist
			&& ntk[i].re_hist == ntk'[i].re_hist
			&& ntk[i].proposals_hist == ntk'[i].proposals_hist
			&& ntk[i].quorum_hist == ntk'[i].quorum_hist
			&& ntk[i].other_quorums_hist == ntk'[i].other_quorums_hist))
		&& (ntk[i].BProcess? ==>
			(ntk'[i].BProcess?
			&& ntk[i].id == ntk'[i].id
			&& ntk[i].outbox == ntk'[i].outbox
			&& ntk[i].st == ntk'[i].st))
	}
}
