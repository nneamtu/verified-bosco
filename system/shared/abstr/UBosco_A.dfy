include "../Types.dfy"
include "QuorumSystem_A.dfy"
include "LBosco_A.dfy"

abstract module UBosco_A {

	import opened Types
	import QSystem : QSystem_A
	import LBosco : LBosco_A

  /* Invariants */

	predicate valid_process<T, S>(p : Process<T, S>)
	{
		p.NBProcess?
		&& QSystem.valid_config(p.C)
		&& p.rnd == |p.re_hist| == |p.proposals_hist| == |p.quorum_hist| == |p.other_quorums_hist|
		&&	p.rnd + 1 == |p.val_hist|
		&& p.val_hist[p.rnd] == p.val
		&& Message(p.id, p.val_hist[0], 0) in p.outbox
		&& (forall m :: m in p.outbox ==> 0 <= m.rnd <= p.rnd)
		&& (forall m :: m in p.outbox ==> m.src == p.id)
		&& (forall t :: 0 <= t < p.rnd ==> proposals_from_inbox(p.inbox, p.proposals_hist[t], t))
		&& (forall m, t :: 0 <= t <= p.rnd && m in p.outbox && m.rnd == t ==> m.val == p.val_hist[t])
		&& (forall t :: 0 <= t <= p.rnd ==> Message(p.id, p.val_hist[t], t) in p.outbox)
		&& (forall t :: 0 <= t < p.rnd ==> p.re_hist[t].val == p.val_hist[t+1])
		&& (forall t :: 0 <= t < p.rnd ==> LBosco.step_quorum(p.proposals_hist[t], p.quorum_hist[t], p.val_hist[t], p.C.Q, p.re_hist[t], p.other_quorums_hist[t]))
	}

  /* Shared definitions */

	predicate proposals_from_inbox<T(!new)>(inbox : set<Message>, proposals : set<Proposal<T>>, rnd : nat)
	{
		(forall src, vals :: Proposal(src, vals) in proposals ==>
			exists msg | msg in inbox && msg.rnd == rnd :: msg.src == src && msg.val == vals)
	}

	predicate inbox_to_proposals<T(!new), S>(p : Process<T, S>, proposals : set<Proposal<T>>, senders : set<nat>)
		requires p.NBProcess?
	{
		(forall src, vals :: Proposal(src, vals) in proposals ==>
			exists msg | msg in p.inbox && msg.rnd == p.rnd :: msg.src == src && msg.val == vals)
		&& (forall msg :: msg in p.inbox && msg.rnd == p.rnd ==> Proposal(msg.src, msg.val) in proposals)
		&& (forall id :: id in senders ==> exists pr :: pr in proposals && pr.id == id)
		&& (forall pr :: pr in proposals ==> pr.id in senders)
	}

	function method inbox_to_proposals_impl<T(==), S>(p : Process<T, S>) : (set<Proposal<T>>, set<nat>)
		requires p.NBProcess?
		ensures inbox_to_proposals(p, inbox_to_proposals_impl(p).0, inbox_to_proposals_impl(p).1)
	{
		(set msg | msg in p.inbox && msg.rnd == p.rnd :: Proposal(msg.src, msg.val),
			set msg | msg in p.inbox && msg.rnd == p.rnd :: msg.src)
	}

  /* Initialization */

	predicate init<T, S>(id : nat, val : T, C : QuorumConfig, p : Process<T, S>)
	{
		p.NBProcess?
		&& p.C == C
		&& p.id == id
		&& p.status == U
		&& p.val == val
		&& p.rnd == 0
		&& p.inbox == {}
		&& p.outbox == {Message(id, val, 0)}
		&& p.val_hist == [val]
		&& p.re_hist == []
		&& p.proposals_hist == []
		&& p.quorum_hist == []
		&& p.other_quorums_hist == []
	}

	method init_impl<T(==), S>(id : nat, val : T, C : QuorumConfig) returns (p : Process<T, S>)
		requires QSystem.valid_config(C)
		ensures init(id, val, C, p)
	{
		p := NBProcess(id, C, U, val, 0, {}, {Message(id, val, 0)}, [val], [], [], [], []);
	}

  /* Proofs */

	lemma single_message_per_round(p : Process)
		requires valid_process(p)
		ensures forall m, m' :: m in p.outbox && m' in p.outbox && m.rnd == m'.rnd ==> m == m'
	{
		forall m, m' | m in p.outbox && m' in p.outbox && m.rnd == m'.rnd
			ensures m == m'
		{
			assert m.val == p.val_hist[m.rnd] == p.val_hist[m'.rnd] == m'.val;
			assert m.src == p.id ==  m'.src;
		}
	}		
}
