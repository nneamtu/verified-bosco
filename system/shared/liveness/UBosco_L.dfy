include "Defs_L.dfy"
include "../abstr/UBosco_A.dfy"

abstract module UBosco_L refines UBosco_A {

  import opened Defs_L

	/* Step */

	predicate step_enabled(p : Process)
    requires p.NBProcess?
	{
		has_msgs_from_quorum(p, p.C.Q)
	}

  predicate step(p : Process, p' : Process, proposals : set<Proposal>, quorum : set<nat>, other_q : OtherQuorums)
	{
		p.NBProcess?
		&& p'.NBProcess?
		&& p'.C == p.C
		&& p'.id == p.id
		&& p'.rnd == p.rnd + 1 
		&& p'.inbox == p.inbox
		&& p'.outbox == p.outbox + {Message(p'.id, p'.val, p'.rnd)}
		&& p'.val_hist == p.val_hist + [p'.val]
		&& p'.re_hist == p.re_hist + [Result(p'.val, p'.status)]
	  && p'.proposals_hist == p.proposals_hist + [proposals] 
	  && p'.quorum_hist == p.quorum_hist + [quorum]
		&& p'.other_quorums_hist == p.other_quorums_hist + [other_q]
		&& proposals_from_inbox(p'.inbox, proposals, p.rnd)
		&& LBosco.step_quorum(proposals, quorum, p.val, p'.C.Q, Result(p'.val, p'.status), other_q)
	}



	lemma {:opaque} step_preserves_invariants(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		ensures valid_process(p')
	{}

	method step_impl<T(==), S>(p : Process) 
    returns (p' : Process, proposals : set<Proposal>, senders : set<nat>, other_q : OtherQuorums)
		requires valid_process(p)
		requires step_enabled(p)
		ensures step(p, p', proposals, senders, other_q)
	{
		var (pr, se) := inbox_to_proposals_impl(p);
		var q :| q in p.C.Q && q <= se;
		proposals := set p | p in pr && p.id in q;
		senders := q;
    quorum_nonempty_placeholder(p, senders);
		var result, other_q' := LBosco.step_quorum_impl(proposals, senders, p.val, p.C.Q);
    other_q := other_q';
			
		var status' := result.status;
		var val' := result.val;
		var rnd' := p.rnd + 1;
		var outbox' := p.outbox + {Message(p.id, val', rnd')};
		var val_hist' := p.val_hist + [result.val];
		var re_hist' := p.re_hist + [result];
		var proposals_hist' := p.proposals_hist + [proposals];
		var quorum_hist' := p.quorum_hist + [senders];
    var other_quorums_hist' := p.other_quorums_hist + [other_q];
		p' := NBProcess(
			p.id,
			p.C,
			status',
			val',
			rnd',
			p.inbox,
			outbox',
			val_hist',
			re_hist',
			proposals_hist',
			quorum_hist',
      other_quorums_hist');
	}

	lemma quorum_nonempty_placeholder(p : Process, q : set<nat>)
		requires valid_process(p)
		requires q in p.C.Q
		ensures q != {}

}