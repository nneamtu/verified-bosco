include "../abstr/Defs_A.dfy"
include "../abstr/UBosco_A.dfy"

abstract module UBosco_S refines UBosco_A {

	import opened Defs_A
	import SetSeqUtil

	/* Step */

	predicate step(p : Process, p' : Process, proposals : set<Proposal>, quorum : set<nat>, other_q : OtherQuorums)
	{
		p.NBProcess?
		&& (p != p' ==>
		    (p'.NBProcess?
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
			  && inbox_to_proposals(p, proposals, quorum)
				&& LBosco.step_quorum(proposals, quorum, p.val, p'.C.Q, Result(p'.val, p'.status), other_q)))
	}

	lemma {:opaque} proposals_from_inbox_lemma(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		requires p != p'
		ensures forall t :: 0 <= t < p'.rnd ==> proposals_from_inbox(p'.inbox, p'.proposals_hist[t], t)
	{
		SetSeqUtil.seq_append_lemma(p.proposals_hist, p'.proposals_hist, p.rnd, pr);
		assert inbox_to_proposals(p, pr, q);
		assert proposals_from_inbox(p.inbox, pr, p.rnd);
		var P := (pr, t) => proposals_from_inbox(p.inbox, pr, t);
		SetSeqUtil.seq_append_predicate(p.proposals_hist, p'.proposals_hist, p.rnd, pr, P);
		assert p.rnd + 1 == p'.rnd;
		assert p'.inbox == p.inbox;
	}

	lemma {:opaque} outbox_vals_same_lemma(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		requires p != p'
		ensures forall m, t :: 0 <= t <= p'.rnd && m in p'.outbox && m.rnd == t ==> m.val == p'.val_hist[t]
	{
		SetSeqUtil.set_append_lemma(p.outbox, p'.outbox, Message(p'.id, p'.val, p'.rnd));
		SetSeqUtil.seq_append_lemma(p.val_hist, p'.val_hist, p'.rnd, p'.val);
		forall m, t | 0 <= t <= p'.rnd && m in p'.outbox && m.rnd == t
			ensures m.val == p'.val_hist[t]
		{
			if t < p'.rnd {
				if m in p.outbox {
					assert m.val == p.val_hist[t];
					assert m.val == p'.val_hist[t];
				} else {
					assert m == Message(p'.id, p'.val, p'.rnd);
					assert m.rnd == p'.rnd;
					assert m.rnd < p'.rnd;
					assert false;
				}
			} else {
				assert m.rnd == p'.rnd;
				if m in p.outbox {
					assert m.rnd <= p.rnd < p'.rnd;
					assert false;
				} else {
					assert m == Message(p'.id, p'.val, p'.rnd);
					assert p'.val == p'.val_hist[t];
				}
			}
		}
	}

	lemma {:opaque} outbox_invariants_lemma(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		requires p != p'
		ensures forall m :: m in p'.outbox ==> 0 <= m.rnd <= p'.rnd
		ensures forall m :: m in p'.outbox ==> m.src == p'.id
	{
		SetSeqUtil.set_append_lemma(p.outbox, p'.outbox, Message(p'.id, p'.val, p'.rnd));
		forall m | m in p'.outbox
			ensures 0 <= m.rnd <= p'.rnd
			ensures m.src == p'.id
		{
			if m in p.outbox {
				assert 0 <= m.rnd <= p.rnd;
				assert m.src == p.id;
			} else {
				assert m == Message(p'.id, p'.val, p'.rnd);
			}
		}
	}

	lemma {:opaque} results_vals_same_lemma(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		requires p != p'
		ensures forall t :: 0 <= t < p'.rnd ==> p'.re_hist[t].val == p'.val_hist[t+1]
	{
		SetSeqUtil.seq_append_lemma(p.re_hist, p'.re_hist, p.rnd, Result(p'.val, p'.status));
		SetSeqUtil.seq_append_lemma(p.val_hist, p'.val_hist, p'.rnd, p'.val);
		forall t | 0 <= t < p'.rnd
			ensures p'.re_hist[t].val == p'.val_hist[t+1]
		{
			if t < p.rnd {
				assert p.re_hist[t].val == p.val_hist[t+1];
				assert p'.re_hist[t].val == p'.val_hist[t+1];
			} else {
				assert p'.re_hist[t].val == p'.val == p'.val_hist[t+1]; 
			}
		}
	}

	lemma 
	{:opaque} 
	{:fuel LBosco.step_quorum<T>, 0, 0} 
	step_quorum_lemma<T, S>(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		requires p != p'
		ensures forall t :: 0 <= t < p.rnd + 1 ==> LBosco.step_quorum(p'.proposals_hist[t], p'.quorum_hist[t], p'.val_hist[t], p'.C.Q, p'.re_hist[t], p'.other_quorums_hist[t])
	{
		SetSeqUtil.seq_append_lemma(p.proposals_hist, p'.proposals_hist, p.rnd, pr);
		SetSeqUtil.seq_append_lemma(p.quorum_hist, p'.quorum_hist, p.rnd, q);
		SetSeqUtil.seq_append_lemma(p.re_hist, p'.re_hist, p.rnd, Result(p'.val, p'.status));
		SetSeqUtil.seq_append_lemma(p.other_quorums_hist, p'.other_quorums_hist, p.rnd, oq);
		SetSeqUtil.seq_append_lemma(p.val_hist[..p.rnd], p'.val_hist[..p.rnd + 1], p.rnd, p.val);
		var P := (pr, q, v, r, oq) => LBosco.step_quorum(pr, q, v, p.C.Q, r, oq);
		SetSeqUtil.seq_append_predicate_5(
			p.proposals_hist, p'.proposals_hist,
			p.quorum_hist, p'.quorum_hist,
			p.val_hist[..p.rnd], p'.val_hist[..p.rnd + 1],
			p.re_hist, p'.re_hist,
			p.other_quorums_hist, p'.other_quorums_hist,
			p.rnd,
			pr, q, p.val, Result(p'.val, p'.status), oq,
			P);
	}

	lemma step_preserves_invariants(p : Process, p' : Process, pr : set<Proposal>, q : set<nat>, oq : OtherQuorums)
		requires valid_process(p)
		requires step(p, p', pr, q, oq)
		ensures valid_process(p')
	{
		if p' != p {
			proposals_from_inbox_lemma(p, p', pr, q, oq);
			outbox_vals_same_lemma(p, p', pr, q, oq);
			outbox_invariants_lemma(p, p', pr, q, oq);
			results_vals_same_lemma(p, p', pr, q, oq);
			step_quorum_lemma(p, p', pr, q, oq);
		}
	}

	method step_impl<T(==), S>(p : Process<T, S>) returns (p' : Process<T, S>, proposals : set<Proposal<T>>, senders : set<nat>, other_q : OtherQuorums)
		requires valid_process(p)
		ensures step(p, p', proposals, senders, other_q)
	{
		var (pr, se) := inbox_to_proposals_impl(p);
		proposals := pr;
		senders := se;
		if senders in p.C.Q {
			assume senders != {};
			assert quorum_proposals_refl(senders, proposals);

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
		} else {
			p' := p;
		}
	}
}

module SetSeqUtil {
	
  lemma {:opaque} seq_append_pre<S>(s : seq<S>, s' : seq<S>, t : nat, el : S)
		requires |s| == t
		requires s' == s + [el]
		ensures forall t' :: 0 <= t' < t ==> s'[t'] == s[t']
	{}

	predicate seq_append<S>(s : seq<S>, s' : seq<S>, l : nat, el : S)
	{
		|s| == l && |s'| == l + 1
			&& (forall i :: 0 <= i < l ==> s[i] == s'[i])
			&& s'[l] == el
	}

	lemma {:opaque} seq_append_lemma<S>(s : seq<S>, s' : seq<S>, l : nat, el : S)
		requires |s| == l
		requires s' == s + [el]
		ensures seq_append(s, s', l, el)
	{}

	lemma {:opaque} seq_append_predicate<S>(s : seq<S>, s' : seq<S>, l : nat, el : S, P : (S, nat) -> bool)
		requires seq_append(s, s', l, el)
		requires forall i :: 0 <= i < l ==> P(s[i], i)
		requires P(el, l)
		ensures forall i :: 0 <= i < l + 1 ==> P(s'[i], i)
	{}

	lemma {:opaque} seq_append_predicate_2<S1, S2>(s1 : seq<S1>, s1' : seq<S1>, s2 : seq<S2>, s2' : seq<S2>, l : nat, el1 : S1, el2 : S2, P : (S1, S2) -> bool)
		requires seq_append(s1, s1', l, el1)
		requires seq_append(s2, s2', l, el2)
		requires forall i :: 0 <= i < l ==> P(s1[i], s2[i])
		requires P(el1, el2)
		ensures forall i :: 0 <= i < l + 1 ==> P(s1'[i], s2'[i])
	{}

	lemma {:opaque} seq_append_predicate_4<S1, S2, S3, S4>
		(s1 : seq<S1>, s1' : seq<S1>,
		s2 : seq<S2>, s2' : seq<S2>,
		s3 : seq<S3>, s3' : seq<S3>,
		s4 : seq<S4>, s4' : seq<S4>,
		l : nat,
		el1 : S1, el2 : S2, el3 : S3, el4 : S4,
		P : (S1, S2, S3, S4) -> bool)
		requires seq_append(s1, s1', l, el1)
		requires seq_append(s2, s2', l, el2)
		requires seq_append(s3, s3', l, el3)
		requires seq_append(s4, s4', l, el4)
		requires forall i :: 0 <= i < l ==> P(s1[i], s2[i], s3[i], s4[i])
		requires P(el1, el2, el3, el4)
		ensures forall i :: 0 <= i < l + 1 ==> P(s1'[i], s2'[i], s3'[i], s4'[i])
	{}

	lemma {:opaque} seq_append_predicate_5<S1, S2, S3, S4, S5>
		(s1 : seq<S1>, s1' : seq<S1>,
		s2 : seq<S2>, s2' : seq<S2>,
		s3 : seq<S3>, s3' : seq<S3>,
		s4 : seq<S4>, s4' : seq<S4>,
		s5 : seq<S5>, s5' : seq<S5>,
		l : nat,
		el1 : S1, el2 : S2, el3 : S3, el4 : S4, el5 : S5,
		P : (S1, S2, S3, S4, S5) -> bool)
		requires seq_append(s1, s1', l, el1)
		requires seq_append(s2, s2', l, el2)
		requires seq_append(s3, s3', l, el3)
		requires seq_append(s4, s4', l, el4)
		requires seq_append(s5, s5', l, el5)
		requires forall i :: 0 <= i < l ==> P(s1[i], s2[i], s3[i], s4[i], s5[i])
		requires P(el1, el2, el3, el4, el5)
		ensures forall i :: 0 <= i < l + 1 ==> P(s1'[i], s2'[i], s3'[i], s4'[i], s5'[i])
	{}

	predicate set_append<S>(a : set<S>, a' : set<S>, x : S)
	{
		(forall x' :: x' in a' ==> x' in a || x' == x)
	}

	lemma {:opaque} set_append_lemma<S>(a : set<S>, a' : set<S>, x : S)
		requires a' == a + {x}
		ensures set_append(a, a', x)
	{}

}

		
