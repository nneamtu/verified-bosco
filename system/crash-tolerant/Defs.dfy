include "../shared/abstr/Defs_A.dfy"

module Defs refines Defs_A {

  predicate three_intersection(Q : set<set<nat>>)
	{
		forall q1, q2, q3 :: q1 in Q && q2 in Q && q3 in Q ==> q1 * q2 * q3 != {}
	}

  lemma quorum_nonempty(Q : set<set<nat>>, q : set<nat>)
		returns (id : nat)
		requires three_intersection(Q)
		requires q in Q
		ensures q != {}
		ensures id in q
	{
		id :| id in q;
	}

	lemma two_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>)
		returns (id : nat)
		requires three_intersection(Q)
		requires q1 in Q && q2 in Q
		ensures q1 * q2 != {}
		ensures id in q1 * q2
	{
		id :| id in q1 * q2;
	}

	lemma three_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>)
		returns (id : nat)
		requires three_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q
		ensures q1 * q2 * q3 != {}
		ensures id in q1 * q2 * q3
	{
		id :| id in q1 * q2 * q3;
	}

	lemma intersect_2_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, p1 : set<Proposal>)
		returns (p : Proposal)
		requires three_intersection(Q)
		requires q1 in Q && q2 in Q
		requires quorum_proposals_refl(q1, p1)
		ensures intersect_2(q1, q2, p1) != {}
		ensures p in intersect_2(q1, q2, p1)
	{
		var id := two_intersection_nonempty(Q, q1, q2);
		p := instantiate_quorum_proposals_refl(q1, p1, id);
		assert p in intersect_2(q1, q2, p1);
	}
		

	lemma unanimous_implies_unanimous_intersect_2<T>(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, p1 : set<Proposal<T>>, v : T)
		requires three_intersection(Q)
		requires q1 in Q && q2 in Q
		requires quorum_proposals_refl(q1, p1)
		requires unanimous(p1, v)
		ensures unanimous_intersect_2(q1, q2, p1, v)
	{
		var _ := intersect_2_nonempty(Q, q1, q2, p1);
	}

	lemma unanimous_intersect_2_sym<T>(q1 : set<nat>, q2 : set<nat>, p1 : set<Proposal<T>>, p2 : set<Proposal<T>>, v : T)
		requires quorum_proposals_refl(q1, p1)
		requires quorum_proposals_refl(q2, p2)
		requires unanimous_intersect_2(q1, q2, p1, v)
		requires forall p, p' :: p in p1 && p' in p2 && p.id == p'.id ==> p == p'
		ensures unanimous_intersect_2(q2, q1, p2, v)
	{}

	lemma unanimous_intersect_3_same<T>(Q : set<set<nat>>, q : set<nat>, q' : set<nat>, q'' : set<nat>, proposals : set<Proposal<T>>, v : T, v' : T)
		requires three_intersection(Q)
		requires q in Q && q' in Q && q'' in Q
		requires quorum_proposals_refl(q, proposals)
		requires unanimous_intersect_2(q, q', proposals, v)
		requires unanimous_intersect_2(q, q'', proposals, v')
		ensures v == v'
	{}

}