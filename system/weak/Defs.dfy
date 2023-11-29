include "../shared/abstr/Defs_A.dfy"

module Defs refines Defs_A {

  predicate five_intersection'(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>)
	{
		q1 in Q && q2 in Q && q3 in Q && q4 in Q && q5 in Q ==> q1 * q2 * q3 * q4 * q5 != {}
	}

	predicate five_intersection(Q : set<set<nat>>)
	{
		forall q1, q2, q3, q4, q5 :: five_intersection'(Q, q1, q2, q3, q4, q5)
	}

  lemma quorum_nonempty(Q : set<set<nat>>, q : set<nat>)
    returns (id : nat)
		requires five_intersection(Q)
		requires q in Q
		ensures q != {}
    ensures id in q
	{
		assert five_intersection'(Q, q, q, q, q, q);
    id :| id in q;
	}

	lemma two_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>)
    returns (id : nat)
		requires five_intersection(Q)
		requires q1 in Q && q2 in Q
		ensures q1 * q2 != {}
    ensures id in q1 * q2
	{
		assert five_intersection'(Q, q1, q2, q2, q2, q2);
    id :| id in q1 * q2;
	}

	lemma three_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>)
    returns (id : nat)
    requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q
		ensures q1 * q2 * q3 != {}
    ensures id in q1 * q2 * q3
	{
		assert five_intersection'(Q, q1, q2, q3, q3, q3);
    id :| id in q1 * q2 * q3;
	}

	lemma four_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>)
		returns (id : nat)
    requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
		ensures q1 * q2 * q3 * q4 != {}
    ensures id in q1 * q2 * q3 * q4
	{
		assert five_intersection'(Q, q1, q2, q3, q4, q4);
    id :| id in q1 * q2 * q3 * q4;
	}

	lemma five_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>)
		returns (id : nat)
    requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q && q5 in Q
		ensures q1 * q2 * q3 * q4 * q5 != {}
    ensures id in q1 * q2 * q3 * q4 * q5
	{
		assert five_intersection'(Q, q1, q2, q3, q4, q5);
    id :| id in q1 * q2 * q3 * q4 * q5;
	}

  lemma intersect_3_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, proposals : set<Proposal>)
    returns (p : Proposal)
		requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q
		requires quorum_proposals_refl(q1, proposals)
		ensures intersect_3(q1, q2, q3, proposals) != {}
		ensures p in intersect_3(q1, q2, q3, proposals)
	{
		var id := three_intersection_nonempty(Q, q1, q2, q3);
    p := instantiate_quorum_proposals_refl(q1, proposals, id);
		assert p in intersect_3(q1, q2, q3, proposals);
	}

	lemma intersect_4_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal>)
    returns (p : Proposal)
		requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
		requires quorum_proposals_refl(q1, proposals)
		ensures intersect_4(q1, q2, q3, q4, proposals) != {}
		ensures p in intersect_4(q1, q2, q3, q4, proposals)
	{
		var id := four_intersection_nonempty(Q, q1, q2, q3, q4);
		p := instantiate_quorum_proposals_refl(q1, proposals, id);
		assert p in intersect_4(q1, q2, q3, q4, proposals);
	}

  lemma unanimous_intersect_4_with_qR<T>(Q : set<set<nat>>, qR : set<nat>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal>, v1 : T, v2 : T)
    returns (p : Proposal)
    requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q && qR in Q
		requires quorum_proposals_refl(q1, proposals)
		requires unanimous_intersect_4(q1, q2, q3, q4, proposals, v1)
		requires unanimous_intersect_4(q1, q2, q3, q4, proposals, v2)
		ensures p in proposals && p.id in qR 
    ensures v1 == p.val && v2 == p.val
	{
    var id := five_intersection_nonempty(Q, q1, q2, q3, q4, qR);
    p := instantiate_quorum_proposals_refl(q1, proposals, id);
  }

	lemma unanimous_implies_unanimous_intersect_3<T>(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, proposals : set<Proposal>, v : T)
		requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q
		requires quorum_proposals_refl(q1, proposals)
		requires unanimous(proposals, v)
		ensures unanimous_intersect_3(q1, q2, q3, proposals, v)
	{
		var _ := intersect_3_nonempty(Q, q1, q2, q3, proposals);
	}

	lemma unanimous_implies_unanimous_intersect_4<T>(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal>, v : T)
		requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
		requires quorum_proposals_refl(q1, proposals)
		requires unanimous(proposals, v)
		ensures unanimous_intersect_4(q1, q2, q3, q4, proposals, v)
	{
		var _ := intersect_4_nonempty(Q, q1, q2, q3, q4, proposals);
	}

	lemma unanimous_intersect_3_implies_unanimous_intersect_4<T>(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal>, v1 : T, v2 : T)
		requires five_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
		requires quorum_proposals_refl(q1, proposals)
		requires unanimous_intersect_3(q1, q2, q2, proposals, v1)
		requires unanimous_intersect_3(q1, q3, q4, proposals, v2)
		ensures unanimous_intersect_4(q1, q2, q3, q4, proposals, v1)
		ensures unanimous_intersect_4(q1, q2, q3, q4, proposals, v2)
	{
		var _ := intersect_4_nonempty(Q, q1, q2, q3, q4, proposals);
	}
}