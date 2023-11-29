include "../shared/abstr/Defs_A.dfy"

module Defs refines Defs_A {

  predicate seven_intersection'(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>, q6 : set<nat>, q7 : set<nat>)
	{
		q1 in Q && q2 in Q && q3 in Q && q4 in Q && q5 in Q && q6 in Q && q7 in Q ==>
		  q1 * q2 * q3 * q4 * q5 * q6 * q7 != {}
	}

	predicate seven_intersection(Q : set<set<nat>>)
	{
		forall q1, q2, q3, q4, q5, q6, q7 :: seven_intersection'(Q, q1, q2, q3, q4, q5, q6, q7)
	}

  lemma seven_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>, q6 : set<nat>, q7 : set<nat>)
    returns (id : nat)
		requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q && q5 in Q && q6 in Q && q7 in Q
		ensures id in q1 * q2 * q3 * q4 * q5 * q6 * q7
    ensures q1 * q2 * q3 * q4 * q5 * q6 * q7 != {}
	{
		assert seven_intersection'(Q, q1, q2, q3, q4, q5, q6, q7);
    id :| id in q1 * q2 * q3 * q4 * q5 * q6 * q7;
	}

	lemma six_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>, q6 : set<nat>)
		returns (id : nat)
    requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q && q5 in Q && q6 in Q
		ensures id in q1 * q2 * q3 * q4 * q5 * q6
    ensures q1 * q2 * q3 * q4 * q5 * q6 != {}
	{
		assert seven_intersection'(Q, q1, q2, q3, q4, q5, q6, q6);
    id :| id in q1 * q2 * q3 * q4 * q5 * q6;
	}

	lemma five_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>)
    returns (id : nat)
		requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q && q5 in Q
    ensures id in q1 * q2 * q3 * q4 * q5
		ensures q1 * q2 * q3 * q4 * q5 != {}
	{
		assert seven_intersection'(Q, q1, q2, q3, q4, q5, q5, q5);
    id :| id in q1 * q2 * q3 * q4 * q5;
	}

	lemma four_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>)
		returns (id : nat)
    requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
    ensures id in q1 * q2 * q3 * q4
		ensures q1 * q2 * q3 * q4 != {}
	{
		assert seven_intersection'(Q, q1, q2, q3, q4, q4, q4, q4);
    id :| id in q1 * q2 * q3 * q4;
	}

	lemma three_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>)
		returns (id : nat)
    requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q
    ensures id in q1 * q2 * q3
		ensures q1 * q2 * q3 != {}
	{
		assert seven_intersection'(Q, q1, q2, q3, q3, q3, q3, q3);
    id :| id in q1 * q2 * q3;
	}

	lemma two_intersection_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>)
		returns (id : nat)
    requires seven_intersection(Q)
		requires q1 in Q && q2 in Q
    ensures id in q1 * q2
		ensures q1 * q2 != {}
	{
		assert seven_intersection'(Q, q1, q2, q2, q2, q2, q2, q2);
    id :| id in q1 * q2;
	}

	lemma quorum_nonempty(Q : set<set<nat>>, q : set<nat>)
		returns (id : nat)
    requires seven_intersection(Q)
		requires q in Q
    ensures id in q
		ensures q != {}
	{
		assert seven_intersection'(Q, q, q, q, q, q, q, q);
    id :| id in q;
	}

  lemma intersect_2_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, proposals : set<Proposal>)
    returns (p : Proposal)
		requires seven_intersection(Q)
		requires q1 in Q && q2 in Q
		requires quorum_proposals_refl(q1, proposals)
		ensures intersect_2(q1, q2, proposals) != {}
		ensures p in intersect_2(q1, q2, proposals)
	{
		var id := two_intersection_nonempty(Q, q1, q2);
		p := instantiate_quorum_proposals_refl(q1, proposals, id);
    assert p in intersect_2(q1, q2, proposals);
	}

	lemma intersect_3_nonempty(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, proposals : set<Proposal>)
    returns (p : Proposal)
		requires seven_intersection(Q)
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
		requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
		requires quorum_proposals_refl(q1, proposals)
		ensures intersect_4(q1, q2, q3, q4, proposals) != {}
		ensures p in intersect_4(q1, q2, q3, q4, proposals)
	{
		var id := four_intersection_nonempty(Q, q1, q2, q3, q4);
		p := instantiate_quorum_proposals_refl(q1, proposals, id);
    assert p in intersect_4(q1, q2, q3, q4, proposals);
	}

  lemma unanimous_intersect_2_implies_unanimous_intersect_4<T>(Q : set<set<nat>>, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal>, v : T)
		requires seven_intersection(Q)
		requires q1 in Q && q2 in Q && q3 in Q && q4 in Q
		requires quorum_proposals_refl(q1, proposals)
		requires unanimous_intersect_2(q1, q2, proposals, v)
		ensures unanimous_intersect_4(q1, q2, q3, q4, proposals, v)
	{
		var _ := intersect_4_nonempty(Q, q1, q2, q3, q4, proposals);
	}

}