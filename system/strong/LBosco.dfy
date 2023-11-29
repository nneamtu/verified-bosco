include "../shared/abstr/LBosco_A.dfy"	

module LBosco refines LBosco_A {

	predicate step_quorum...
	{
		quorum_proposals_refl(quorum, proposals)
		&& quorum in Q
		&& (result.status == D ==> other_q.q2 in Q && unanimous_intersect_2(quorum, other_q.q2, proposals, result.val))
		&& (result.status == M ==> other_q.q2 in Q && other_q.q3 in Q && other_q.q4 in Q && unanimous_intersect_4(quorum, other_q.q2, other_q.q3, other_q.q4, proposals, result.val))
		&& (result.status == U ==> result.val == def)
		&& ((exists q2, val' :: q2 in Q && unanimous_intersect_2(quorum, q2, proposals, val')) ==> 
		other_q.q2 in Q && unanimous_intersect_2(quorum, other_q.q2, proposals, result.val) && result.status == D)
		&& ((exists q2, q3, v, q4 :: q2 in Q && q3 in Q && q4 in Q && unanimous_intersect_4(quorum, q2, q3, q4, proposals, v)) ==>
		other_q.q2 in Q && other_q.q3 in Q && other_q.q4 in Q && unanimous_intersect_4(quorum, other_q.q2, other_q.q3, other_q.q4, proposals, result.val))
	}

	lemma instantiate_decide_condition<T>(proposals : set<Proposal>, quorum : set<nat>, def : T, Q : set<set<nat>>, result : Result, other_q : OtherQuorums, q2 : set<nat>, val' : T)
		requires step_quorum(proposals, quorum, def, Q, result, other_q)
		requires q2 in Q
		requires unanimous_intersect_2(quorum, q2, proposals, val')
		ensures other_q.q2 in Q
		ensures unanimous_intersect_2(quorum, other_q.q2, proposals, result.val)
		ensures result.status == D
	{}

	lemma instantiate_maybe_condition<T>(proposals : set<Proposal>, quorum : set<nat>, def : T, Q : set<set<nat>>, result : Result, other_q : OtherQuorums, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, val' : T)
		requires step_quorum(proposals, quorum, def, Q, result, other_q)
		requires q2 in Q && q3 in Q && q4 in Q
		requires unanimous_intersect_4(quorum, q2, q3, q4, proposals, val')
		ensures other_q.q2 in Q && other_q.q3 in Q && other_q.q4 in Q
		ensures unanimous_intersect_4(quorum, other_q.q2, other_q.q3, other_q.q4, proposals, result.val)
	{}

	method step_quorum_impl...
	{
		var all_pr := set pr | pr in proposals :: pr.val;		
		if exists q2, v | q2 in Q && v in all_pr :: unanimous_intersect_2(quorum, q2, proposals, v)
		{
			var q2, v :| q2 in Q && v in all_pr && unanimous_intersect_2(quorum, q2, proposals, v);
			result := Result(v, D);
			other_q := OtherQuorums(q2, q2, q2);
		}
		else if exists q2, q3, q4, v | q2 in Q && q3 in Q && q4 in Q && v in all_pr :: unanimous_intersect_4(quorum, q2, q3, q4, proposals, v)
    {
			var q2, q3, q4, v :| q2 in Q && q3 in Q && q4 in Q && v in all_pr && unanimous_intersect_4(quorum, q2, q3, q4, proposals, v);
			result := Result(v, M);
			other_q := OtherQuorums(q2, q3, q4);
		}
		else
		{
			result := Result(def, U);
			other_q := OtherQuorums(quorum, quorum, quorum);
		}	
	}
}


	
