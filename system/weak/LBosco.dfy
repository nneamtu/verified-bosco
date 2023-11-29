include "../shared/abstr/LBosco_A.dfy"	

module LBosco refines LBosco_A {

	predicate step_quorum...
	{
		quorum_proposals_refl(quorum, proposals)
		&& quorum in Q
		&& (result.status == D ==> unanimous(proposals, result.val))
		&& (result.status == M ==> other_q.q2 in Q && other_q.q3 in Q && unanimous_intersect_3(quorum, other_q.q2, other_q.q3, proposals, result.val))
		&& (result.status == U ==> result.val == def)
		&& ((exists q2, q3, v :: q2 in Q && q3 in Q && unanimous_intersect_3(quorum, q2, q3, proposals, v)) ==> 
				other_q.q2 in Q && other_q.q3 in Q && unanimous_intersect_3(quorum, other_q.q2, other_q.q3, proposals, result.val))
		&& ((exists val' :: unanimous(proposals, val')) ==> unanimous(proposals, result.val) && result.status == D)
		&& (!(exists val' :: unanimous(proposals, val')) && !(exists q2, q3, v :: q2 in Q && q3 in Q && unanimous_intersect_3(quorum, q2, q3, proposals, v)) ==> result.val == def)
	}

	lemma instantiate_decide_condition<T>(proposals : set<Proposal>, quorum : set<nat>, def : T, Q : set<set<nat>>, result : Result, other_q : OtherQuorums, val' : T)
		requires step_quorum(proposals, quorum, def, Q, result, other_q)
		requires unanimous(proposals, val')
		ensures unanimous(proposals, result.val)
		ensures result.status == D
	{}

	lemma instantiate_maybe_condition<T>(proposals : set<Proposal>, quorum : set<nat>, def : T, Q : set<set<nat>>, result : Result, other_q : OtherQuorums, q2 : set<nat>, q3 : set<nat>, val' : T)
		requires step_quorum(proposals, quorum, def, Q, result, other_q)
		requires q2 in Q && q3 in Q
		requires unanimous_intersect_3(quorum, q2, q3, proposals, val')
		ensures other_q.q2 in Q && other_q.q3 in Q
		ensures unanimous_intersect_3(quorum, other_q.q2, other_q.q3, proposals, result.val)
	{}

	method step_quorum_impl...
	{
		var all_pr := set pr | pr in proposals :: pr.val;		
		if exists v | v in all_pr :: unanimous(proposals, v)
		{
			var v :| v in all_pr && unanimous(proposals, v);
			result := Result(v, D);
			other_q := OtherQuorums(quorum, quorum, quorum);
		}
		else if exists q2, q3, v | q2 in Q && q3 in Q && v in all_pr :: unanimous_intersect_3(quorum, q2, q3, proposals, v)
    {
			var q2, q3, v :| q2 in Q && q3 in Q && v in all_pr && unanimous_intersect_3(quorum, q2, q3, proposals, v);
			result := Result(v, M);
			other_q := OtherQuorums(q2, q3, q3);
		}
		else
		{
			result := Result(def, U);
			other_q := OtherQuorums(quorum, quorum, quorum);
		}	
	}
}
	
