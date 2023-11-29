include "../Types.dfy"

module Defs_A {

	import opened Types

	function method intersect_2(q1 : set<nat>, q2 : set<nat>, proposals : set<Proposal>) : set<Proposal>
	{
		set pr | pr in proposals && pr.id in (q1 * q2)
	}

	function method intersect_3(q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, proposals : set<Proposal>) : set<Proposal>
	{
		set pr | pr in proposals && pr.id in (q1 * q2 * q3)
	}

	function method intersect_4(q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal>) : set<Proposal>
	{
		set pr | pr in proposals && pr.id in (q1 * q2 * q3 * q4)
	}

	function method intersect_5(q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, q5 : set<nat>, proposals : set<Proposal>) : set<Proposal>
	{
		set pr | pr in proposals && pr.id in (q1 * q2 * q3 * q4 * q5)
	}

	function method unanimous<T(==)>(pr : set<Proposal<T>>, v : T) : bool {
		forall p :: p in pr ==> v == p.val
	}

	predicate quorum_proposals_refl(quorum : set<nat>, proposals : set<Proposal>){
		(forall p :: p in proposals ==> p.id in quorum)
		&& (forall id :: id in quorum ==> exists p :: p in proposals && p.id == id)
	}

	lemma instantiate_quorum_proposals_refl(quorum : set<nat>, proposals : set<Proposal>, id : nat)
		returns (p : Proposal)
		requires quorum_proposals_refl(quorum, proposals)
		requires id in quorum
		ensures p in proposals && p.id == id
	{
		p :| p in proposals && p.id == id;
	}

	function method unanimous_intersect_2<T(==)>(q1 : set<nat>, q2 : set<nat>, proposals : set<Proposal<T>>, v : T)
		: bool
	{
	  intersect_2(q1, q2, proposals) != {}
		&& unanimous(intersect_2(q1, q2, proposals), v)
	}

	function method unanimous_intersect_3<T(==)>(q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, proposals : set<Proposal<T>>, v : T)
		: bool
	{
	  intersect_3(q1, q2, q3, proposals) != {} && unanimous(intersect_3(q1, q2, q3, proposals), v)
	}

	function method unanimous_intersect_4<T(==)>(q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>, proposals : set<Proposal<T>>, v : T)
		: bool
	{
	  intersect_4(q1, q2, q3, q4, proposals) != {} && unanimous(intersect_4(q1, q2, q3, q4, proposals), v)
	}
}
