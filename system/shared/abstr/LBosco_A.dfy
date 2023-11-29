include "../Types.dfy"
include "Defs_A.dfy"

abstract module LBosco_A {
	import opened Types
	import opened Defs_A

	predicate step_quorum<T(!new)>(proposals : set<Proposal>, quorum : set<nat>, def : T, Q : set<set<nat>>, result : Result, other_q : OtherQuorums)

	method step_quorum_impl<T(==)>(proposals : set<Proposal<T>>, quorum : set<nat>, def : T, Q : set<set<nat>>)
		returns (result : Result<T>, other_q : OtherQuorums)
		requires quorum_proposals_refl(quorum, proposals)
		requires quorum in Q
		requires quorum != {}
		ensures step_quorum(proposals, quorum, def, Q, result, other_q)

}