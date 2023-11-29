include "../Defs.dfy"
include "../../shared/safety/UBosco_S.dfy"
include "../QuorumSystem.dfy"	
include "../LBosco.dfy"

module UBosco refines UBosco_S {

	import QSystem
	import LBosco
	import Defs	

	method step_impl...
	{
		...;
		if ... {
			var _ := Defs.quorum_nonempty(p.C.Q, senders);
			assert ...;
			...;
			
		} else {
			...;
		}
	}
}