include "../Defs.dfy"
include "../../shared/liveness/UBosco_L.dfy"
include "../QuorumSystem.dfy"	
include "../LBosco.dfy"

module UBosco refines UBosco_L {

	import QSystem
	import LBosco
	import Defs

	lemma quorum_nonempty_placeholder...
	{
		var _ := Defs.quorum_nonempty(p.C.Q, q);
	}
}
