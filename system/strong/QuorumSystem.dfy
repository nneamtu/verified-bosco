include "Defs.dfy"
include "../shared/abstr/QuorumSystem_A.dfy"	
	
module QSystem refines QSystem_A {

	import opened Defs

	predicate valid_config...
	{
		C.P != {} && C.Q != {}
		&& (forall q :: q in C.Q ==> q <= C.P)
		&& seven_intersection(C.Q)
	}

	method construct_system...
	{
		var P := {};
		var i := 0;
		while i < N
			invariant 0 <= i <= N
			invariant |P| == i
			invariant forall i :: i in P ==> 0 <= i < |P|
		{
			P := P + {i};
			i := i + 1;
		}
		var R := P;
		var Q := {P};
		var C := QuorumConfig(P, Q);
		QS := QuorumSystem(C, R);
	}	

	lemma two_intersection_contains_correct_process(QS : QuorumSystem, q1 : set<nat>, q2 : set<nat>)
		returns (id : nat)
		requires valid_quorum_system(QS)
		requires q1 in QS.C.Q && q2 in QS.C.Q
		ensures id in q1 * q2 && id in QS.R
	{
		var qR :| qR in QS.C.Q && qR <= QS.R;
		id := Defs.three_intersection_nonempty(QS.C.Q, q1, q2, qR);
	}

	lemma four_intersection_contains_correct_process(QS : QuorumSystem, q1 : set<nat>, q2 : set<nat>, q3 : set<nat>, q4 : set<nat>)
		returns (id : nat)
		requires valid_quorum_system(QS)
		requires q1 in QS.C.Q && q2 in QS.C.Q && q3 in QS.C.Q && q4 in QS.C.Q
		ensures id in q1 * q2 * q3 * q4 && id in QS.R
	{
		var qR :| qR in QS.C.Q && qR <= QS.R;
		id := Defs.five_intersection_nonempty(QS.C.Q, q1, q2, q3, q4, qR);
	}
}