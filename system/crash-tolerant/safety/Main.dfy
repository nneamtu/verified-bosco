include "../../shared/safety/Main_S.dfy"	
include "DistributedSystem.dfy"
include "Proof.dfy"

module Main refines Main_S {

	import opened DistributedSystem
	import Proof

	method
	{:fuel Proof.agreement<T, S>, 0, 0}
	{:fuel Proof.validity<T, S>, 0, 0}
	{:fuel Proof.unanimity<T, S>, 0, 0}
	Main...
	{
		...;

		while ...
			invariant Proof.agreement(S, QS)
			invariant Proof.validity(S, QS)
			invariant forall v :: v in V ==> Proof.unanimity(S, QS, v)
		{
			...;
			if ... {
				...;
			} else {
				if ... {
					...;
				} else {
					...;
				}
			}
			...;
		}
	}

	lemma safety_props_placeholder...
		ensures Proof.agreement(S, QS)
		ensures Proof.validity(S, QS)
		ensures forall v :: v in V ==> Proof.unanimity(S, QS, v)
	{
		Proof.agreement_lemma(S, QS);
		Proof.validity_lemma(S, QS);
		forall v | v in V
			ensures Proof.unanimity(S, QS, v)
		{
			Proof.unanimity_lemma(S, QS, v);
		}
	}
}
