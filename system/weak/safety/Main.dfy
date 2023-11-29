include "../../shared/safety/Main_S.dfy"	
include "DistributedSystem.dfy"
include "Proof.dfy"

module Main refines Main_S {

	import opened DistributedSystem
	import Proof

	method
	{:fuel Proof.agreement<T, S>, 0, 0}
	{:fuel Proof.validity<T, S>, 0, 0}
	{:fuel Proof.weakly_one_step<T, S>, 0, 0}
	Main...
	{
		...;

		while ...
			invariant Proof.agreement(S, QS)
			invariant Proof.validity(S, QS)
			invariant forall v :: v in V ==> Proof.weakly_one_step(S, QS, v)
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
		ensures forall v :: v in V ==> Proof.weakly_one_step(S, QS, v)
	{
		Proof.agreement_lemma(S, QS);
		Proof.validity_lemma(S, QS);
		forall v | v in V
			ensures Proof.weakly_one_step(S, QS, v)
		{
			Proof.weakly_one_step_lemma(S, QS, v);
		}
	}
}
