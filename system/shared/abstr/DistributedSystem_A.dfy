include "../Types.dfy"
include "UBosco_A.dfy"
include "Network_A.dfy"

abstract module DistributedSystem_A {

	import opened Types
	import opened UBosco : UBosco_A
	import Network : Network_A

  /* Invariants */

	predicate valid_distributed_system_single(S : seq<Process>, QS : QuorumSystem, p : Process, i : nat)
	{
		Network.valid_network_single(S, p, i)
		&& (p.NBProcess? ==> UBosco.valid_process(p))
		&& (p.NBProcess? ==> p.C == QS.C)
	}

	// Hacky solution: Dafny doesn't allow refining non-abstract predicates
	// (unless they are protected, and thus not accessible outside the module)
	// So, keep [valid_distributed_system_impl] abstract here, and any non-abstract 
	// module that refines [DistributedSystem_A] can implement extra invariants
	// using this predicate
	predicate valid_distributed_system(S : seq<Process>, QS : QuorumSystem)
	{
		UBosco.QSystem.valid_quorum_system(QS)
		&& (forall i :: 0 <= i < |S| ==> valid_distributed_system_single(S, QS, S[i], i))
		&& (forall i :: i in QS.C.P ==> 0 <= i < |S|)
		&& (forall i :: i in QS.R ==> S[i].NBProcess?)
	}

	predicate valid_distributed_system_impl(S : seq<Process>, QS : QuorumSystem)

  /* Initialization */

	predicate init<T, S>(N : nat, V : set<T>, init_byz_st : S, S : seq<Process>, QS : QuorumSystem)
	{
		N > 0
		&& V != {}
		&& |S| == N
		&& valid_distributed_system(S, QS)
		&& valid_distributed_system_impl(S, QS)
		&& (forall i :: 0 <= i < |S| && S[i].NBProcess? ==> S[i].val_hist[0] in V)
	}

	method init_impl<T(==), S>(N : nat, V : set<T>, init_byz_st : S) returns (S : seq<Process>, QS : QuorumSystem)
		requires N > 0
		requires V != {}
		ensures init(N, V, init_byz_st, S, QS)

	/* Byzantine processes */

	predicate byzantine_process_init(S : seq<Process>, QS : QuorumSystem, id : nat, p : Process)
	{
		id !in QS.R
			&& p.BProcess?
			&& p.inbox == {}
			&& p.outbox == {}
			&& p.id == id
	}

	method byzantine_process_init_impl<T, S>(S : seq<Process>, QS : QuorumSystem, id : nat, st : S) returns (p : Process<T, S>)
		requires id !in QS.R
		ensures byzantine_process_init(S, QS, id, p)
	{
		p := BProcess(id, {}, {}, st);
	}

	predicate byzantine_process_step(S : seq<Process>, i : nat, QS : QuorumSystem, S' : seq<Process>)
		requires 0 <= i < |S|
	{
		|S| == |S'|
		&& (forall j :: 0 <= j < |S'| && i != j ==> S'[j] == S[j])
		&& S[i].BProcess? && S'[i].BProcess?	
		&& S'[i].id == S[i].id
		&& S'[i].inbox == S[i].inbox
		&& S[i].outbox <= S'[i].outbox
		&& (forall msg :: msg in S'[i].outbox ==> 0 <= msg.src < |S|)
		&& (forall msg :: msg in S'[i].outbox ==> S'[msg.src].BProcess?)
	}

	lemma byzantine_process_step_preserves_invariants(S : seq<Process>, i : nat, QS : QuorumSystem, S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires byzantine_process_step(S, i, QS, S')
		ensures valid_distributed_system(S', QS)
		ensures valid_distributed_system_impl(S', QS)
	{	
		assume valid_distributed_system_impl(S', QS);
	}

	method byzantine_process_step_impl(S : seq<Process>, i : nat, QS : QuorumSystem) returns (S' : seq<Process>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires S[i].BProcess?
		ensures byzantine_process_step(S, i, QS, S')
	{
		S' := S;
	}

  /* Proofs */

	lemma exists_qR(S : seq<Process>, QS : QuorumSystem) 
		returns (qR : set<nat>)
		requires valid_distributed_system(S, QS)
		ensures qR in QS.C.Q && qR <= QS.R
	{
		qR :| qR in QS.C.Q && qR <= QS.R;
	}

  lemma {:opaque} proposals_from_messages(S : seq<Process>, QS : QuorumSystem, i : nat, pr : Proposal, t : nat) returns (msg : Message)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires pr in S[i].proposals_hist[t]
		requires S[pr.id].NBProcess?
		ensures msg in S[pr.id].outbox && msg.rnd == t && msg.src == pr.id && msg.val == pr.val
	{
		assert exists m :: m in S[i].inbox && m.src == pr.id && m.rnd == t && m.val == pr.val;
		msg :| msg in S[i].inbox && msg.src == pr.id && msg.rnd == t && msg.val == pr.val;
		assert msg in S[pr.id].outbox;
	}

	lemma {:opaque} proposals_from_messages_byz(S : seq<Process>, QS : QuorumSystem, i : nat, pr : Proposal, t : nat) returns (msg : Message, j : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires pr in S[i].proposals_hist[t]
		ensures 0 <= j < |S|
		ensures msg in S[j].outbox && msg.rnd == t && msg.val == pr.val
	{
		assert exists m :: m in S[i].inbox && m.src == pr.id && m.rnd == t && m.val == pr.val;
		msg :| msg in S[i].inbox && msg.src == pr.id && msg.rnd == t && msg.val == pr.val;
		assert exists j :: 0 <= j < |S| && msg in S[j].outbox;
		j :| 0 <= j < |S| && msg in S[j].outbox;
	}

	lemma {:opaque} proposals_from_vals(S : seq<Process>, QS : QuorumSystem, i : nat, pr : Proposal, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires pr in S[i].proposals_hist[t]
		requires S[pr.id].NBProcess?
		ensures t <= S[pr.id].rnd
		ensures S[pr.id].val_hist[t] == pr.val;
	{
		var msg := proposals_from_messages(S, QS, i, pr, t);
		assert msg in S[msg.src].outbox;
		assert msg.val == S[msg.src].val_hist[msg.rnd];
	}

	lemma {:opaque} proposals_from_results(S : seq<Process>, QS : QuorumSystem, i : nat, pr : Proposal, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 1 <= t < S[i].rnd
		requires pr in S[i].proposals_hist[t]
		requires S[pr.id].NBProcess?
		ensures S[pr.id].re_hist[t - 1].val == pr.val
	{
		proposals_from_vals(S, QS, i, pr, t);
		assert S[pr.id].val_hist[t] == S[pr.id].re_hist[t-1].val;
	}

	lemma {:opaque} proposals_from_results'(S : seq<Process>, QS : QuorumSystem, i : nat, pr : Proposal, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= t + 1 < S[i].rnd
		requires pr in S[i].proposals_hist[t + 1]
		requires S[pr.id].NBProcess?
		ensures S[pr.id].re_hist[t].val == pr.val
	{
		proposals_from_results(S, QS, i, pr, t + 1);
	}

	lemma {:opaque} unique_proposals_by_nonbyzantine_process(S : seq<Process>, QS : QuorumSystem, i : nat, j : nat, pr_i : Proposal, pr_j : Proposal, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= j < |S| && S[j].NBProcess?
		requires 0 <= t < S[i].rnd
		requires t < S[j].rnd
		requires pr_i in S[i].proposals_hist[t]
		requires pr_j in S[j].proposals_hist[t]
		requires pr_i.id == pr_j.id
		requires S[pr_i.id].NBProcess?
		ensures pr_i == pr_j
	{
		var m_i := proposals_from_messages(S, QS, i, pr_i, t);

		var m_j := proposals_from_messages(S, QS, j, pr_j, t);

		assert pr_j.id == pr_i.id;
		assert m_i in S[pr_i.id].outbox && m_j in S[pr_j.id].outbox;
		assert m_i.rnd == m_j.rnd == t;
		UBosco.single_message_per_round(S[pr_i.id]);
		assert m_i == m_j;

		assert pr_i == pr_j;
	}
}

