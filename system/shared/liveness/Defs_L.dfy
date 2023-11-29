include "../Types.dfy"

module Defs_L {

  import opened Types

  predicate started_rnd(p : Process, r : nat)
		requires p.NBProcess?
	{
		r <= p.rnd
	}

	predicate valid_qR(S : seq<Process>, QS : QuorumSystem, qR : set<nat>)
	{
		qR in QS.C.Q
		&& qR <= QS.R
		&& (forall id :: id in qR ==> 0 <= id < |S| && S[id].NBProcess?)
		&& (exists p :: p in S && p.id in qR && p.NBProcess?)
	}
	
	function method has_msgs_from_quorum(p : Process, Q : set<set<nat>>) : bool
		requires p.NBProcess?
	{
		exists q :: q in Q && q <= (set msg | msg in p.inbox && msg.rnd == p.rnd :: msg.src)
	}

	function method min_rnd_subset(S : seq<Process>, R : set<nat>) : nat
		requires exists p :: p in S && p.id in R && p.NBProcess?
		ensures forall p : Process :: p in S && p.id in R && p.NBProcess? ==> min_rnd_subset(S, R) <= p.rnd
		ensures exists p | p in S && p.id in R && p.NBProcess? :: p.rnd == min_rnd_subset(S, R)
	{
		if |S| == 1 || !(exists i :: 1 <= i < |S| && S[i].id in R && S[i].NBProcess?) then S[0].rnd
		else
			var min' := min_rnd_subset(S[1..], R);
			if S[0].BProcess? || (min' <= S[0].rnd || S[0].id !in R) then min' else S[0].rnd
	}

	method instantiate_min_rnd_subset(S : seq<Process>, R : set<nat>) returns (p : Process)
		requires exists p :: p in S && p.id in R && p.NBProcess?
		ensures p in S && p.id in R && p.NBProcess? && p.rnd == min_rnd_subset(S, R)
	{
		var i :| 0 <= i < |S| && S[i].id in R && S[i].NBProcess? && S[i].rnd == min_rnd_subset(S, R);
		p := S[i];
	}

	function method sum_rnd_subset(S : seq<Process>, R : set<nat>) : nat
	{
		if S == [] then 0
		else
			if S[0].NBProcess? && S[0].id in R then S[0].rnd + sum_rnd_subset(S[1..], R)
			else sum_rnd_subset(S[1..], R)
	}

	function method sum_rnd_replace_subset(S : seq<Process>, R : set<nat>, rnd : nat) : nat
	{
		if S == [] then 0
		else
			if S[0].NBProcess? && S[0].id in R then
			  if S[0].rnd <= rnd then rnd + sum_rnd_replace_subset(S[1..], R, rnd)
			  else S[0].rnd + sum_rnd_replace_subset(S[1..], R, rnd)
			else sum_rnd_replace_subset(S[1..], R, rnd)
	}
}


module Defs_LProof refines Defs_L {

  lemma sum_rnd_subset_hd(S : seq<Process>, R : set<nat>)
		requires S != []
		requires S[0].NBProcess?
		requires S[0].id in R
		ensures sum_rnd_subset(S, R) == S[0].rnd + sum_rnd_subset(S[1..], R)
	{}
	
	
	lemma sum_rnd_replace_subset_hd_lte(S : seq<Process>, R : set<nat>, rnd : nat)
		requires S != []
		requires S[0].NBProcess?
		requires S[0].id in R
		requires S[0].rnd <= rnd
		ensures sum_rnd_replace_subset(S, R, rnd) == rnd + sum_rnd_replace_subset(S[1..], R, rnd)
	{}


	lemma sum_rnd_replace_subset_hd_ge(S : seq<Process>, R : set<nat>, rnd : nat)
		requires S != []
		requires S[0].id in R
		requires S[0].NBProcess?
		requires S[0].rnd >= rnd
		ensures sum_rnd_replace_subset(S, R, rnd) == S[0].rnd + sum_rnd_replace_subset(S[1..], R, rnd)
	{}
	
	lemma sum_rnd_replace_subset_lte(S : seq<Process>, R : set<nat>, rnd : nat)
		ensures sum_rnd_subset(S, R) <= sum_rnd_replace_subset(S, R, rnd)
	{
		if (S == []) {
		} else {
			sum_rnd_replace_subset_lte(S[1..], R, rnd);
		}
	}


	lemma sum_rnd_replace_subset_eq(S : seq<Process>, R : set<nat>, rnd : nat)
		requires sum_rnd_subset(S, R) == sum_rnd_replace_subset(S, R, rnd)
		ensures forall p :: p in S && p.id in R && p.NBProcess? ==> p.rnd >= rnd
	{
		if (S == []) {
		} else {
			if (S[0].id in R && S[0].NBProcess?) {
				if (S[0].rnd <= rnd) {
					assert S[0].rnd + sum_rnd_subset(S[1..], R) == rnd + sum_rnd_replace_subset(S[1..], R, rnd);
					sum_rnd_replace_subset_lte(S[1..], R, rnd);
					assert S[0].rnd >= rnd;
					sum_rnd_replace_subset_eq(S[1..], R, rnd);
				} else {
					assert sum_rnd_subset(S, R) == sum_rnd_replace_subset(S, R, rnd);
					assert S[0].rnd + sum_rnd_subset(S[1..], R) == S[0].rnd + sum_rnd_replace_subset(S[1..], R, rnd);
					sum_rnd_replace_subset_eq(S[1..], R, rnd);
				}
			} else {
				assert sum_rnd_subset(S, R) == sum_rnd_replace_subset(S, R, rnd);
				assert sum_rnd_subset(S[1..], R) == sum_rnd_replace_subset(S[1..], R, rnd);
				sum_rnd_replace_subset_eq(S[1..], R, rnd);
			}
		}
	}

	lemma sum_rnd_replace_subset_eq_conv(S : seq<Process>, R : set<nat>, rnd : nat)
		requires forall p :: p in S && p.id in R && p.NBProcess? ==> p.rnd >= rnd
		ensures sum_rnd_subset(S, R) == sum_rnd_replace_subset(S, R, rnd)
	{}


	lemma sum_rnd_subset_same_seq(S1 : seq<Process>, S2 : seq<Process>, R : set<nat>)
		requires |S1| == |S2|
		requires forall j :: 0 <= j < |S1| ==> S1[j].id == S2[j].id
		requires forall j :: 0 <= j < |S1| ==> (S1[j].NBProcess? <==> S2[j].NBProcess?)
		requires forall j :: 0 <= j < |S1| && S1[j].NBProcess? ==> S1[j].rnd == S2[j].rnd
		ensures sum_rnd_subset(S1, R) == sum_rnd_subset(S2, R)
	{}

	lemma sum_rnd_replace_subset_same_seq(S1 : seq<Process>, S2 : seq<Process>, R : set<nat>, rnd : nat)
		requires |S1| == |S2|
		requires forall j :: 0 <= j < |S1| ==> S1[j].id == S2[j].id
		requires forall j :: 0 <= j < |S1| ==> (S1[j].NBProcess? <==> S2[j].NBProcess?)
		requires forall j :: 0 <= j < |S1| && S1[j].NBProcess? ==> S1[j].rnd == S2[j].rnd
		ensures sum_rnd_replace_subset(S1, R, rnd) == sum_rnd_replace_subset(S2, R, rnd)
	{}

	lemma sum_rnd_incr(S1 : seq<Process>, S2 : seq<Process>, R : set<nat>, i : nat)
		requires |S1| == |S2|
		requires forall j :: 0 <= j < |S1| ==> S1[j].id == S2[j].id
		requires forall j :: 0 <= j < |S1| ==> (S1[j].NBProcess? <==> S2[j].NBProcess?)
		requires forall j :: 0 <= j < |S1| && S1[j].NBProcess? && j != i ==> S1[j].rnd == S2[j].rnd
		requires 0 <= i < |S1|
		requires S1[i].id in R
		requires S1[i].NBProcess?
		requires S1[i].rnd + 1 == S2[i].rnd
		ensures sum_rnd_subset(S1, R) + 1 == sum_rnd_subset(S2, R)
	{
		if (i == 0) {
			assert S1[0].id in R;
			sum_rnd_subset_hd(S1, R);
			sum_rnd_subset_hd(S2, R);
			sum_rnd_subset_same_seq(S1[1..], S2[1..], R);
		} else {
			sum_rnd_incr(S1[1..], S2[1..], R, i - 1);
		}
	}


	lemma sum_rnd_replace_subset_incr(S1 : seq<Process>, S2 : seq<Process>, i : nat, R : set<nat>, rnd : nat)
		requires |S1| == |S2|
		requires forall j :: 0 <= j < |S1| ==> S1[j].id == S2[j].id
		requires forall j :: 0 <= j < |S1| ==> (S1[j].NBProcess? <==> S2[j].NBProcess?)
		requires forall j :: 0 <= j < |S1| && S1[j].NBProcess? && j != i ==> S1[j].rnd == S2[j].rnd
		requires 0 <= i < |S1|
		requires S1[i].id in R
		requires S1[i].NBProcess?
		requires S1[i].rnd < rnd
		requires S2[i].rnd == S1[i].rnd + 1
		ensures sum_rnd_replace_subset(S1, R, rnd) == sum_rnd_replace_subset(S2, R, rnd)
	{
		if (i == 0) {
			assert S1[i].id in R;
			assert S1[0].rnd <= rnd;
			assert S2[0].rnd <= rnd;
			sum_rnd_replace_subset_hd_lte(S1, R, rnd);
			sum_rnd_replace_subset_hd_lte(S2, R, rnd);
			sum_rnd_replace_subset_same_seq(S1[1..], S2[1..], R, rnd);
		} else {
			sum_rnd_replace_subset_incr(S1[1..], S2[1..], i - 1, R, rnd);
			assert sum_rnd_replace_subset(S1[1..], R, rnd) == sum_rnd_replace_subset(S2[1..], R, rnd);
			if (S1[0].id in R && S1[0].NBProcess? && S1[0].rnd <= rnd) {
				sum_rnd_replace_subset_hd_lte(S1, R, rnd);
				sum_rnd_replace_subset_hd_lte(S2, R, rnd);
			} else {
				
			}
		}
	}

	lemma sum_rnd_replace_subset_eq_iff_min_eq(S : seq<Process>, R : set<nat>, rnd : nat)
		requires exists p :: p in S && p.id in R && p.NBProcess?
		requires min_rnd_subset(S, R) <= rnd
		ensures min_rnd_subset(S, R) == rnd <==> sum_rnd_replace_subset(S, R, rnd) == sum_rnd_subset(S, R)
	{
		if (min_rnd_subset(S, R) == rnd) {
			assert forall p :: p in S && p.id in R && p.NBProcess? ==> rnd <= p.rnd;
			sum_rnd_replace_subset_eq_conv(S, R, rnd);
		}
		if (sum_rnd_replace_subset(S, R, rnd) == sum_rnd_subset(S, R)) {
			sum_rnd_replace_subset_eq(S, R, rnd);
			var i :| 0 <= i < |S| && S[i].id in R && S[i].NBProcess? && S[i].rnd == min_rnd_subset(S, R);
			var p := S[i];
			if (p.rnd <= rnd) {
				assert p.id in R;
				assert p.rnd == rnd;
			} else {
				assert rnd < p.rnd;
				assert min_rnd_subset(S, R) <= rnd;
				assert false;
			}
			assert p.rnd == rnd;
		}
	}

	lemma sum_rnd_lt_implies_member(S : seq<Process>, R : set<nat>, rnd : nat)
		requires sum_rnd_subset(S, R) < sum_rnd_replace_subset(S, R, rnd)
		ensures exists p :: p in S && p.id in R && p.NBProcess?
	{
		if (S == []) {
			assert sum_rnd_subset(S, R) == 0;
			assert sum_rnd_replace_subset(S, R, rnd) == 0;
			assert false;
		} else {
			if (S[0].id !in R || S[0].BProcess?) {
				sum_rnd_lt_implies_member(S[1..], R, rnd);
			} else {
				assert S[0].id in R && S[0].NBProcess?;
			}
		}
	}
	
	lemma min_rnd_lt_if_sum_rnd_lt(S : seq<Process>, R : set<nat>, rnd : nat)
		requires exists p :: p in S && p.id in R && p.NBProcess?
		requires sum_rnd_subset(S, R) < sum_rnd_replace_subset(S, R, rnd)
		ensures min_rnd_subset(S, R) < rnd
	{
		if (S == []) {

		} else if (|S| == 1) {
			var i :| 0 <= i < |S| && S[i].id in R && S[i].NBProcess? && S[i].rnd == min_rnd_subset(S, R);
			var p := S[i];
			assert sum_rnd_subset(S, R) == p.rnd;
			assert sum_rnd_replace_subset(S, R, rnd) == rnd;
			assert p.rnd < rnd;
		} else {
			if (S[0].id in R && S[0].NBProcess?) {
				if (S[0].rnd < rnd) {
					var i :| 0 <= i < |S| && S[i].id in R && S[i].NBProcess? && S[i].rnd == min_rnd_subset(S, R);
					var p := S[i];
					assert p.rnd <= S[0].rnd;
				} else {
					sum_rnd_subset_hd(S, R);
					sum_rnd_replace_subset_hd_ge(S, R, rnd);
					assert sum_rnd_subset(S[1..], R) < sum_rnd_replace_subset(S[1..], R, rnd);
					sum_rnd_lt_implies_member(S[1..], R, rnd);
					min_rnd_lt_if_sum_rnd_lt(S[1..], R, rnd);
				}
			} else {
				min_rnd_lt_if_sum_rnd_lt(S[1..], R, rnd);
			}
		}
	}
}
