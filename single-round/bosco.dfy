
module LBosco {

  export Interface
    provides step_system
    reveals Status, Proposal, LBResult, unanimous_proposals, unanimous_intersect, valid_system, agreement, validity, unanimity, quorum_intersection_unanimity

  export Types reveals Status

  /* U is "undecided", M is "maybe", D is "decide" */
  datatype Status = U | M | D

    
  /* Proposal(p, i) abstracts a process proposing value with unique identifier i */
  datatype Proposal<T(==)> = Proposal(value : T, id : nat)

  /* LBResult(v, s, q, q', p) represents the result of a step producing value v and status s, 
   * with q, q', and p being "evidence" for the result.
   * - q is the quorum that was stepped to produce this result.
   * - if s == M, then q' is a quorum that intersects unanimously with q. Otherwise, q' is just q.
   * - p is a proposal whose value is the same as v. */
  datatype LBResult<T(==)> = LBResult(value : T, status : Status, q : set<Proposal<T>>, q' : set<Proposal<T>>, p : Proposal<T>)

  /* unanimous_proposals(P, v) is true when every proposal in P proposes v */
  predicate unanimous_proposals<T(==)>(P : set<Proposal<T>>, v : T){
    forall p :: p in P ==> p.value == v
  }

  /* unanimous_intersect(q, q', v) is true when every proposal in the intersection 
   * of q and q' proposes v (and the intersection is non-empty) */
  predicate unanimous_intersect<T(==)>(q : set<Proposal<T>>, q' : set<Proposal<T>>, v : T){
    q * q' != {} && (forall p :: p in q * q' ==> p.value == v)
  }

  /* valid_system(P, Q) is true when P and Q constitute a valid set of proposals
   * and quorum system for those proposals, respectively. */
  predicate valid_system<T(==)>(P : set<Proposal<T>>, Q : set<set<Proposal<T>>>)
  {
    // P and Q are non-empty
    P != {} && Q != {}
    // every element of Q is a subset of P
    && (forall q :: q in Q ==> q <= P)
    // Q satisfies 3-Intersection
    && (forall q1, q2, q3 :: q1 in Q && q2 in Q && q3 in Q ==> q1 * q2 * q3 != {})
    // no two proposals in P have the same id
    && (forall p1, p2 | p1 in P && p2 in P :: p1 != p2 ==> p1.id != p2.id)
  }

  /* valid_result(s, P, Q) is true when s represents a valid result of a step in 
   * the quorum system represented by P and Q */
  predicate valid_result<T(!new)>(s : LBResult<T>, P : set<Proposal<T>>, Q : set<set<Proposal<T>>>)
  {
    // sets used as evidence are quorums
    s.q in Q && s.q' in Q
    // value was proposed by some process in P
    && s.value == s.p.value && s.p in P
    // if decided, then the quorum being stepped was unanimous
    && (s.status == D ==> unanimous_proposals(s.q, s.value))
    // if some quorum intersects unanimously with the quorum being stepped, then status is Maybe or Decide, and the value is taken from this intersection
    && (forall q', v :: q' in Q && unanimous_intersect(s.q, q', v) ==> (s.status == M || s.status == D) && s.value == v)
    // if proposals were unanimous in some value, then that value is decided
    && (forall v :: unanimous_proposals(P, v) ==> s.value == v && s.status == D)
  }

  predicate agreement<T(==)>(S : set<LBResult<T>>)
  {
    forall s :: s in S && s.status == D ==>
      (forall s' :: s' in S ==> (s'.status == D || s'.status == M) && s'.value == s.value)
  }

  predicate unanimity<T(!new)>(P : set<Proposal<T>>, S : set<LBResult<T>>)
  {
    forall v :: unanimous_proposals(P, v) ==>
      (forall s :: s in S ==> s.value == v && s.status == D)
  }

  predicate validity<T(==)>(P : set<Proposal<T>>, S : set<LBResult<T>>)
  {
    forall s :: s in S ==> s.value == s.p.value && s.p in P
  }
	
	predicate quorum_intersection_unanimity<T(!new)>(P : set<Proposal>, Q : set<set<Proposal>>, S : set<LBResult>)
	{
		forall q1, v, id :: q1 in Q && Proposal(v, id) in P && (forall q2 :: q2 in Q ==> unanimous_intersect(q1, q2, v)) ==>
			(forall s :: s in S ==> s.value == v && (s.status == D || s.status == M))
	}

  /* Helper lemma for guaranteeing agreement over valid results of stepping. */
  lemma agreement_lemma<T(==)>(P : set<Proposal<T>>, Q : set<set<Proposal<T>>>, S : set<LBResult<T>>)
    requires valid_system(P, Q)
    requires forall s :: s in S ==> s.q in Q
    requires forall s :: s in S && s.status == D ==> unanimous_proposals(s.q, s.value)
    requires forall s, q', v :: s in S && q' in Q && unanimous_intersect(s.q, q', v) ==> (s.status == M || s.status == D) && s.value == v
    ensures agreement(S)
  {
    forall s | s in S && s.status == D
      ensures (forall s' :: s' in S ==> (s'.status == D || s'.status == M) && s'.value == s.value)
    {
      forall s' | s' in S
        ensures (s'.status == D || s'.status == M) && s'.value == s.value
      {
        assert unanimous_proposals(s.q, s.value);
        assert unanimous_intersect(s.q, s'.q, s.value);
        assert unanimous_intersect(s'.q, s.q, s.value);
        assert s'.status == M || s'.status == D;
        assert s'.value == s.value;
      }
    }
  }

	lemma quorum_intersection_unanimity_lemma<T(!new)>(P : set<Proposal>, Q : set<set<Proposal>>, S : set<LBResult>)
		requires forall s :: s in S ==> valid_result(s, P, Q)
		ensures quorum_intersection_unanimity(P, Q, S)
	{
		forall q1, v, id | q1 in Q && Proposal(v, id) in P && (forall q2 :: q2 in Q ==> unanimous_intersect(q1, q2, v))
			ensures forall s :: s in S ==> s.value == v && (s.status == D || s.status == M)
		{
			forall s | s in S
				ensures s.value == v && (s.status == D || s.status == M)
			{
				assert unanimous_intersect(s.q, q1, v);
			}
		}
	}

  /* Helper lemma for reasoning about 3 intersecting quorums in a valid system. */
  lemma unanimous_intersect_3<T(==)>(P : set<Proposal<T>>, Q : set<set<Proposal<T>>>, q : set<Proposal<T>>, q' : set<Proposal<T>>, q'' : set<Proposal<T>>, v : T, v' : T)
    requires valid_system(P, Q)
    requires q in Q && q' in Q && q'' in Q
    requires unanimous_intersect(q, q', v)
    requires unanimous_intersect(q, q'', v')
    ensures v == v'
  {}

  /* step_quorum(q, P, Q) is the result of stepping q in system P, Q. */
  method step_quorum<T(==)>(q : set<Proposal<T>>, P : set<Proposal<T>>, Q : set<set<Proposal<T>>>) returns (s : LBResult<T>)
    requires valid_system(P, Q)
    requires q in Q
    ensures valid_result(s, P, Q)
  {
    if (forall p1, p2 | p1 in q && p2 in q :: p1.value == p2.value)
    {
      var p :| p in q;
      s := LBResult(p.value, D, q, q, p);
      forall q', v | q' in Q && unanimous_intersect(s.q, q', v)
        ensures s.value == v
      {}
    }
    else if exists q' | q' in Q :: 
      (forall p1, p2 | p1 in (q * q') && p2 in (q * q') :: p1.value == p2.value) 
    {
      var q' :| q' in Q && (forall p1, p2 | p1 in (q * q') && p2 in (q * q') :: p1.value == p2.value);
      var p :| p in (q * q');
      s := LBResult(p.value, M, q, q', p);
      forall q'', v | q'' in Q && unanimous_intersect(s.q, q'', v)
        ensures s.value == v
      {
        unanimous_intersect_3(P, Q, s.q, s.q', q'', s.value, v);
      }
    }
    else {
      var p :| p in P;
      s := LBResult(p.value, U, q, q, p);
    }    
  }

  /* step_system(P, Q) is the result of stepping all of the quorums in the system P, Q, 
   * guaranteeing agreement, validity, and unanimity on the results. */
  method step_system<T(==)>(P : set<Proposal<T>>, Q : set<set<Proposal<T>>>)
		returns (S : set<LBResult<T>>)
    requires valid_system(P, Q)
    ensures agreement(S)
    ensures unanimity(P, S)
		ensures quorum_intersection_unanimity(P, Q, S)
    ensures validity(P, S)
  {
    S := {};
    var Q' := {};
    while Q' != Q
      invariant valid_system(P, Q)
      invariant forall s :: s in S ==> valid_result(s, P, Q)
      invariant Q' <= Q
      decreases Q - Q'
    {
      var q :| q in Q - Q';
      Q' := Q' + {q};
      var r := step_quorum(q, P, Q);
      S := S + {r};
    }
    assert (forall s :: s in S ==> s.q in Q);
    assert (forall s :: s in S && s.status == D ==> unanimous_proposals(s.q, s.value));
    assert (forall s, q', v :: s in S && q' in Q && unanimous_intersect(s.q, q', v) ==> (s.status == M || s.status == D) && s.value == v);
    agreement_lemma(P, Q, S);
		quorum_intersection_unanimity_lemma(P, Q, S);
    assert (forall s :: s in S ==> s.value == s.p.value && s.p in P);
  }
}
  
  
