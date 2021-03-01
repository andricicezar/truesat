include "../int32.dfy"

module Utils {
  import Int32

  method newInitializedSeq(n: Int32.t, d: Int32.t) returns (r : array<Int32.t>)
    requires 0 < n;
    ensures r.Length == n as int;
    ensures forall j :: 0 <= j < r.Length ==> r[j] == d;
    ensures fresh(r);
  {
    r := new Int32.t[n];

    var index : Int32.t := 0;
    while (index < n)
      invariant 0 <= index as int <= r.Length == n as int;
      invariant forall j :: 0 <= j < index ==> r[j] == d;    
      decreases n - index;
    {
      r[index] := d;
      index := index + 1;
    }
  }

  function method abs(literal: Int32.t) : Int32.t {
    if literal < 0 then - literal else literal
  }

  /* function method properClause(clause : seq<Int32.t>) : bool {*/
  /*   forall literal :: (literal in clause) ==> literal != 0*/
  /* }*/

  /* function method properClauses(clauses : seq<seq<Int32.t>>) : bool {*/
  /*   |clauses| > 0 &&*/
  /*   forall clause :: (clause in clauses) ==> properClause(clause)*/
  /* }*/
  
  lemma prop_seq_predicate(q : int, abc : seq<Int32.t>) 
    requires forall j :: j in abc ==> 0 <= j as int < q;
    ensures forall j :: 0 <= j < |abc| ==> 0 <= abc[j] as int < q;
  {
    assert forall j :: 0 <= j < |abc| ==> 
              abc[j] in abc ==> 0 <= abc[j] as int < q;
  }

  predicate valueBoundedBy(value : Int32.t, min : int, max : int) {
    min <= value as int < max
  }

  predicate valuesBoundedBy(s: seq<Int32.t>, min : int, max: int) {
    (forall el :: el in s ==>
      valueBoundedBy(el, min, max)) &&
    (forall i :: 0 <= i < |s| ==>
      valueBoundedBy(s[i], min, max))
  }

  predicate orderedAsc(s : seq<Int32.t>) {
    forall x, y :: 0 <= x < y < |s| ==> s[x] < s[y]
  }

  predicate InRange(lo : Int32.t, hi : Int32.t, i : Int32.t) {
    lo <= i < hi
  }

  function RangeSet(lo: Int32.t, hi: Int32.t): set<Int32.t>
  {
      set i | lo <= i < hi && InRange(lo, hi, i)
  }

  lemma CardinalityRangeSet(lo: Int32.t, hi: Int32.t)
      requires 0 <= lo <= hi
      decreases hi - lo
      ensures |RangeSet(lo, hi)| == if lo >= hi then 0 else (hi - lo) 
        as int
  {
      if lo < hi {
          assert RangeSet(lo, hi) == {lo} + RangeSet(lo + 1, hi);
          CardinalityRangeSet(lo + 1, hi);
      }
  }
}
