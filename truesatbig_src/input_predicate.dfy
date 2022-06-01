include "int32.dfy"

module InputPredicate {
  import Int32

  function countLiterals(clauses : seq<seq<Int32.t>>) : int
  {
    if |clauses| == 0 then 0
    else |clauses[|clauses|-1]| + countLiterals(clauses[..|clauses|-1])
  }

  predicate checkClauses(variablesCount: Int32.t, clauses : seq<seq<Int32.t>>) {
    countLiterals(clauses) < Int32.max as int &&
    forall clause :: (clause in clauses) ==>
      0 < |clause| < Int32.max as int &&
      forall literal :: (literal in clause) ==> (
        (literal < 0 && 0 < -literal <= variablesCount) ||
        (literal > 0 && 0 < literal <= variablesCount))
  }
  
  predicate sortedClauses(clauses : seq<seq<Int32.t>>) {
    forall clause :: (clause in clauses) ==>
      forall x, y :: 0 <= x < y < |clause| ==>
        clause[x] < clause[y]
  }

  predicate valid(input : (Int32.t, seq<seq<Int32.t>>)) {
    (0 < input.0 < Int32.max) &&

    (0 < |input.1| <= Int32.max as int) &&

    checkClauses(input.0, input.1) &&

    sortedClauses(input.1)
  }
}
