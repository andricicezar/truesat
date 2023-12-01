include "formula.dfy"
include "../int32.dfy"

datatype SAT_UNSAT = SAT(tau:seq<Int32.t>) | UNSAT

class SATSolver {
  var formula : Formula;

  constructor(f' : Formula)
    requires f'.valid();
    ensures formula == f';
    ensures formula.valid();
  {
    formula := f';
  }

  method step(literal : Int32.t, value : bool) returns (result : SAT_UNSAT)
    requires formula.valid();
    requires formula.decisionLevel < formula.variablesCount - 1; // not full
    requires formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];
    requires !formula.hasEmptyClause();
    requires !formula.isEmpty();
    requires formula.validLiteral(literal);
    requires formula.getLiteralValue(formula.truthAssignment[..], literal) == -1;

    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
             formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
             formula`assignmentsTrace, formula.trueLiteralsCount,
             formula.falseLiteralsCount;

    ensures formula.valid();
    ensures !formula.hasEmptyClause();
    ensures old(formula.decisionLevel) == formula.decisionLevel;
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace;
    ensures forall i :: 0 <= i <= formula.decisionLevel ==>
      old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i);
    ensures formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];
    ensures !formula.isEmpty();

    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> (
      var (variable, val) := formula.convertLVtoVI(literal, value);
      formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val]));
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)

    ensures result.UNSAT? ==> (
      var (variable, val) := formula.convertLVtoVI(literal, value);
      !formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val]));

    ensures formula.countUnsetVariables(formula.truthAssignment[..]) ==
      formula.countUnsetVariables(old(formula.truthAssignment[..]));

    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 0;
  {
    formula.increaseDecisionLevel();
    formula.setLiteral(literal, value);
    result := solve();
    formula.revertLastDecisionLevel();

    if (formula.truthAssignment[..] != old(formula.truthAssignment[..])) {
      ghost var i : Int32.t :| 0 <= i as int < formula.truthAssignment.Length &&
              formula.truthAssignment[i] != old(formula.truthAssignment[i]);

      ghost var y : (Int32.t, bool) := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));
      assert false;
    }

    return result;
  }

  method solve() returns (result : SAT_UNSAT)
    requires formula.valid();
    requires formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];

    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
             formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
             formula`assignmentsTrace, formula.trueLiteralsCount,
             formula.falseLiteralsCount;

    ensures formula.valid();
    ensures old(formula.decisionLevel) == formula.decisionLevel;
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace;
    ensures forall i :: 0 <= i <= formula.decisionLevel ==>
      old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i);
    ensures formula.decisionLevel > -1 ==>
      formula.traceDLStart[formula.decisionLevel] <
        formula.traceDLEnd[formula.decisionLevel];

    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(formula.truthAssignment[..]);
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(formula.truthAssignment[..]);
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) ==
      formula.countUnsetVariables(old(formula.truthAssignment[..]));

    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 1;
  {
    var hasEmptyClause : bool := formula.getHasEmptyClause();
    if (hasEmptyClause) {
      formula.hasEmptyClause_notSatisfiable();
      return UNSAT;
    }

    var isEmpty : bool := formula.getIsEmpty();
    if (isEmpty) {
      formula.isEmpty_sastisfied();
      result := SAT(formula.truthAssignment[..]);
      assert formula.validValuesTruthAssignment(result.tau);
      return result;
    }

    var literal := formula.chooseLiteral();

    formula.notEmptyNoEmptyClauses_traceNotFull();
    result := step(literal, true);

    if (result.SAT?) {
      return result;
    }

    result := step(literal, false);

    if (result.UNSAT?) {
      ghost var variable := formula.getVariableFromLiteral(literal);
      formula.forVariableNotSatisfiableExtend_notSatisfiableExtend(
        formula.truthAssignment[..],
        variable
      );
    }

    return result;
  }

  /** in a way it is weird that solve does not know in any way about the
  level0unitPropagation. **/
  method start() returns (result : SAT_UNSAT)
    requires formula.valid();
    requires formula.decisionLevel == -1;

    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue,
             formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel,
             formula`assignmentsTrace, formula.trueLiteralsCount,
             formula.falseLiteralsCount;

    ensures formula.valid();
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau);
    ensures result.SAT? ==> formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==>
      !formula.isSatisfiableExtend(old(formula.truthAssignment[..]));
  {
    formula.level0UnitPropagation();
    result := solve();
  }
}
