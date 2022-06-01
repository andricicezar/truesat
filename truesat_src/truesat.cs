// Dafny program truesat.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.6.0.40511
// Command Line Options: /compileTarget:cs /compileVerbose:1 /spillTargetCode:1 /compile:2 truesat.dfy file_input.cs
// truesat.dfy

method Main()
{
  var starttime := Input.getTimestamp();
  var input := Input.getInput();
  var totalTime: real := (Input.getTimestamp() - starttime) as real / 1000.0;
  print ""c Time to read: "", totalTime, ""s\n"";
  match input {
    case {:split false} Error(m) =>
      print ""c Error: "", m, ""\n"";
    case {:split false} Just(z) =>
      var (variablesCount, clauses) := z;
      starttime := Input.getTimestamp();
      var formula := new Formula(variablesCount, clauses);
      var solver := new SATSolver(formula);
      totalTime := (Input.getTimestamp() - starttime) as real / 1000.0;
      print ""c Time to initialize: "", totalTime, ""s\n"";
      starttime := Input.getTimestamp();
      var solution := solver.start();
      totalTime := (Input.getTimestamp() - starttime) as real / 1000.0;
      print ""c Time to solve: "", totalTime, ""s\n"";
      match solution {
        case {:split false} SAT(x) =>
          print ""s SATISFIABLE\n"";
        case {:split false} UNSAT =>
          print ""s UNSATISFIABLE\n"";
      }
  }
}

module Int32 {
  newtype {:nativeType ""int""} t = x: int
    | -2000000 <= x < 2000001

  const max: t := 2000000
  const min: t := -2000000

  ghost method test(x: t)
    decreases x
  {
    ghost var m1: t := -x;
  }
}

datatype SAT_UNSAT = SAT(tau: seq<Int32.t>) | UNSAT

class SATSolver {
  var formula: Formula

  constructor (f': Formula)
    requires f'.valid()
    ensures formula == f'
    ensures formula.valid()
    decreases f'
  {
    formula := f';
  }

  method step(literal: Int32.t, value: bool) returns (result: SAT_UNSAT)
    requires formula.valid()
    requires formula.decisionLevel < formula.variablesCount - 1
    requires formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    requires !formula.hasEmptyClause()
    requires !formula.isEmpty()
    requires formula.validLiteral(literal)
    requires formula.getLiteralValue(formula.truthAssignment[..], literal) == -1
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue, formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel, formula`assignmentsTrace, formula.trueLiteralsCount, formula.falseLiteralsCount
    ensures formula.valid()
    ensures !formula.hasEmptyClause()
    ensures old(formula.decisionLevel) == formula.decisionLevel
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace
    ensures forall i: Int32.t :: 0 <= i <= formula.decisionLevel ==> old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i)
    ensures formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    ensures !formula.isEmpty()
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> var (variable: Int32.t, val: Int32.t) := formula.convertLVtoVI(literal, value); formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val])
    ensures result.UNSAT? ==> var (variable: Int32.t, val: Int32.t) := formula.convertLVtoVI(literal, value); !formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val])
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]))
    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 0
  {
    formula.increaseDecisionLevel();
    formula.setLiteral(literal, value);
    result := solve();
    formula.revertLastDecisionLevel();
    if formula.truthAssignment[..] != old(formula.truthAssignment[..]) {
      ghost var i: Int32.t :| 0 <= i as int < formula.truthAssignment.Length && formula.truthAssignment[i] != old(formula.truthAssignment[i]);
      ghost var y: (Int32.t, bool) := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));
      assert false;
    }
    return result;
  }

  method solve() returns (result: SAT_UNSAT)
    requires formula.valid()
    requires formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue, formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel, formula`assignmentsTrace, formula.trueLiteralsCount, formula.falseLiteralsCount
    ensures formula.valid()
    ensures old(formula.decisionLevel) == formula.decisionLevel
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace
    ensures forall i: Int32.t :: 0 <= i <= formula.decisionLevel ==> old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i)
    ensures formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> formula.isSatisfiableExtend(formula.truthAssignment[..])
    ensures result.UNSAT? ==> !formula.isSatisfiableExtend(formula.truthAssignment[..])
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]))
    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 1
  {
    var hasEmptyClause: bool := formula.getHasEmptyClause();
    if hasEmptyClause {
      formula.hasEmptyClause_notSatisfiable();
      return UNSAT;
    }
    var isEmpty: bool := formula.getIsEmpty();
    if isEmpty {
      formula.isEmpty_sastisfied();
      result := SAT(formula.truthAssignment[..]);
      assert formula.validValuesTruthAssignment(result.tau);
      return result;
    }
    var literal := formula.chooseLiteral();
    formula.notEmptyNoEmptyClauses_traceNotFull();
    result := step(literal, true);
    if result.SAT? {
      return result;
    }
    result := step(literal, false);
    if result.UNSAT? {
      ghost var variable := formula.getVariableFromLiteral(literal);
      formula.forVariableNotSatisfiableExtend_notSatisfiableExtend(formula.truthAssignment[..], variable);
    }
    return result;
  }

  method start() returns (result: SAT_UNSAT)
    requires formula.valid()
    requires formula.decisionLevel == -1
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue, formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel, formula`assignmentsTrace, formula.trueLiteralsCount, formula.falseLiteralsCount
    ensures formula.valid()
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> formula.isSatisfiableExtend(old(formula.truthAssignment[..]))
    ensures result.UNSAT? ==> !formula.isSatisfiableExtend(old(formula.truthAssignment[..]))
  {
    formula.level0UnitPropagation();
    result := solve();
  }
}

module Input {

  import Int32

  import opened Useless

  import FileInput

  import opened MyDatatypes

  import InputPredicate
  method getInput() returns (result: Maybe<(Int32.t, seq<seq<Int32.t>>)>)
    ensures result.Just? ==> InputPredicate.valid(result.value)
  {
    var input := FileInput.Reader.getContent();
    if 0 < input.Length < Int32.max as int {
      var parser := new Parser(input);
      var x := parser.parse();
      return x;
    } else {
      return Error(""the file contains more data than Int32.max"");
    }
  }

  function method getTimestamp(): int
  {
    FileInput.Reader.getTimestamp()
  }
}

module MyDatatypes {
  datatype Maybe<T> = Error(string) | Just(value: T)
}

module InputPredicate {

  import Int32
  function countLiterals(clauses: seq<seq<Int32.t>>): int
    decreases clauses
  {
    if |clauses| == 0 then
      0
    else
      |clauses[|clauses| - 1]| + countLiterals(clauses[..|clauses| - 1])
  }

  predicate checkClauses(variablesCount: Int32.t, clauses: seq<seq<Int32.t>>)
    decreases variablesCount, clauses
  {
    countLiterals(clauses) < Int32.max as int &&
    forall clause: seq<Int32.t> :: 
      clause in clauses ==>
        0 < |clause| < Int32.max as int &&
        forall literal: Int32.t :: 
          literal in clause ==>
            (literal < 0 && 0 < -literal <= variablesCount) || (literal > 0 && 0 < literal <= variablesCount)
  }

  predicate sortedClauses(clauses: seq<seq<Int32.t>>)
    decreases clauses
  {
    forall clause: seq<Int32.t> :: 
      clause in clauses ==>
        forall x: int, y: int :: 
          0 <= x < y < |clause| ==>
            clause[x] < clause[y]
  }

  predicate valid(input: (Int32.t, seq<seq<Int32.t>>))
    decreases input
  {
    0 < input.0 < Int32.max &&
    0 < |input.1| <= Int32.max as int &&
    checkClauses(input.0, input.1) &&
    sortedClauses(input.1)
  }
}

class Formula extends DataStructures {
  constructor (variablesCount: Int32.t, clauses: seq<seq<Int32.t>>)
    requires InputPredicate.valid((variablesCount, clauses))
    ensures valid()
    ensures fresh(this.traceVariable) && fresh(this.traceValue) && fresh(this.traceDLStart) && fresh(this.traceDLEnd) && fresh(this.clauseLength) && fresh(this.trueLiteralsCount) && fresh(this.falseLiteralsCount) && fresh(this.positiveLiteralsToClauses) && fresh(this.negativeLiteralsToClauses) && fresh(this.truthAssignment)
    ensures this.decisionLevel == -1
    decreases variablesCount, clauses
  {
    assert 0 < variablesCount < Int32.max;
    assert 0 < |clauses| <= Int32.max as int;
    assert forall clause: seq<Int32.t> :: clause in clauses ==> forall literal: Int32.t :: literal in clause ==> (literal < 0 && 0 < -literal <= variablesCount) || (literal > 0 && 0 < literal <= variablesCount);
    this.variablesCount := variablesCount;
    this.clauses := clauses;
    this.decisionLevel := -1;
    this.traceVariable := new Int32.t[variablesCount];
    this.traceValue := new bool[variablesCount];
    this.traceDLStart := new Int32.t[variablesCount];
    this.traceDLEnd := new Int32.t[variablesCount];
    this.assignmentsTrace := {};
    var clsLength := |clauses| as Int32.t;
    this.clausesCount := clsLength;
    this.clauseLength := new Int32.t[clsLength];
    this.trueLiteralsCount := new Int32.t[clsLength];
    this.falseLiteralsCount := new Int32.t[clsLength];
    this.positiveLiteralsToClauses := new seq<Int32.t>[variablesCount];
    this.negativeLiteralsToClauses := new seq<Int32.t>[variablesCount];
    this.truthAssignment := new Int32.t[variablesCount];
    new;
    var k: Int32.t := 0;
    while k < this.clausesCount
      invariant this.clauseLength.Length == this.clausesCount as int
      invariant forall i: Int32.t :: 0 <= i < k <= this.clausesCount ==> this.clauseLength[i] as int == |clauses[i]|
      invariant 0 <= k <= this.clausesCount
      decreases this.clausesCount as int - k as int
      modifies this.clauseLength
    {
      this.clauseLength[k] := |this.clauses[k]| as Int32.t;
      k := k + 1;
    }
    var index: Int32.t := 0;
    while index < variablesCount
      invariant 0 <= index <= variablesCount
      invariant forall j: Int32.t :: 0 <= j < index ==> truthAssignment[j] == -1
      invariant forall j: Int32.t :: 0 <= j < index && truthAssignment[j] == -1 ==> (j, false) !in assignmentsTrace && (j, true) !in assignmentsTrace
      decreases variablesCount as int - index as int
      modifies truthAssignment
    {
      truthAssignment[index] := -1;
      assert (index, true) !in assignmentsTrace;
      assert (index, false) !in assignmentsTrace;
      index := index + 1;
    }
    this.createTFLArrays();
    this.createPositiveLiteralsToClauses();
    this.createNegativeLiteralsToClauses();
    inputPredicate_countLiterals(clausesCount);
    assert clauses == clauses[..clausesCount];
    assert countLiterals(clausesCount) == InputPredicate.countLiterals(clauses);
  }

  lemma /*{:_induction this, cI}*/ inputPredicate_countLiterals(cI: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= cI <= clausesCount
    ensures countLiterals(cI) == InputPredicate.countLiterals(clauses[..cI])
    decreases cI
  {
  }

  method createTFLArrays()
    requires validReferences()
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validTruthAssignment()
    requires validClauses()
    requires trueLiteralsCount.Length == |clauses|
    requires falseLiteralsCount.Length == |clauses|
    requires forall value: int :: 0 <= value < truthAssignment.Length ==> truthAssignment[value] == -1
    modifies trueLiteralsCount, falseLiteralsCount
    ensures validTrueLiteralsCount(truthAssignment[..])
    ensures validFalseLiteralsCount(truthAssignment[..])
  {
    var i: Int32.t := 0;
    while i < clausesCount
      invariant 0 <= i <= clausesCount
      invariant forall j: Int32.t :: 0 <= j < i ==> trueLiteralsCount[j] == countTrueLiterals(truthAssignment[..], clauses[j])
      invariant forall j: Int32.t :: 0 <= j < i ==> falseLiteralsCount[j] == countFalseLiterals(truthAssignment[..], clauses[j])
      decreases clausesCount - i
    {
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      trueLiteralsCount[i] := 0;
      prop_countFalseLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      falseLiteralsCount[i] := 0;
      i := i + 1;
    }
  }

  method createPositiveLiteralsToClauses()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires positiveLiteralsToClauses.Length == variablesCount as int
    modifies positiveLiteralsToClauses
    ensures validPositiveLiteralsToClauses()
  {
    var variable := 0;
    while variable < variablesCount
      invariant 0 <= variable <= variablesCount
      invariant forall v: Int32.t :: 0 <= v < variable ==> validPositiveLiteralToClause(v, positiveLiteralsToClauses[v])
      invariant forall v: Int32.t :: 0 <= v < variable ==> |positiveLiteralsToClauses[v]| <= clausesCount as int
      decreases variablesCount - variable
    {
      positiveLiteralsToClauses[variable] := [];
      var clauseIndex: Int32.t := 0;
      while clauseIndex < clausesCount
        invariant 0 <= clauseIndex <= clausesCount
        invariant forall v: Int32.t :: 0 <= v < variable ==> validPositiveLiteralToClause(v, positiveLiteralsToClauses[v])
        invariant forall v: Int32.t :: 0 <= v < variable ==> |positiveLiteralsToClauses[v]| <= clausesCount as int
        invariant |positiveLiteralsToClauses[variable]| <= clauseIndex as int
        invariant Utils.valuesBoundedBy(positiveLiteralsToClauses[variable], 0, |clauses|)
        invariant |positiveLiteralsToClauses[variable]| > 0 ==> positiveLiteralsToClauses[variable][|positiveLiteralsToClauses[variable]| - 1] < clauseIndex
        invariant Utils.orderedAsc(positiveLiteralsToClauses[variable])
        invariant forall cI: Int32.t :: cI in positiveLiteralsToClauses[variable] ==> variable + 1 in clauses[cI]
        invariant forall cI: Int32.t :: 0 <= cI < clauseIndex ==> cI !in positiveLiteralsToClauses[variable] ==> variable + 1 !in clauses[cI]
        decreases clausesCount - clauseIndex
      {
        if variable + 1 in clauses[clauseIndex] {
          positiveLiteralsToClauses[variable] := positiveLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }

  method createNegativeLiteralsToClauses()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires negativeLiteralsToClauses.Length == variablesCount as int
    modifies negativeLiteralsToClauses
    ensures validNegativeLiteralsToClauses()
  {
    var variable: Int32.t := 0;
    while variable < variablesCount
      invariant 0 <= variable <= variablesCount
      invariant forall v: Int32.t :: 0 <= v < variable ==> validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
      invariant forall v: Int32.t :: 0 <= v < variable ==> |negativeLiteralsToClauses[v]| <= clausesCount as int
      decreases variablesCount - variable
    {
      negativeLiteralsToClauses[variable] := [];
      var clauseIndex: Int32.t := 0;
      while clauseIndex < clausesCount
        invariant 0 <= clauseIndex <= clausesCount
        invariant forall v: Int32.t :: 0 <= v < variable ==> validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
        invariant forall v: Int32.t :: 0 <= v < variable ==> |negativeLiteralsToClauses[v]| <= clausesCount as int
        invariant |negativeLiteralsToClauses[variable]| <= clauseIndex as int
        invariant Utils.valuesBoundedBy(negativeLiteralsToClauses[variable], 0, |clauses|)
        invariant |negativeLiteralsToClauses[variable]| > 0 ==> negativeLiteralsToClauses[variable][|negativeLiteralsToClauses[variable]| - 1] < clauseIndex
        invariant Utils.orderedAsc(negativeLiteralsToClauses[variable])
        invariant forall cI: Int32.t :: cI in negativeLiteralsToClauses[variable] ==> -variable - 1 in clauses[cI]
        invariant forall cI: Int32.t :: 0 <= cI < clauseIndex ==> cI !in negativeLiteralsToClauses[variable] ==> -variable - 1 !in clauses[cI]
        decreases |clauses| - clauseIndex as int
      {
        if -variable - 1 in clauses[clauseIndex] {
          negativeLiteralsToClauses[variable] := negativeLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }

  method revertLastDecisionLevel()
    requires valid()
    requires 0 <= decisionLevel
    modifies `assignmentsTrace, `decisionLevel, truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd
    ensures decisionLevel == old(decisionLevel) - 1
    ensures assignmentsTrace == old(assignmentsTrace) - old(getDecisionLevel(decisionLevel))
    ensures valid()
    ensures forall i: Int32.t :: 0 <= i <= decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
  {
    ghost var k: Int32.t := traceDLEnd[decisionLevel] - 1;
    while traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
      invariant traceDLStart[decisionLevel] - 1 <= k < traceDLEnd[decisionLevel]
      invariant k == traceDLEnd[decisionLevel] - 1
      invariant valid()
      invariant forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
      decreases traceDLEnd[decisionLevel] as int - traceDLStart[decisionLevel] as int
      modifies `assignmentsTrace, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount
    {
      removeLastVariable();
      k := k - 1;
    }
    decisionLevel := decisionLevel - 1;
    assert old(traceVariable[..]) == traceVariable[..];
  }

  method removeLastVariable()
    requires valid()
    requires 0 <= decisionLevel < variablesCount
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    modifies `assignmentsTrace, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount
    ensures traceDLEnd[decisionLevel] == old(traceDLEnd[decisionLevel]) - 1
    ensures valid()
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
  {
    forall_validAssignmentTrace_traceDLEndStrictlyOrdered();
    var k: Int32.t := traceDLEnd[decisionLevel] - 1;
    var variable := traceVariable[k];
    var value := traceValue[k];
    assignmentsTrace := assignmentsTrace - {(variable, value)};
    traceDLEnd[decisionLevel] := k;
    ghost var previousTau := truthAssignment[..];
    truthAssignment[variable] := -1;
    ghost var newTau := truthAssignment[..];
    assert forall i: Int32.t :: 0 <= i < decisionLevel ==> traceDLEnd[i] == old(traceDLEnd[i]) && traceDLStart[i] == old(traceDLStart[i]);
    assert traceVariable[..traceDLEnd[decisionLevel]] == old(traceVariable[..traceDLEnd[decisionLevel] - 1]);
    assert forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i);
    var positivelyImpactedClauses: seq<Int32.t> := positiveLiteralsToClauses[variable];
    var negativelyImpactedClauses: seq<Int32.t> := negativeLiteralsToClauses[variable];
    if !value {
      negativelyImpactedClauses := positiveLiteralsToClauses[variable];
      positivelyImpactedClauses := negativeLiteralsToClauses[variable];
    }
    assert Utils.valuesBoundedBy(positivelyImpactedClauses, 0, |clauses|);
    assert Utils.valuesBoundedBy(negativelyImpactedClauses, 0, |clauses|);
    undoImpactedClauses_TFSArraysModified(previousTau, newTau, variable, positivelyImpactedClauses, negativelyImpactedClauses);
    var i: Int32.t := 0;
    var len := |positivelyImpactedClauses| as Int32.t;
    while i < len
      invariant len as int == |positivelyImpactedClauses|
      invariant 0 <= i <= len
      invariant forall i': Int32.t :: 0 <= i' < clausesCount && i' !in positivelyImpactedClauses ==> trueLiteralsCount[i'] == countTrueLiterals(newTau, clauses[i'])
      invariant forall i': Int32.t :: 0 <= i' < i ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']])
      invariant forall i': Int32.t :: i <= i' < len ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']])
      decreases len as int - i as int
      modifies trueLiteralsCount
    {
      var clauseIndex := positivelyImpactedClauses[i];
      ghost var clause := clauses[clauseIndex];
      assert validClause(clause);
      unsetVariable_countTrueLiteralsDecreasesWithOne(previousTau, newTau, variable, clause);
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;
      i := i + 1;
    }
    assert trueLiteralsCount.Length == |clauses|;
    forall i: Int32.t | 0 <= i as int < |clauses|
      ensures trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i])
    {
      if i !in positivelyImpactedClauses {
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      } else {
        ghost var j: Int32.t :| 0 <= j as int < |positivelyImpactedClauses| && positivelyImpactedClauses[j] == i;
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    i := 0;
    len := |negativelyImpactedClauses| as Int32.t;
    modify falseLiteralsCount {
      while i < len
        invariant 0 <= i <= len
        invariant forall i': Int32.t :: 0 <= i' < i ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(newTau, clauses[negativelyImpactedClauses[i']])
        invariant forall i': Int32.t :: i <= i' < len ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(previousTau, clauses[negativelyImpactedClauses[i']])
        invariant forall i': Int32.t :: 0 <= i' < clausesCount && i' !in negativelyImpactedClauses ==> falseLiteralsCount[i'] == countFalseLiterals(newTau, clauses[i'])
        invariant forall i': Int32.t :: 0 <= i' < clausesCount && i' !in positivelyImpactedClauses ==> trueLiteralsCount[i'] == countTrueLiterals(newTau, clauses[i'])
        invariant forall i': int :: 0 <= i' < |positivelyImpactedClauses| ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']])
        invariant validTrueLiteralsCount(truthAssignment[..])
        decreases len - i
        modifies falseLiteralsCount
      {
        var clauseIndex := negativelyImpactedClauses[i];
        unsetVariable_countFalseLiteralsDecreasesWithOne(previousTau, newTau, variable, clauses[clauseIndex]);
        falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
        i := i + 1;
      }
    }
    assert falseLiteralsCount.Length == |clauses|;
    forall i: Int32.t | 0 <= i as int < |clauses|
      ensures falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i])
    {
      if i !in negativelyImpactedClauses {
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      } else {
        ghost var j: Int32.t :| 0 <= j as int < |negativelyImpactedClauses| && negativelyImpactedClauses[j] == i;
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert old(traceVariable[..]) == traceVariable[..];
  }

  method setVariable(variable: Int32.t, value: bool)
    requires valid()
    requires validVariable(variable)
    requires truthAssignment[variable] == -1
    requires 0 <= decisionLevel
    modifies truthAssignment, traceVariable, traceValue, traceDLEnd, `assignmentsTrace, trueLiteralsCount, falseLiteralsCount
    ensures valid()
    ensures value == false ==> old(truthAssignment[..])[variable as int := 0] == truthAssignment[..]
    ensures value == true ==> old(truthAssignment[..])[variable as int := 1] == truthAssignment[..]
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures traceVariable[traceDLEnd[decisionLevel] - 1] == variable
    ensures traceValue[traceDLEnd[decisionLevel] - 1] == value
    ensures forall i: Int32.t :: 0 <= i < variablesCount && i != decisionLevel ==> traceDLEnd[i] == old(traceDLEnd[i])
    ensures forall i: Int32.t :: 0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==> traceVariable[i] == old(traceVariable[i]) && traceValue[i] == old(traceValue[i])
    ensures forall x: Int32.t :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures assignmentsTrace == old(assignmentsTrace) + {(variable, value)}
    ensures countUnsetVariables(truthAssignment[..]) + 1 == old(countUnsetVariables(truthAssignment[..]))
    decreases variable, value
  {
    ghost var oldTau: seq<Int32.t> := truthAssignment[..];
    existsUnsetLiteral_traceNotFull(variable);
    addAssignment(variable, value);
    if value {
      truthAssignment[variable] := 1;
    } else {
      truthAssignment[variable] := 0;
    }
    assert validTruthAssignment();
    ghost var newTau := truthAssignment[..];
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if !value {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    var i: Int32.t := 0;
    var impactedClauses := positiveLiteralsToClauses[variable];
    var impactedClauses' := negativeLiteralsToClauses[variable];
    if !value {
      impactedClauses := negativeLiteralsToClauses[variable];
      impactedClauses' := positiveLiteralsToClauses[variable];
    }
    clausesNotImpacted_TFArraysSame(oldTau, newTau, variable, impactedClauses, impactedClauses');
    var impactedClausesLen: Int32.t := |impactedClauses| as Int32.t;
    while i < impactedClausesLen
      invariant 0 <= i <= impactedClausesLen
      invariant forall j: Int32.t :: 0 <= j < clausesCount && j !in impactedClauses ==> trueLiteralsCount[j] == countTrueLiterals(newTau, clauses[j])
      invariant forall j: Int32.t :: 0 <= j < i ==> trueLiteralsCount[impactedClauses[j]] == countTrueLiterals(newTau, clauses[impactedClauses[j]])
      invariant forall j: Int32.t :: i <= j < impactedClausesLen ==> trueLiteralsCount[impactedClauses[j]] == countTrueLiterals(oldTau, clauses[impactedClauses[j]])
      decreases impactedClausesLen - i
      modifies trueLiteralsCount
    {
      var clauseIndex := impactedClauses[i];
      unsetVariable_countTrueLiteralsLessThanLength(oldTau, variable, clauses[clauseIndex]);
      setVariable_countTrueLiteralsIncreasesWithOne(oldTau, newTau, variable, clauses[clauseIndex]);
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] + 1;
      assert trueLiteral in clauses[clauseIndex] && getLiteralValue(newTau, trueLiteral) == 1;
      assert isClauseSatisfied(newTau, clauseIndex);
      i := i + 1;
    }
    assert trueLiteralsCount.Length == |clauses|;
    forall i: Int32.t | 0 <= i as int < |clauses|
      ensures trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i])
    {
      if i !in impactedClauses {
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      } else {
        ghost var j: Int32.t :| 0 <= j as int < |impactedClauses| && impactedClauses[j] == i;
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert validTrueLiteralsCount(truthAssignment[..]);
    var i': Int32.t := 0;
    var impactedClausesLen': Int32.t := |impactedClauses'| as Int32.t;
    while i' < impactedClausesLen'
      invariant 0 <= i' <= impactedClausesLen'
      invariant forall j: Int32.t :: 0 <= j < clausesCount && j !in impactedClauses' ==> falseLiteralsCount[j] == countFalseLiterals(newTau, clauses[j])
      invariant forall j: Int32.t :: 0 <= j < i' ==> falseLiteralsCount[impactedClauses'[j]] == countFalseLiterals(newTau, clauses[impactedClauses'[j]])
      invariant forall j: Int32.t :: i' <= j < impactedClausesLen' ==> falseLiteralsCount[impactedClauses'[j]] == countFalseLiterals(oldTau, clauses[impactedClauses'[j]])
      decreases impactedClausesLen' - i'
      modifies falseLiteralsCount
    {
      var clauseIndex := impactedClauses'[i'];
      unsetVariable_countFalseLiteralsLessThanLength(oldTau, variable, clauses[clauseIndex]);
      setVariable_countFalseLiteralsIncreasesWithOne(oldTau, newTau, variable, clauses[clauseIndex]);
      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] + 1;
      i' := i' + 1;
    }
    assert falseLiteralsCount.Length == |clauses|;
    forall i: Int32.t | 0 <= i as int < |clauses|
      ensures falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i])
    {
      if i !in impactedClauses {
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      } else {
        ghost var j: Int32.t :| 0 <= j as int < |impactedClauses| && impactedClauses[j] == i;
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert validFalseLiteralsCount(truthAssignment[..]);
    variableSet_countUnsetVariablesLessThanLength(newTau, variable);
    setVariable_unsetVariablesDecreasesWithOne(oldTau, newTau, variable);
  }

  lemma /*{:_induction this}*/ traceFull_variableInTrace(variable: Int32.t)
    requires valid()
    requires validVariable(variable)
    requires 0 <= decisionLevel
    requires traceDLEnd[decisionLevel] == variablesCount
    ensures exists i: Int32.t :: 0 <= i < traceDLEnd[decisionLevel] && traceVariable[i] == variable
    decreases variable
  {
  }

  lemma /*{:_induction this}*/ existsUnsetLiteral_traceNotFull(variable: Int32.t)
    requires valid()
    requires validVariable(variable)
    requires truthAssignment[variable] == -1
    requires 0 <= decisionLevel
    ensures traceDLEnd[decisionLevel] < variablesCount
    ensures forall x: (Int32.t, bool) :: x in assignmentsTrace ==> x.0 != variable
    decreases variable
  {
  }

  method addAssignment(variable: Int32.t, value: bool)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= decisionLevel
    requires 0 <= variable < variablesCount
    requires forall x: (Int32.t, bool) :: x in assignmentsTrace ==> x.0 != variable
    requires traceDLEnd[decisionLevel] < variablesCount
    modifies `assignmentsTrace, traceDLEnd, traceVariable, traceValue
    ensures traceDLEnd[decisionLevel] == old(traceDLEnd[decisionLevel]) + 1
    ensures traceVariable[traceDLEnd[decisionLevel] - 1] == variable
    ensures traceValue[traceDLEnd[decisionLevel] - 1] == value
    ensures forall i: Int32.t :: 0 <= i < variablesCount && i != decisionLevel ==> traceDLEnd[i] == old(traceDLEnd[i])
    ensures forall i: Int32.t :: 0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==> traceVariable[i] == old(traceVariable[i]) && traceValue[i] == old(traceValue[i])
    ensures assignmentsTrace == old(assignmentsTrace) + {(variable, value)}
    ensures validAssignmentTrace()
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    decreases variable, value
  {
    traceVariable[traceDLEnd[decisionLevel]] := variable;
    traceValue[traceDLEnd[decisionLevel]] := value;
    assignmentsTrace := assignmentsTrace + {(variable, value)};
    traceDLEnd[decisionLevel] := traceDLEnd[decisionLevel] + 1;
    forall_validAssignmentTrace_traceDLEndStrictlyOrdered();
  }

  lemma /*{:_induction this}*/ forall_validAssignmentTrace_traceDLStartStrictlyOrdered()
    requires 0 <= decisionLevel
    requires decisionLevel as int < traceDLStart.Length
    requires decisionLevel as int < traceDLEnd.Length
    ensures validVariablesCount() && validAssignmentTrace() ==> forall i: Int32.t, j: Int32.t :: 0 <= i < j <= decisionLevel ==> traceDLStart[i] < traceDLStart[j]
  {
  }

  lemma /*{:_induction this}*/ validAssignmentTrace_traceDLStartStrictlyOrdered(i: Int32.t, j: Int32.t)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= i < j <= decisionLevel
    ensures traceDLStart[i] < traceDLStart[j]
    decreases decisionLevel - i
  {
  }

  lemma /*{:_induction this}*/ forall_validAssignmentTrace_traceDLEndStrictlyOrdered()
    requires 0 <= decisionLevel
    requires decisionLevel as int < traceDLStart.Length
    requires decisionLevel as int < traceDLEnd.Length
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures validVariablesCount() && validAssignmentTrace() ==> forall i: Int32.t :: 0 <= i < decisionLevel ==> traceDLEnd[i] < traceDLEnd[decisionLevel]
  {
  }

  lemma /*{:_induction this}*/ validAssignmentTrace_traceDLEndStrictlyOrdered(i: Int32.t)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= i < decisionLevel
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures traceDLEnd[i] < traceDLEnd[decisionLevel]
    decreases decisionLevel - i
  {
  }

  method increaseDecisionLevel()
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires decisionLevel < variablesCount - 1
    requires decisionLevel >= 0 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    modifies `decisionLevel, traceDLStart, traceDLEnd
    ensures decisionLevel == old(decisionLevel) + 1
    ensures validAssignmentTrace()
    ensures traceDLStart[decisionLevel] == traceDLEnd[decisionLevel]
    ensures getDecisionLevel(decisionLevel) == {}
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
  {
    decisionLevel := decisionLevel + 1;
    var previous: Int32.t := 0;
    if decisionLevel == 0 {
      previous := 0;
    } else {
      previous := traceDLEnd[decisionLevel - 1];
    }
    traceDLStart[decisionLevel] := previous;
    traceDLEnd[decisionLevel] := previous;
    assert old(traceVariable[..]) == traceVariable[..];
  }

  function getDecisionLevel(dL: Int32.t): set<(Int32.t, bool)>
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires -1 <= dL <= decisionLevel
    requires traceVariable.Length == variablesCount as int
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue, `assignmentsTrace
    ensures getDecisionLevel(dL) <= assignmentsTrace
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue, this}, dL
  {
    if dL == -1 then
      {}
    else
      set j: (Int32.t, bool) {:trigger j.0} {:trigger j in assignmentsTrace} | j in assignmentsTrace && j.0 in traceVariable[traceDLStart[dL] .. traceDLEnd[dL]]
  }

  method extractUnsetLiteralFromClause(clauseIndex: Int32.t) returns (literal: Int32.t)
    requires valid()
    requires 0 <= clauseIndex < clausesCount
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    requires trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex]
    ensures validLiteral(literal)
    ensures literal in clauses[clauseIndex]
    ensures truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases clauseIndex
  {
    unitClause_existsUnsetLiteral(clauseIndex);
    var i: Int32.t := 0;
    var clause := clauses[clauseIndex];
    while i < clauseLength[clauseIndex]
      invariant 0 <= i < clauseLength[clauseIndex]
      invariant exists literal: Int32.t :: literal in clause[i..] && truthAssignment[getVariableFromLiteral(literal)] == -1
      decreases clauseLength[clauseIndex] - i
    {
      if truthAssignment[getVariableFromLiteral(clause[i])] == -1 {
        return clause[i];
      }
      i := i + 1;
    }
    assert false;
  }

  method propagate(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= decisionLevel
    requires 0 <= clauseIndex < clausesCount
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    requires trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex]
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    ensures valid()
    ensures forall x: Int32.t :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
    ensures countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]))
    ensures old(assignmentsTrace) <= assignmentsTrace
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures ghost var tau: seq<Int32.t> := old(truthAssignment[..]); isSatisfiableExtend(tau) <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..]), 1
  {
    ghost var tau'' := truthAssignment[..];
    var literal := extractUnsetLiteralFromClause(clauseIndex);
    var clause := clauses[clauseIndex];
    ghost var (v', val') := convertLVtoVI(literal, true);
    unitClauseLiteralFalse_tauNotSatisfiable(tau'', clauseIndex, literal);
    setLiteral(literal, true);
    assert isSatisfiableExtend(tau''[v' as int := val']) <==> isSatisfiableExtend(truthAssignment[..]);
    if isSatisfiableExtend(truthAssignment[..]) {
      extensionSatisfiable_baseSatisfiable(tau'', v', val');
    } else {
      forVariableNotSatisfiableExtend_notSatisfiableExtend(tau'', v');
    }
    assert !isSatisfiableExtend(tau'') <==> !isSatisfiableExtend(truthAssignment[..]);
    assert countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]));
  }

  method unitPropagation(variable: Int32.t, value: bool)
    requires valid()
    requires validVariable(variable)
    requires 0 <= decisionLevel
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    ensures valid()
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures old(assignmentsTrace) <= assignmentsTrace
    ensures assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
    ensures forall x: Int32.t :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures countUnsetVariables(truthAssignment[..]) <= old(countUnsetVariables(truthAssignment[..]))
    ensures ghost var tau: seq<Int32.t> := old(truthAssignment[..]); isSatisfiableExtend(tau) <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..]), 2
  {
    var negativelyImpactedClauses := negativeLiteralsToClauses[variable];
    if !value {
      negativelyImpactedClauses := positiveLiteralsToClauses[variable];
    }
    var k: Int32.t := 0;
    var negativelyImpactedClausesLen: Int32.t := |negativelyImpactedClauses| as Int32.t;
    while k < negativelyImpactedClausesLen
      invariant 0 <= k <= negativelyImpactedClausesLen
      invariant valid()
      invariant decisionLevel == old(decisionLevel)
      invariant traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
      invariant assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
      invariant countUnsetVariables(truthAssignment[..]) <= old(countUnsetVariables(truthAssignment[..]))
      invariant isSatisfiableExtend(old(truthAssignment[..])) <==> isSatisfiableExtend(truthAssignment[..])
      invariant forall x: Int32.t :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
      invariant forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
      decreases |negativelyImpactedClauses| - k as int
    {
      var clauseIndex := negativelyImpactedClauses[k];
      if falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex] {
        if trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex] {
          propagate(clauseIndex);
        }
      }
      k := k + 1;
    }
  }

  method setLiteral(literal: Int32.t, value: bool)
    requires valid()
    requires validLiteral(literal)
    requires getLiteralValue(truthAssignment[..], literal) == -1
    requires 0 <= decisionLevel
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    ensures valid()
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures forall x: Int32.t :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
    ensures forall i: Int32.t :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]))
    ensures var (variable: Int32.t, val: Int32.t) := convertLVtoVI(literal, value); isSatisfiableExtend(old(truthAssignment[..])[variable as int := val]) <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..]), 0
  {
    ghost var (vari, val) := convertLVtoVI(literal, value);
    ghost var tau' := truthAssignment[..][vari as int := val];
    var variable := getVariableFromLiteral(literal);
    var value' := if literal > 0 then value else !value;
    setVariable(variable, value');
    unitPropagation(variable, value');
  }

  method chooseLiteral() returns (x: Int32.t)
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    ensures valid()
    ensures validLiteral(x)
    ensures truthAssignment[getVariableFromLiteral(x)] == -1
    ensures getLiteralValue(truthAssignment[..], x) == -1
  {
    notEmptyNoEmptyClauses_existUnsetLiteralInClauses();
    var minim: Int32.t := Int32.max;
    var counter: Int32.t := 0;
    var result: Int32.t := -1;
    var ok := false;
    var cI: Int32.t := 0;
    while cI < clausesCount
      invariant 0 <= cI <= clausesCount
      invariant !ok ==> counter == 0 && minim == Int32.max && exists i': Int32.t, k': int :: cI <= i' < clausesCount && 0 <= k' < |clauses[i']| && trueLiteralsCount[i'] == 0 && validLiteral(clauses[i'][k']) && truthAssignment[getVariableFromLiteral(clauses[i'][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[i'][k']) == -1
      invariant (exists i': Int32.t, k': int :: 0 <= i' < cI && 0 <= k' < |clauses[i']| && trueLiteralsCount[i'] == 0 && validLiteral(clauses[i'][k']) && truthAssignment[getVariableFromLiteral(clauses[i'][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[i'][k']) == -1) ==> ok
      invariant ok ==> validLiteral(result) && truthAssignment[getVariableFromLiteral(result)] == -1 && getLiteralValue(truthAssignment[..], result) == -1
      invariant 0 <= counter as int <= countLiterals(cI)
      decreases clausesCount as int - cI as int
    {
      var diff := clauseLength[cI] - falseLiteralsCount[cI];
      if trueLiteralsCount[cI] == 0 && diff < minim {
        minim := diff;
      }
      if trueLiteralsCount[cI] == 0 && diff == minim {
        assert validClause(clauses[cI]);
        var lI: Int32.t := 0;
        while lI < clauseLength[cI]
          invariant 0 <= lI <= clauseLength[cI]
          invariant !ok ==> counter == 0 && exists k': int :: lI as int <= k' < |clauses[cI]| && trueLiteralsCount[cI] == 0 && validLiteral(clauses[cI][k']) && truthAssignment[getVariableFromLiteral(clauses[cI][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[cI][k']) == -1
          invariant (exists k': Int32.t :: 0 <= k' < lI && trueLiteralsCount[cI] == 0 && validLiteral(clauses[cI][k']) && truthAssignment[getVariableFromLiteral(clauses[cI][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[cI][k']) == -1) ==> ok
          invariant ok ==> validLiteral(result) && truthAssignment[getVariableFromLiteral(result)] == -1 && getLiteralValue(truthAssignment[..], result) == -1
          invariant 0 <= counter as int <= countLiterals(cI) + lI as int
          decreases clauseLength[cI] as int - lI as int
        {
          countLiterals_monotone(cI);
          assert validLiteral(clauses[cI][lI]);
          var variable := getVariableFromLiteral(clauses[cI][lI]);
          if truthAssignment[variable] == -1 {
            ok := true;
            if counter == 0 {
              result := variable + 1;
              counter := counter + 1;
            } else if result == variable + 1 {
              counter := counter + 1;
            } else {
              counter := counter - 1;
            }
          }
          lI := lI + 1;
        }
      }
      cI := cI + 1;
    }
    return -result;
  }

  lemma /*{:_induction this}*/ maybeClause_existUnsetLiteralInClause(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= clauseIndex < clausesCount
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    ensures exists j': Int32.t :: 0 <= j' < clauseLength[clauseIndex] && validLiteral(clauses[clauseIndex][j']) && truthAssignment[getVariableFromLiteral(clauses[clauseIndex][j'])] == -1
    decreases clauseIndex
  {
  }

  lemma /*{:_induction this}*/ notEmptyNoEmptyClauses_existUnsetLiteralInClauses()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    ensures forall i: int :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0 && falseLiteralsCount[i] < clauseLength[i] ==> exists j': Int32.t :: 0 <= j' < clauseLength[i] && validLiteral(clauses[i][j']) && truthAssignment[getVariableFromLiteral(clauses[i][j'])] == -1
  {
  }

  function hasEmptyClause(): bool
    requires valid()
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    ensures hasEmptyClause() == true ==> exists i: int :: 0 <= i < |clauses| && falseLiteralsCount[i] as int == |clauses[i]|
    ensures hasEmptyClause() == false ==> forall i: int :: 0 <= i < |clauses| ==> falseLiteralsCount[i] as int < |clauses[i]|
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    if exists i: Int32.t :: 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i] then
      ghost var i: Int32.t :| 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i];
      true
    else
      false
  }

  method getHasEmptyClause() returns (ok: bool)
    requires valid()
    ensures ok <==> hasEmptyClause()
    ensures ok ==> exists i: Int32.t :: 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i]
    ensures !ok ==> forall i: Int32.t :: 0 <= i < clausesCount ==> falseLiteralsCount[i] < clauseLength[i]
  {
    var k: Int32.t := 0;
    while k < clausesCount
      invariant 0 <= k <= clausesCount
      invariant forall k': Int32.t :: 0 <= k' < k ==> falseLiteralsCount[k'] < clauseLength[k']
      decreases clausesCount as int - k as int
    {
      if falseLiteralsCount[k] == clauseLength[k] {
        return true;
      }
      k := k + 1;
    }
    return false;
  }

  function isEmpty(): bool
    requires valid()
    requires !hasEmptyClause()
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    ensures isEmpty() == true ==> forall i: int :: 0 <= i < |clauses| ==> trueLiteralsCount[i] > 0
    ensures isEmpty() == false ==> exists i: int :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    if exists i: Int32.t :: 0 <= i < clausesCount && trueLiteralsCount[i] == 0 then
      ghost var i: Int32.t :| 0 <= i < clausesCount && trueLiteralsCount[i] == 0;
      false
    else
      true
  }

  method getIsEmpty() returns (ok: bool)
    requires valid()
    requires !hasEmptyClause()
    ensures ok <==> isEmpty()
    ensures ok ==> forall i: Int32.t :: 0 <= i < clausesCount ==> trueLiteralsCount[i] > 0
    ensures !ok ==> exists i: Int32.t :: 0 <= i < clausesCount && trueLiteralsCount[i] == 0
  {
    var k: Int32.t := 0;
    while k < clausesCount
      invariant 0 <= k <= clausesCount
      invariant forall k': Int32.t :: 0 <= k' < k ==> trueLiteralsCount[k'] > 0
      decreases clausesCount as int - k as int
    {
      if trueLiteralsCount[k] == 0 {
        return false;
      }
      k := k + 1;
    }
    return true;
  }

  method level0UnitPropagation()
    requires valid()
    requires decisionLevel == -1
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLStart, traceDLEnd, traceValue, traceVariable, `assignmentsTrace, `decisionLevel
    ensures valid()
    ensures decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures isSatisfiableExtend(old(truthAssignment[..])) <==> isSatisfiableExtend(truthAssignment[..])
  {
    var i := 0;
    increaseDecisionLevel();
    while i < clausesCount
      invariant 0 <= i <= clausesCount
      invariant valid()
      invariant isSatisfiableExtend(old(truthAssignment[..])) <==> isSatisfiableExtend(truthAssignment[..])
      decreases clausesCount as int - i as int
      modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLStart, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    {
      if trueLiteralsCount[i] == 0 && falseLiteralsCount[i] + 1 == clauseLength[i] {
        propagate(i);
      }
      i := i + 1;
    }
    if traceDLStart[decisionLevel] == traceDLEnd[decisionLevel] {
      revertLastDecisionLevel();
    }
  }

  lemma /*{:_induction this}*/ notEmptyNoEmptyClauses_traceNotFull()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    requires decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures decisionLevel < variablesCount - 1
  {
  }

  predicate occursInTrace(variable: Int32.t)
    requires valid()
    requires validVariable(variable)
    requires decisionLevel > -1
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}, variable
  {
    exists j: Int32.t :: 
      0 <= j < traceDLEnd[decisionLevel] &&
      traceVariable[j] == variable
  }

  predicate occursInAssignmentsTrace(variable: Int32.t)
    requires valid()
    requires validVariable(variable)
    requires decisionLevel > -1
    requires decisionLevel == variablesCount - 1
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}, variable
  {
    exists x: (Int32.t, bool) :: 
      x in assignmentsTrace &&
      x.0 == variable
  }

  lemma /*{:_induction this}*/ ifFull_containsAllVariables()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    requires decisionLevel == variablesCount - 1
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures forall v: Int32.t :: 0 <= v < variablesCount ==> occursInTrace(v)
    ensures forall v: Int32.t :: 0 <= v < variablesCount ==> occursInAssignmentsTrace(v)
  {
  }

  lemma /*{:_induction this}*/ allVariablesSet_done()
    requires valid()
    requires forall v: Int32.t :: validVariable(v) ==> isVariableSet(truthAssignment[..], v)
    ensures hasEmptyClause() || isEmpty()
  {
  }

  lemma /*{:_induction this}*/ tauFullClauseNotEmpty_clauseIsSatisfied(cI: int)
    requires valid()
    requires 0 <= cI < |clauses|
    requires validClause(clauses[cI])
    requires forall x: Int32.t :: x in clauses[cI] ==> isVariableSet(truthAssignment[..], getVariableFromLiteral(x))
    requires falseLiteralsCount[cI] as int < |clauses[cI]|
    ensures trueLiteralsCount[cI] > 0
    decreases cI
  {
  }

  lemma /*{:_induction this, clause, truthAssignment}*/ existsTrueLiteral_countTrueLiteralsPositive(clause: seq<Int32.t>, truthAssignment: seq<Int32.t>)
    requires valid()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires exists x: Int32.t :: x in clause && getLiteralValue(truthAssignment, x) == 1
    ensures countTrueLiterals(truthAssignment, clause) > 0
    decreases clause, truthAssignment
  {
  }

  lemma /*{:_induction this}*/ unitClause_existsUnsetLiteral(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    ensures exists literal: Int32.t :: literal in clauses[clauseIndex] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases clauseIndex
  {
  }

  lemma /*{:_induction this}*/ hasEmptyClause_notSatisfiable()
    requires valid()
    requires hasEmptyClause()
    ensures !isSatisfiableExtend(truthAssignment[..])
  {
  }

  lemma /*{:_induction this}*/ allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= clauseIndex as int < |clauses|
    requires falseLiteralsCount[clauseIndex] as int == |clauses[clauseIndex]|
    requires validClause(clauses[clauseIndex])
    ensures forall literal: Int32.t :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment[..], literal) == 0
    decreases clauseIndex
  {
  }

  lemma /*{:_induction this}*/ isEmpty_sastisfied()
    requires valid()
    requires !hasEmptyClause()
    requires isEmpty()
    ensures isSatisfiableExtend(truthAssignment[..])
  {
  }

  lemma /*{:_induction this}*/ partialTauSatisfied_isSatisfiableExtend(tau: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClauses()
    requires isSatisfied(tau)
    ensures isSatisfiableExtend(tau)
    decreases countUnsetVariables(tau)
  {
  }

  lemma /*{:_induction this}*/ unitClause_allFalseExceptLiteral(truthAssignment: seq<Int32.t>, clauseIndex: Int32.t, literal: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires validTrueLiteralsCount(truthAssignment)
    requires validFalseLiteralsCount(truthAssignment)
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires validLiteral(literal)
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    requires literal in clauses[clauseIndex]
    requires getLiteralValue(truthAssignment, literal) == -1
    requires forall literal: Int32.t :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment, literal) != 1
    ensures forall literal': Int32.t :: literal' in clauses[clauseIndex] && literal' != literal ==> getLiteralValue(truthAssignment, literal') != -1
    decreases truthAssignment, clauseIndex, literal
  {
  }

  lemma /*{:_induction this}*/ unitClauseLiteralFalse_tauNotSatisfiable(truthAssignment: seq<Int32.t>, clauseIndex: Int32.t, literal: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires validTrueLiteralsCount(truthAssignment)
    requires validFalseLiteralsCount(truthAssignment)
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires validLiteral(literal)
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    requires truthAssignment[getVariableFromLiteral(literal)] == -1
    requires literal in clauses[clauseIndex]
    ensures var (variable: Int32.t, value: Int32.t) := convertLVtoVI(literal, false); !isSatisfiableExtend(truthAssignment[variable as int := value])
    decreases truthAssignment, clauseIndex, literal
  {
  }

  lemma /*{:_induction this, tau}*/ variableSet_countUnsetVariablesLessThanLength(tau: seq<Int32.t>, variable: Int32.t)
    requires |tau| <= Int32.max as int
    requires 0 <= variable as int < |tau|
    requires tau[variable] in [0, 1]
    ensures countUnsetVariables(tau) as int < |tau|
    decreases tau, variable
  {
  }

  lemma /*{:_induction this, tau, clause}*/ unsetVariable_countTrueLiteralsLessThanLength(tau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClause(clause)
    requires validVariable(variable)
    requires tau[variable] == -1
    requires variable + 1 in clause || -variable - 1 in clause
    ensures countTrueLiterals(tau, clause) as int < |clause|
    decreases tau, variable, clause
  {
  }

  lemma /*{:_induction this, tau, clause}*/ unsetVariable_countFalseLiteralsLessThanLength(tau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClause(clause)
    requires validVariable(variable)
    requires tau[variable] == -1
    requires variable + 1 in clause || -variable - 1 in clause
    ensures countFalseLiterals(tau, clause) as int < |clause|
    decreases tau, variable, clause
  {
  }

  lemma /*{:_induction this}*/ forVariableNotSatisfiableExtend_notSatisfiableExtend(tau: seq<Int32.t>, variable: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires validVariable(variable)
    requires !isSatisfiableExtend(tau[variable as int := 0])
    requires !isSatisfiableExtend(tau[variable as int := 1])
    ensures !isSatisfiableExtend(tau)
    decreases tau, variable
  {
  }

  lemma /*{:_induction this}*/ extensionSatisfiable_baseSatisfiable(tau: seq<Int32.t>, variable: Int32.t, value: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires validVariable(variable)
    requires value in [0, 1]
    requires tau[variable] == -1
    requires isSatisfiableExtend(tau[variable as int := value])
    ensures isSatisfiableExtend(tau)
    decreases tau, variable, value
  {
  }
}

module Useless {

  import opened MyDatatypes

  import Int32

  import InputPredicate
  class Parser {
    var content: array<char>
    var contentLength: Int32.t
    var cursor: Int32.t

    constructor (c: array<char>)
      requires valid'(c)
      ensures valid()
      decreases c
    {
      content := c;
      contentLength := c.Length as Int32.t;
      cursor := 0;
    }

    predicate valid()
      reads `content, content, `contentLength, `cursor
      decreases {this, content, this, this}
    {
      valid'(content) &&
      contentLength as int == content.Length &&
      0 <= cursor <= contentLength
    }

    method skipLine()
      requires valid()
      modifies `cursor
      ensures valid()
      ensures old(cursor) <= cursor
    {
      while cursor < contentLength && content[cursor] != '\n'
        invariant 0 <= cursor <= contentLength
        decreases contentLength as int - cursor as int, if cursor < contentLength then if content[cursor] <= '\n' then '\n' as int - content[cursor] as int else content[cursor] as int - '\n' as int else 0 - 1
      {
        cursor := cursor + 1;
      }
      if cursor < contentLength {
        cursor := cursor + 1;
      }
    }

    method toNextNumber()
      requires valid()
      modifies `cursor
      ensures valid()
      ensures old(cursor) <= cursor
      ensures cursor < contentLength ==> content[cursor] == '-' || '0' <= content[cursor] <= '9'
    {
      while cursor < contentLength && !('0' <= content[cursor] <= '9' || content[cursor] == '-')
        invariant 0 <= cursor <= contentLength
        decreases contentLength as int - cursor as int, if cursor < contentLength && !('0' <= content[cursor] <= '9') then if content[cursor] <= '-' then '-' as int - content[cursor] as int else content[cursor] as int - '-' as int else 0 - 1
      {
        cursor := cursor + 1;
      }
    }

    method extractNumber() returns (res: Maybe<Int32.t>)
      requires valid()
      requires cursor < contentLength ==> content[cursor] == '-' || '0' <= content[cursor] <= '9'
      modifies `cursor
      ensures valid()
      ensures old(cursor) <= cursor
      ensures res.Just? ==> old(cursor) < cursor
    {
      var number := 0;
      var isNegative: bool := false;
      if cursor < contentLength && content[cursor] == '-' {
        isNegative := true;
        cursor := cursor + 1;
      }
      if cursor == contentLength {
        return Error(""There is no number around here."");
      }
      while cursor < contentLength && '0' <= content[cursor] <= '9'
        invariant 0 <= cursor <= contentLength
        invariant 0 <= number <= Int32.max
        decreases contentLength as int - cursor as int
      {
        var digit: Int32.t := content[cursor] as Int32.t - '0' as Int32.t;
        if number <= (Int32.max - digit) / 10 {
          assert 0 <= (Int32.max - digit) / 10 - number;
          number := number * 10 + digit;
        } else {
          return Error(""There is a number bigger than Int32.max"");
        }
        cursor := cursor + 1;
      }
      if isNegative {
        number := -number;
      }
      return Just(number);
    }

    method parse() returns (result: Maybe<(Int32.t, seq<seq<Int32.t>>)>)
      requires valid()
      modifies `cursor
      ensures result.Just? ==> InputPredicate.valid(result.value)
    {
      var variablesCount: Int32.t := 0;
      var clausesCount: Int32.t := 0;
      var clauses: seq<seq<Int32.t>> := [];
      var clause: array<Int32.t> := new Int32.t[1000];
      var clauseLength: Int32.t := 0;
      var ok := false;
      var literalsCount: Int32.t := 0;
      var contentLength: Int32.t := content.Length as Int32.t;
      while cursor < contentLength
        invariant 0 <= cursor <= contentLength
        invariant InputPredicate.checkClauses(variablesCount, clauses)
        invariant InputPredicate.sortedClauses(clauses)
        invariant clause.Length <= Int32.max as int
        invariant forall z: Int32.t :: 0 <= z < clauseLength ==> (clause[z] < 0 && 0 < -clause[z] <= variablesCount) || (clause[z] > 0 && 0 < clause[z] <= variablesCount)
        invariant forall x: Int32.t, y: Int32.t :: 0 <= x < y < clauseLength ==> clause[x] < clause[y]
        invariant ok ==> 0 < variablesCount < Int32.max
        invariant InputPredicate.countLiterals(clauses) == literalsCount as int
        decreases contentLength - cursor
        modifies `cursor, clause
      {
        var oldCursor := cursor;
        if content[cursor] == 'c' {
          skipLine();
        } else if content[cursor] == 'p' && variablesCount == 0 {
          toNextNumber();
          var x := extractNumber();
          match x {
            case {:split false} Error(t) =>
              {
                return Error(t);
              }
            case {:split false} Just(number) =>
              {
                if 0 < number < Int32.max {
                  variablesCount := number;
                  ok := true;
                } else {
                  return Error(""Variables count is bigger than Int32.max"");
                }
              }
          }
          toNextNumber();
          x := extractNumber();
          match x {
            case {:split false} Error(t) =>
              {
                return Error(t);
              }
            case {:split false} Just(number) =>
              {
                clausesCount := number;
              }
          }
          skipLine();
        } else if content[cursor] == 'p' {
          return Error(""Twice p? what are you doing?"");
        } else if ok {
          toNextNumber();
          if clauseLength == 0 && cursor == contentLength {
            break;
          }
          var x := extractNumber();
          match x {
            case {:split false} Error(t) =>
              {
                return Error(t);
              }
            case {:split false} Just(number) =>
              {
                if number == 0 && clauseLength > 0 {
                  clauses := clauses + [clause[..clauseLength]];
                  if Int32.max - clauseLength > literalsCount {
                    literalsCount := literalsCount + clauseLength;
                  } else {
                    return Error(""The number of literals is to big"");
                  }
                  clauseLength := 0;
                } else if number != 0 {
                  if clauseLength < 1000 {
                    if (number < 0 && 0 < -number <= variablesCount) || (number > 0 && 0 < number <= variablesCount) {
                      clause[clauseLength] := number;
                      clauseLength := clauseLength + 1;
                      var k: Int32.t := clauseLength - 1;
                      while 0 < k && clause[k - 1] > clause[k]
                        invariant 0 <= k <= clauseLength
                        invariant forall z :: 0 <= z < clauseLength ==> (clause[z] < 0 && 0 < -clause[z] <= variablesCount) || (clause[z] > 0 && 0 < clause[z] <= variablesCount)
                        invariant forall x, y :: 0 <= x < y < clauseLength && x != k && y != k ==> clause[x] < clause[y]
                        invariant forall x, y :: k <= x < y < clauseLength ==> clause[x] < clause[y]
                        decreases k
                        modifies clause
                      {
                        var aux := clause[k];
                        clause[k] := clause[k - 1];
                        clause[k - 1] := aux;
                        k := k - 1;
                      }
                      if k > 0 && clause[k - 1] == clause[k] {
                        return Error(""duplice literal in clause"");
                      }
                    } else {
                      return Error(""literal bigger than variablesCount"");
                    }
                  } else {
                    return Error(""clause longer than 1000"");
                  }
                }
              }
          }
        }
        if cursor < contentLength && oldCursor == cursor {
          cursor := cursor + 1;
        }
      }
      if !(0 < |clauses| < Int32.max as int) {
        return Error(""number of clauses incorrect"");
      }
      if |clauses| != clausesCount as int {
        return Error(""different number of clauses"");
      }
      if ok {
        return Just((variablesCount, clauses));
      } else {
        return Error(""p not found"");
      }
    }
  }

  predicate valid'(c: array<char>)
    decreases c
  {
    0 < c.Length < Int32.max as int
  }
}

module {:extern ""FileInput""} FileInput {
  class {:extern ""Reader""} Reader {
    static function method {:extern ""getContent""} getContent(): array<char>

    static function method {:extern ""getTimestamp""} getTimestamp(): int
  }
}

trait DataStructures {
  var variablesCount: Int32.t
  var clauses: seq<seq<Int32.t>>
  var clausesCount: Int32.t
  var clauseLength: array<Int32.t>
  var truthAssignment: array<Int32.t>
  var trueLiteralsCount: array<Int32.t>
  var falseLiteralsCount: array<Int32.t>
  var positiveLiteralsToClauses: array<seq<Int32.t>>
  var negativeLiteralsToClauses: array<seq<Int32.t>>
  var decisionLevel: Int32.t
  var traceVariable: array<Int32.t>
  var traceValue: array<bool>
  var traceDLStart: array<Int32.t>
  var traceDLEnd: array<Int32.t>
  ghost var assignmentsTrace: set<(Int32.t, bool)>

  predicate validVariablesCount()
    reads `variablesCount
    decreases {this}
  {
    0 < variablesCount < Int32.max
  }

  predicate validLiteral(literal: Int32.t)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, literal
  {
    if literal == 0 then
      false
    else if -variablesCount <= literal && literal <= variablesCount then
      true
    else
      false
  }

  predicate validClause(clause: seq<Int32.t>)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, clause
  {
    |clause| < Int32.max as int &&
    (forall x: int, y: int :: 
      0 <= x < y < |clause| ==>
        clause[x] != clause[y]) &&
    forall literal: Int32.t :: 
      literal in clause ==>
        validLiteral(literal)
  }

  predicate validClauses()
    requires validVariablesCount()
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}
  {
    0 < |clauses| == clausesCount as int <= Int32.max as int &&
    clauseLength.Length == clausesCount as int &&
    (forall i: Int32.t :: 
      0 <= i < clausesCount ==>
        0 < clauseLength[i] as int == |clauses[i]| < Int32.max as int) &&
    forall clause: seq<Int32.t> :: 
      clause in clauses ==>
        validClause(clause)
  }

  predicate validVariable(variable: Int32.t)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, variable
  {
    0 <= variable < variablesCount
  }

  predicate validAssignmentTrace()
    requires validVariablesCount()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue, `assignmentsTrace
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue, this}
  {
    validAssignmentTraceBasic() &&
    validTraceDL() &&
    validTraceVariable() &&
    validAssignmentTraceGhost()
  }

  predicate validAssignmentTraceBasic()
    requires validVariablesCount()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue}
  {
    0 < variablesCount < Int32.max &&
    -1 <= decisionLevel < variablesCount &&
    traceVariable.Length == variablesCount as int &&
    traceValue.Length == variablesCount as int &&
    traceDLStart.Length == variablesCount as int &&
    traceDLEnd.Length == variablesCount as int &&
    traceVariable != traceDLStart &&
    traceVariable != traceDLEnd &&
    traceDLStart != traceDLEnd
  }

  predicate validTraceDL()
    requires validVariablesCount()
    requires validAssignmentTraceBasic()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue}
  {
    (forall dl: Int32.t :: 
      0 <= dl < decisionLevel ==>
        0 <= traceDLStart[dl] < traceDLEnd[dl] <= variablesCount) &&
    (decisionLevel >= 0 ==>
      traceDLStart[0] == 0 &&
      0 <= traceDLStart[decisionLevel] <= traceDLEnd[decisionLevel] <= variablesCount) &&
    forall dl: Int32.t :: 
      0 < dl <= decisionLevel ==>
        traceDLStart[dl] == traceDLEnd[dl - 1]
  }

  predicate validTraceVariable()
    requires validVariablesCount()
    requires validAssignmentTraceBasic()
    requires validTraceDL()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue}
  {
    decisionLevel >= 0 ==>
      (forall i: Int32.t :: 
        0 <= i < traceDLEnd[decisionLevel] ==>
          validVariable(traceVariable[i])) &&
      forall i: Int32.t :: 
        0 <= i < traceDLEnd[decisionLevel] ==>
          forall j: Int32.t :: 
            0 <= j < traceDLEnd[decisionLevel] &&
            i != j ==>
              traceVariable[i] != traceVariable[j]
  }

  predicate validAssignmentTraceGhost()
    requires validVariablesCount()
    requires validAssignmentTraceBasic()
    requires validTraceDL()
    requires validTraceVariable()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue, `assignmentsTrace
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue, this}
  {
    (decisionLevel == -1 ==>
      assignmentsTrace == {}) &&
    (decisionLevel >= 0 ==>
      (forall i: Int32.t :: 
        0 <= i < traceDLEnd[decisionLevel] ==>
          (traceVariable[i], traceValue[i]) in assignmentsTrace) &&
      forall x: (Int32.t, bool) :: 
        x in assignmentsTrace ==>
          exists i: Int32.t :: 
            0 <= i < traceDLEnd[decisionLevel] &&
            (traceVariable[i], traceValue[i]) == x)
  }

  function convertIntToBool(x: Int32.t): bool
    decreases x
  {
    if x == 0 then
      false
    else
      true
  }

  predicate validValuesTruthAssignment(truthAssignment: seq<Int32.t>)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, truthAssignment
  {
    |truthAssignment| == variablesCount as int &&
    |truthAssignment| <= Int32.max as int &&
    forall i: int :: 
      0 <= i < |truthAssignment| ==>
        -1 <= truthAssignment[i] <= 1
  }

  predicate validTruthAssignment()
    requires validVariablesCount()
    requires validAssignmentTrace()
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment
    decreases {this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment}
  {
    validValuesTruthAssignment(truthAssignment[..]) &&
    (forall i: Int32.t :: 
      0 <= i < variablesCount &&
      truthAssignment[i] != -1 ==>
        (i, convertIntToBool(truthAssignment[i])) in assignmentsTrace) &&
    forall i: Int32.t :: 
      0 <= i < variablesCount &&
      truthAssignment[i] == -1 ==>
        (i, false) !in assignmentsTrace &&
        (i, true) !in assignmentsTrace
  }

  function getLiteralValue(truthAssignment: seq<Int32.t>, literal: Int32.t): Int32.t
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validLiteral(literal)
    reads `variablesCount
    decreases {this}, truthAssignment, literal
  {
    ghost var variable: Int32.t := Utils.abs(literal) - 1;
    if truthAssignment[variable] == -1 then
      -1
    else if literal < 0 then
      1 - truthAssignment[variable]
    else
      truthAssignment[variable]
  }

  predicate isClauseSatisfied(truthAssignment: seq<Int32.t>, clauseIndex: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires 0 <= clauseIndex as int < |clauses|
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, truthAssignment, clauseIndex
  {
    assert validClause(clauses[clauseIndex]);
    exists literal: Int32.t :: 
      literal in clauses[clauseIndex] &&
      getLiteralValue(truthAssignment, literal) == 1
  }

  function method getVariableFromLiteral(literal: Int32.t): Int32.t
    requires validVariablesCount()
    requires validLiteral(literal)
    reads this
    ensures validVariable(getVariableFromLiteral(literal))
    decreases {this}, literal
  {
    Utils.abs(literal) - 1
  }

  function method convertLVtoVI(literal: Int32.t, value: bool): (Int32.t, Int32.t)
    requires validVariablesCount()
    requires validLiteral(literal)
    reads this
    ensures validVariable(convertLVtoVI(literal, value).0)
    ensures convertLVtoVI(literal, value).0 == getVariableFromLiteral(literal)
    ensures convertLVtoVI(literal, value).1 in [0, 1]
    decreases {this}, literal, value
  {
    var variable: Int32.t := getVariableFromLiteral(literal);
    var v: Int32.t := if value then 1 else 0;
    var val: Int32.t := if literal < 0 then 1 - v else v;
    (variable, val)
  }

  predicate validTrueLiteralsCount(truthAssignment: seq<Int32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauses, `trueLiteralsCount, `clauseLength, `clausesCount, trueLiteralsCount, clauseLength
    decreases {this, this, this, this, this, trueLiteralsCount, clauseLength}, truthAssignment
  {
    trueLiteralsCount.Length == |clauses| &&
    forall i: int :: 
      0 <= i < |clauses| ==>
        0 <= trueLiteralsCount[i] == countTrueLiterals(truthAssignment, clauses[i])
  }

  function countUnsetVariables(truthAssignment: seq<Int32.t>): Int32.t
    requires |truthAssignment| <= Int32.max as int
    ensures 0 <= countUnsetVariables(truthAssignment) as int <= |truthAssignment| <= Int32.max as int
    decreases truthAssignment
  {
    if |truthAssignment| == 0 then
      0
    else
      ghost var ok: Int32.t := if truthAssignment[0] == -1 then 1 else 0; ok + countUnsetVariables(truthAssignment[1..])
  }

  function countTrueLiterals(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>): Int32.t
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    reads `variablesCount, `clauseLength, clauseLength
    ensures 0 <= countTrueLiterals(truthAssignment, clause) as int <= |clause|
    decreases {this, this, clauseLength}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      ghost var ok: Int32.t := if getLiteralValue(truthAssignment, clause[0]) == 1 then 1 else 0; ok + countTrueLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ prop_countTrueLiterals_initialTruthAssignment(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countTrueLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ countTrueLiterals0_noLiteralsTrue(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) == 0
    ensures forall literal: Int32.t :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1
    decreases truthAssignment, clause
  {
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ countTrueLiteralsX_existsTrueLiteral(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) > 0
    ensures exists literal: Int32.t :: literal in clause && getLiteralValue(truthAssignment, literal) == 1
    decreases truthAssignment, clause
  {
  }

  predicate validFalseLiteralsCount(truthAssignment: seq<Int32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauses, `falseLiteralsCount, `clauseLength, `clausesCount, falseLiteralsCount, clauseLength
    decreases {this, this, this, this, this, falseLiteralsCount, clauseLength}, truthAssignment
  {
    falseLiteralsCount.Length == |clauses| &&
    forall i: int :: 
      0 <= i < |clauses| ==>
        0 <= falseLiteralsCount[i] == countFalseLiterals(truthAssignment, clauses[i])
  }

  function countFalseLiterals(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>): Int32.t
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    reads `variablesCount, `clauseLength, clauseLength
    ensures 0 <= countFalseLiterals(truthAssignment, clause) as int <= |clause|
    decreases {this, this, clauseLength}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      ghost var ok: Int32.t := if getLiteralValue(truthAssignment, clause[0]) == 0 then 1 else 0; ok + countFalseLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ prop_countFalseLiterals_initialTruthAssignment(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countFalseLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
  }

  predicate validPositiveLiteralsToClauses()
    requires validVariablesCount()
    requires validClauses()
    reads this, positiveLiteralsToClauses, clauseLength
    decreases {this, positiveLiteralsToClauses, clauseLength}
  {
    positiveLiteralsToClauses.Length == variablesCount as int &&
    (forall variable: Int32.t :: 
      0 <= variable as int < positiveLiteralsToClauses.Length ==>
        validPositiveLiteralToClause(variable, positiveLiteralsToClauses[variable])) &&
    forall variable: Int32.t :: 
      0 <= variable as int < positiveLiteralsToClauses.Length ==>
        |positiveLiteralsToClauses[variable]| <= clausesCount as int
  }

  predicate validPositiveLiteralToClause(variable: Int32.t, s: seq<Int32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= variable < variablesCount
    reads this, clauseLength
    decreases {this, clauseLength}, variable, s
  {
    Utils.valuesBoundedBy(s, 0, |clauses|) &&
    Utils.orderedAsc(s) &&
    (forall clauseIndex: Int32.t :: 
      clauseIndex in s ==>
        variable + 1 in clauses[clauseIndex]) &&
    forall clauseIndex: Int32.t :: 
      0 <= clauseIndex as int < |clauses| &&
      clauseIndex !in s ==>
        variable + 1 !in clauses[clauseIndex]
  }

  predicate validNegativeLiteralsToClauses()
    requires validVariablesCount()
    requires validClauses()
    reads this, negativeLiteralsToClauses, clauseLength
    decreases {this, negativeLiteralsToClauses, clauseLength}
  {
    negativeLiteralsToClauses.Length == variablesCount as int &&
    forall v: Int32.t :: 
      0 <= v as int < negativeLiteralsToClauses.Length ==>
        validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v]) &&
        forall variable: Int32.t :: 
          0 <= variable as int < negativeLiteralsToClauses.Length ==>
            |negativeLiteralsToClauses[variable]| <= clausesCount as int
  }

  predicate validNegativeLiteralsToClause(variable: Int32.t, s: seq<Int32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= variable < variablesCount
    reads this, clauseLength
    decreases {this, clauseLength}, variable, s
  {
    Utils.valuesBoundedBy(s, 0, |clauses|) &&
    Utils.orderedAsc(s) &&
    (forall clauseIndex: Int32.t :: 
      clauseIndex in s ==>
        -variable - 1 in clauses[clauseIndex]) &&
    forall clauseIndex: Int32.t :: 
      0 <= clauseIndex as int < |clauses| &&
      clauseIndex !in s ==>
        -variable - 1 !in clauses[clauseIndex]
  }

  predicate validReferences()
    reads this, truthAssignment, trueLiteralsCount, falseLiteralsCount, positiveLiteralsToClauses, negativeLiteralsToClauses, clauseLength
    decreases {this, truthAssignment, trueLiteralsCount, falseLiteralsCount, positiveLiteralsToClauses, negativeLiteralsToClauses, clauseLength}
  {
    truthAssignment != trueLiteralsCount &&
    truthAssignment != falseLiteralsCount &&
    truthAssignment != clauseLength &&
    truthAssignment != traceVariable &&
    truthAssignment != traceDLStart &&
    truthAssignment != traceDLEnd &&
    trueLiteralsCount != falseLiteralsCount &&
    trueLiteralsCount != clauseLength &&
    trueLiteralsCount != traceVariable &&
    trueLiteralsCount != traceDLStart &&
    trueLiteralsCount != traceDLEnd &&
    falseLiteralsCount != clauseLength &&
    falseLiteralsCount != traceVariable &&
    falseLiteralsCount != traceDLStart &&
    falseLiteralsCount != traceDLEnd &&
    clauseLength != traceVariable &&
    clauseLength != traceDLStart &&
    clauseLength != traceDLEnd &&
    positiveLiteralsToClauses != negativeLiteralsToClauses
  }

  predicate valid()
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    validReferences() &&
    validVariablesCount() &&
    validClauses() &&
    countLiterals(clausesCount) < Int32.max as int &&
    validAssignmentTrace() &&
    validTruthAssignment() &&
    validTrueLiteralsCount(truthAssignment[..]) &&
    validFalseLiteralsCount(truthAssignment[..]) &&
    validPositiveLiteralsToClauses() &&
    validNegativeLiteralsToClauses()
  }

  function countLiterals(clauseIndex: Int32.t): int
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= clauseIndex <= clausesCount
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, clauseIndex
  {
    if clauseIndex == 0 then
      0
    else
      |clauses[clauseIndex - 1]| + countLiterals(clauseIndex - 1)
  }

  lemma /*{:_induction this, cI}*/ countLiterals_monotone(cI: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires countLiterals(clausesCount) < Int32.max as int
    requires 0 <= cI <= clausesCount
    ensures 0 <= cI < clausesCount ==> countLiterals(cI) < countLiterals(cI + 1) < Int32.max as int
    decreases clausesCount - cI
  {
  }

  lemma /*{:_induction this, oldTau, newTau}*/ clausesNotImpacted_TFArraysSame(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, impactedClauses: seq<Int32.t>, impactedClauses': seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validClauses()
    requires validTrueLiteralsCount(oldTau)
    requires validFalseLiteralsCount(oldTau)
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex])
    requires validVariable(variable)
    requires newTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses)
    requires newTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses')
    requires newTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses')
    requires newTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses)
    requires forall x: Int32.t :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    ensures forall clauseIndex: Int32.t :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
    ensures forall clauseIndex: Int32.t :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    decreases oldTau, newTau, variable, impactedClauses, impactedClauses'
  {
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ setVariable_countTrueLiteralsIncreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires newTau[variable] == 1 ==> variable + 1 in clause
    requires newTau[variable] == 0 ==> -variable - 1 in clause
    requires forall x: Int32.t :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    requires countTrueLiterals(oldTau, clause) as int < |clause|
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) + 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ setVariable_countFalseLiteralsIncreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires newTau[variable] == 1 ==> -variable - 1 in clause
    requires newTau[variable] == 0 ==> variable + 1 in clause
    requires forall x: Int32.t :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    requires countFalseLiterals(oldTau, clause) as int < |clause|
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) + 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction this, oldTau, clause}*/ literalTrue_countTrueLiteralsAtLeastOne(oldTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> variable + 1 in clause
    requires oldTau[variable] == 0 ==> -variable - 1 in clause
    requires oldTau[variable] in [0, 1]
    ensures 0 < countTrueLiterals(oldTau, clause)
    decreases oldTau, variable, clause
  {
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ unsetVariable_countTrueLiteralsDecreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> variable + 1 in clause
    requires oldTau[variable] == 0 ==> -variable - 1 in clause
    requires forall x: Int32.t :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) - 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ unsetVariable_countFalseLiteralsDecreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> -variable - 1 in clause
    requires oldTau[variable] == 0 ==> variable + 1 in clause
    requires forall x: Int32.t :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) - 1
    decreases oldTau, newTau, variable, clause
  {
  }

  lemma /*{:_induction this, oldTau, newTau}*/ undoImpactedClauses_TFSArraysModified(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, impactedClauses: seq<Int32.t>, impactedClauses': seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validClauses()
    requires validTrueLiteralsCount(oldTau)
    requires validFalseLiteralsCount(oldTau)
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex])
    requires validVariable(variable)
    requires oldTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses)
    requires oldTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses')
    requires oldTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses')
    requires oldTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses)
    requires forall x: Int32.t :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == trueLiteralsCount[clauseIndex]
    requires forall clauseIndex: int :: 0 <= clauseIndex < |clauses| ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == falseLiteralsCount[clauseIndex]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures forall clauseIndex: Int32.t :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
    ensures forall clauseIndex: Int32.t :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    decreases oldTau, newTau, variable, impactedClauses, impactedClauses'
  {
  }

  lemma /*{:_induction this}*/ notDone_literalsToSet(i: Int32.t)
    requires valid()
    requires 0 <= i as int < |clauses|
    requires falseLiteralsCount[i] as int < |clauses[i]|
    requires trueLiteralsCount[i] == 0
    requires validClause(clauses[i])
    requires forall literal: Int32.t :: literal in clauses[i] ==> validLiteral(literal)
    ensures exists literal: Int32.t :: literal in clauses[i] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases i
  {
  }

  lemma /*{:_induction this, oldTau, newTau}*/ setVariable_unsetVariablesDecreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t)
    requires validVariablesCount()
    requires validVariable(variable)
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires |oldTau| == |newTau|
    requires forall i: Int32.t :: 0 <= i as int < |oldTau| && i != variable ==> oldTau[i] == newTau[i]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    requires countUnsetVariables(newTau) as int < |newTau|
    ensures countUnsetVariables(newTau) + 1 == countUnsetVariables(oldTau)
    decreases oldTau, newTau, variable
  {
  }

  predicate isVariableSet(truthAssignment: seq<Int32.t>, variable: Int32.t)
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validVariable(variable)
    reads this
    decreases {this}, truthAssignment, variable
  {
    truthAssignment[variable] != -1
  }

  predicate isSatisfied(truthAssignment: seq<Int32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, truthAssignment
  {
    forall cI: Int32.t :: 
      0 <= cI as int < |clauses| ==>
        isClauseSatisfied(truthAssignment, cI)
  }

  predicate isExtendingTau(tau: seq<Int32.t>, tau': seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validValuesTruthAssignment(tau')
    reads `variablesCount
    decreases {this}, tau, tau'
  {
    forall i: int :: 
      0 <= i < |tau| &&
      tau[i] != -1 ==>
        tau[i] == tau'[i]
  }

  predicate isTauComplete(tau: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    reads `variablesCount
    decreases {this}, tau
  {
    forall i: int :: 
      0 <= i < |tau| ==>
        tau[i] != -1
  }

  function getExtendedCompleteTau(tau: seq<Int32.t>): seq<Int32.t>
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires isSatisfiableExtend(tau)
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    ensures ghost var tau': seq<Int32.t> := getExtendedCompleteTau(tau); validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau')
    decreases {this, this, this, this, clauseLength}, tau
  {
    ghost var tau': seq<Int32.t> :| validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau');
    tau'
  }

  predicate isSatisfiableExtend(tau: seq<Int32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, tau
  {
    exists tau': seq<Int32.t> :: 
      validValuesTruthAssignment(tau') &&
      isTauComplete(tau') &&
      isExtendingTau(tau, tau') &&
      isSatisfied(tau')
  }

  function method isUnitClause(index: Int32.t): bool
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validTruthAssignment()
    requires validClauses()
    requires validTrueLiteralsCount(truthAssignment[..])
    requires validFalseLiteralsCount(truthAssignment[..])
    requires 0 <= index < clausesCount
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength
    decreases {this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength}, index
  {
    trueLiteralsCount[index] == 0 &&
    clauseLength[index] - falseLiteralsCount[index] == 1
  }

  function method isEmptyClause(index: Int32.t): bool
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validTruthAssignment()
    requires validClauses()
    requires validTrueLiteralsCount(truthAssignment[..])
    requires validFalseLiteralsCount(truthAssignment[..])
    requires 0 <= index < clausesCount
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength
    decreases {this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength}, index
  {
    clauseLength[index] == falseLiteralsCount[index]
  }
}

module Utils {

  import Int32
  method newInitializedSeq(n: Int32.t, d: Int32.t) returns (r: array<Int32.t>)
    requires 0 < n
    ensures r.Length == n as int
    ensures forall j: int :: 0 <= j < r.Length ==> r[j] == d
    ensures fresh(r)
    decreases n, d
  {
    r := new Int32.t[n];
    var index: Int32.t := 0;
    while index < n
      invariant 0 <= index as int <= r.Length == n as int
      invariant forall j: Int32.t :: 0 <= j < index ==> r[j] == d
      decreases n - index
    {
      r[index] := d;
      index := index + 1;
    }
  }

  function method abs(literal: Int32.t): Int32.t
    decreases literal
  {
    if literal < 0 then
      -literal
    else
      literal
  }

  lemma prop_seq_predicate(q: int, abc: seq<Int32.t>)
    requires forall j: Int32.t :: j in abc ==> 0 <= j as int < q
    ensures forall j: int :: 0 <= j < |abc| ==> 0 <= abc[j] as int < q
    decreases q, abc
  {
  }

  predicate valueBoundedBy(value: Int32.t, min: int, max: int)
    decreases value, min, max
  {
    min <= value as int < max
  }

  predicate valuesBoundedBy(s: seq<Int32.t>, min: int, max: int)
    decreases s, min, max
  {
    (forall el: Int32.t :: 
      el in s ==>
        valueBoundedBy(el, min, max)) &&
    forall i: int :: 
      0 <= i < |s| ==>
        valueBoundedBy(s[i], min, max)
  }

  predicate orderedAsc(s: seq<Int32.t>)
    decreases s
  {
    forall x: int, y: int :: 
      0 <= x < y < |s| ==>
        s[x] < s[y]
  }

  predicate InRange(lo: Int32.t, hi: Int32.t, i: Int32.t)
    decreases lo, hi, i
  {
    lo <= i < hi
  }

  function RangeSet(lo: Int32.t, hi: Int32.t): set<Int32.t>
    decreases lo, hi
  {
    set i: Int32.t {:trigger InRange(lo, hi, i)} | lo <= i < hi && InRange(lo, hi, i)
  }

  lemma CardinalityRangeSet(lo: Int32.t, hi: Int32.t)
    requires 0 <= lo <= hi
    ensures |RangeSet(lo, hi)| == if lo >= hi then 0 else (hi - lo) as int
    decreases hi - lo
  {
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i])) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m) {
        return this;
      }

      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      int startingElement = checked((int)m);
      if (startingElement == 0) {
        return this;
      }

      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero) {
        return this;
      }

      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int)lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {
  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace Int32_Compile {

  public partial class t {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static int max { get {
      return 2000000;
    } }
    public static int min { get {
      return -2000000;
    } }
  }
} // end of namespace Int32_Compile
namespace MyDatatypes_Compile {

  public interface _IMaybe<T> {
    bool is_Error { get; }
    bool is_Just { get; }
    Dafny.ISequence<char> dtor_Error_a0 { get; }
    T dtor_value { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() { }
    public static _IMaybe<T> Default() {
      return create_Error(Dafny.Sequence<char>.Empty);
    }
    public static Dafny.TypeDescriptor<MyDatatypes_Compile._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<MyDatatypes_Compile._IMaybe<T>>(MyDatatypes_Compile.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Error(Dafny.ISequence<char> _a0) {
      return new Maybe_Error<T>(_a0);
    }
    public static _IMaybe<T> create_Just(T @value) {
      return new Maybe_Just<T>(@value);
    }
    public bool is_Error { get { return this is Maybe_Error<T>; } }
    public bool is_Just { get { return this is Maybe_Just<T>; } }
    public Dafny.ISequence<char> dtor_Error_a0 {
      get {
        var d = this;
        return ((Maybe_Error<T>)d)._a0;
      }
    }
    public T dtor_value {
      get {
        var d = this;
        return ((Maybe_Just<T>)d).@value;
      }
    }
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Maybe_Error<T> : Maybe<T> {
    public readonly Dafny.ISequence<char> _a0;
    public Maybe_Error(Dafny.ISequence<char> _a0) {
      this._a0 = _a0;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Error<__T>(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as MyDatatypes_Compile.Maybe_Error<T>;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MyDatatypes_Compile.Maybe.Error";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Maybe_Just<T> : Maybe<T> {
    public readonly T @value;
    public Maybe_Just(T @value) {
      this.@value = @value;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Just<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as MyDatatypes_Compile.Maybe_Just<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MyDatatypes_Compile.Maybe.Just";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

} // end of namespace MyDatatypes_Compile
namespace InputPredicate_Compile {

} // end of namespace InputPredicate_Compile
namespace Useless_Compile {

  public partial class Parser {
    public Parser() {
      this.content = new char[0];
      this.contentLength = 0;
      this.cursor = 0;
    }
    public  char[] content {get; set;}
    public  int contentLength {get; set;}
    public  int cursor {get; set;}
    public void __ctor(char[] c)
    {
      (this).content = c;
      (this).contentLength = (int)(c).Length;
      (this).cursor = 0;
    }
    public void skipLine()
    {
      while (((this.cursor) < (this.contentLength)) && (((this.content)[(int)(this.cursor)]) != ('\n'))) {
        (this).cursor = (this.cursor) + (1);
      }
      if ((this.cursor) < (this.contentLength)) {
        (this).cursor = (this.cursor) + (1);
      }
    }
    public void toNextNumber()
    {
      while (((this.cursor) < (this.contentLength)) && (!(((('0') <= ((this.content)[(int)(this.cursor)])) && (((this.content)[(int)(this.cursor)]) <= ('9'))) || (((this.content)[(int)(this.cursor)]) == ('-'))))) {
        (this).cursor = (this.cursor) + (1);
      }
    }
    public MyDatatypes_Compile._IMaybe<int> extractNumber()
    {
      MyDatatypes_Compile._IMaybe<int> res = MyDatatypes_Compile.Maybe<int>.Default();
      int _0_number;
      _0_number = 0;
      bool _1_isNegative;
      _1_isNegative = false;
      if (((this.cursor) < (this.contentLength)) && (((this.content)[(int)(this.cursor)]) == ('-'))) {
        _1_isNegative = true;
        (this).cursor = (this.cursor) + (1);
      }
      if ((this.cursor) == (this.contentLength)) {
        res = MyDatatypes_Compile.Maybe<int>.create_Error(Dafny.Sequence<char>.FromString("There is no number around here."));
        return res;
      }
      while (((this.cursor) < (this.contentLength)) && ((('0') <= ((this.content)[(int)(this.cursor)])) && (((this.content)[(int)(this.cursor)]) <= ('9')))) {
        int _2_digit;
        _2_digit = ((int)((this.content)[(int)(this.cursor)])) - ((int)('0'));
        if ((_0_number) <= (Dafny.Helpers.EuclideanDivision_int((Int32_Compile.__default.max) - (_2_digit), 10))) {
          _0_number = ((_0_number) * (10)) + (_2_digit);
        } else {
          res = MyDatatypes_Compile.Maybe<int>.create_Error(Dafny.Sequence<char>.FromString("There is a number bigger than Int32.max"));
          return res;
        }
        (this).cursor = (this.cursor) + (1);
      }
      if (_1_isNegative) {
        _0_number = (0) - (_0_number);
      }
      res = MyDatatypes_Compile.Maybe<int>.create_Just(_0_number);
      return res;
      return res;
    }
    public MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> parse()
    {
      MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.Default();
      int _3_variablesCount;
      _3_variablesCount = 0;
      int _4_clausesCount;
      _4_clausesCount = 0;
      Dafny.ISequence<Dafny.ISequence<int>> _5_clauses;
      _5_clauses = Dafny.Sequence<Dafny.ISequence<int>>.FromElements();
      int[] _6_clause;
      int[] _nw0 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger(1000), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      _6_clause = _nw0;
      int _7_clauseLength;
      _7_clauseLength = 0;
      bool _8_ok;
      _8_ok = false;
      int _9_literalsCount;
      _9_literalsCount = 0;
      int _10_contentLength;
      _10_contentLength = (int)(this.content).Length;
      while ((this.cursor) < (_10_contentLength)) {
        int _11_oldCursor;
        _11_oldCursor = this.cursor;
        if (((this.content)[(int)(this.cursor)]) == ('c')) {
          (this).skipLine();
        } else if ((((this.content)[(int)(this.cursor)]) == ('p')) && ((_3_variablesCount) == (0))) {
          (this).toNextNumber();
          MyDatatypes_Compile._IMaybe<int> _12_x;
          MyDatatypes_Compile._IMaybe<int> _out0;
          _out0 = (this).extractNumber();
          _12_x = _out0;
          MyDatatypes_Compile._IMaybe<int> _source0 = _12_x;
          if (_source0.is_Error) {
            Dafny.ISequence<char> _13___mcc_h0 = _source0.dtor_Error_a0;
            Dafny.ISequence<char> _14_t = _13___mcc_h0;
            {
              result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(_14_t);
              return result;
            }
          } else {
            int _15___mcc_h1 = _source0.dtor_value;
            int _16_number = _15___mcc_h1;
            {
              if (((0) < (_16_number)) && ((_16_number) < (Int32_Compile.__default.max))) {
                _3_variablesCount = _16_number;
                _8_ok = true;
              } else {
                result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("Variables count is bigger than Int32.max"));
                return result;
              }
            }
          }
          (this).toNextNumber();
          MyDatatypes_Compile._IMaybe<int> _out1;
          _out1 = (this).extractNumber();
          _12_x = _out1;
          MyDatatypes_Compile._IMaybe<int> _source1 = _12_x;
          if (_source1.is_Error) {
            Dafny.ISequence<char> _17___mcc_h2 = _source1.dtor_Error_a0;
            Dafny.ISequence<char> _18_t = _17___mcc_h2;
            {
              result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(_18_t);
              return result;
            }
          } else {
            int _19___mcc_h3 = _source1.dtor_value;
            int _20_number = _19___mcc_h3;
            {
              _4_clausesCount = _20_number;
            }
          }
          (this).skipLine();
        } else if (((this.content)[(int)(this.cursor)]) == ('p')) {
          result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("Twice p? what are you doing?"));
          return result;
        } else if (_8_ok) {
          (this).toNextNumber();
          if (((_7_clauseLength) == (0)) && ((this.cursor) == (_10_contentLength))) {
            goto after_0;
          }
          MyDatatypes_Compile._IMaybe<int> _21_x;
          MyDatatypes_Compile._IMaybe<int> _out2;
          _out2 = (this).extractNumber();
          _21_x = _out2;
          MyDatatypes_Compile._IMaybe<int> _source2 = _21_x;
          if (_source2.is_Error) {
            Dafny.ISequence<char> _22___mcc_h4 = _source2.dtor_Error_a0;
            Dafny.ISequence<char> _23_t = _22___mcc_h4;
            {
              result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(_23_t);
              return result;
            }
          } else {
            int _24___mcc_h5 = _source2.dtor_value;
            int _25_number = _24___mcc_h5;
            {
              if (((_25_number) == (0)) && ((_7_clauseLength) > (0))) {
                _5_clauses = Dafny.Sequence<Dafny.ISequence<int>>.Concat(_5_clauses, Dafny.Sequence<Dafny.ISequence<int>>.FromElements(Dafny.Helpers.SeqFromArray(_6_clause).Take(_7_clauseLength)));
                if (((Int32_Compile.__default.max) - (_7_clauseLength)) > (_9_literalsCount)) {
                  _9_literalsCount = (_9_literalsCount) + (_7_clauseLength);
                } else {
                  result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("The number of literals is to big"));
                  return result;
                }
                _7_clauseLength = 0;
              } else if ((_25_number) != (0)) {
                if ((_7_clauseLength) < (1000)) {
                  if ((((_25_number) < (0)) && (((0) < ((0) - (_25_number))) && (((0) - (_25_number)) <= (_3_variablesCount)))) || (((_25_number) > (0)) && (((0) < (_25_number)) && ((_25_number) <= (_3_variablesCount))))) {
                    (_6_clause)[(int)((_7_clauseLength))] = _25_number;
                    _7_clauseLength = (_7_clauseLength) + (1);
                    int _26_k;
                    _26_k = (_7_clauseLength) - (1);
                    while (((0) < (_26_k)) && (((_6_clause)[(int)((_26_k) - (1))]) > ((_6_clause)[(int)(_26_k)]))) {
                      int _27_aux;
                      _27_aux = (_6_clause)[(int)(_26_k)];
                      (_6_clause)[(int)((_26_k))] = (_6_clause)[(int)((_26_k) - (1))];
                      var _index0 = (_26_k) - (1);
                      (_6_clause)[(int)(_index0)] = _27_aux;
                      _26_k = (_26_k) - (1);
                    }
                    if (((_26_k) > (0)) && (((_6_clause)[(int)((_26_k) - (1))]) == ((_6_clause)[(int)(_26_k)]))) {
                      result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("duplice literal in clause"));
                      return result;
                    }
                  } else {
                    result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("literal bigger than variablesCount"));
                    return result;
                  }
                } else {
                  result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("clause longer than 1000"));
                  return result;
                }
              }
            }
          }
        }
        if (((this.cursor) < (_10_contentLength)) && ((_11_oldCursor) == (this.cursor))) {
          (this).cursor = (this.cursor) + (1);
        }
      continue_0: ;
      }
    after_0: ;
      if (!(((new BigInteger((_5_clauses).Count)).Sign == 1) && ((new BigInteger((_5_clauses).Count)) < (new BigInteger(Int32_Compile.__default.max))))) {
        result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("number of clauses incorrect"));
        return result;
      }
      if ((new BigInteger((_5_clauses).Count)) != (new BigInteger(_4_clausesCount))) {
        result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("different number of clauses"));
        return result;
      }
      if (_8_ok) {
        result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Just(_System.Tuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>.create(_3_variablesCount, _5_clauses));
        return result;
      } else {
        result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("p not found"));
        return result;
      }
      return result;
    }
  }

} // end of namespace Useless_Compile
namespace FileInput {


} // end of namespace FileInput
namespace Input_Compile {

  public partial class __default {
    public static MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> getInput()
    {
      MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.Default();
      char[] _28_input;
      _28_input = FileInput.Reader.getContent();
      if (((new BigInteger((_28_input).Length)).Sign == 1) && ((new BigInteger((_28_input).Length)) < (new BigInteger(Int32_Compile.__default.max)))) {
        Useless_Compile.Parser _29_parser;
        Useless_Compile.Parser _nw1 = new Useless_Compile.Parser();
        _nw1.__ctor(_28_input);
        _29_parser = _nw1;
        MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _30_x;
        MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _out3;
        _out3 = (_29_parser).parse();
        _30_x = _out3;
        result = _30_x;
        return result;
      } else {
        result = MyDatatypes_Compile.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("the file contains more data than Int32.max"));
        return result;
      }
      return result;
    }
    public static BigInteger getTimestamp() {
      return FileInput.Reader.getTimestamp();
    }
  }
} // end of namespace Input_Compile
namespace Utils_Compile {

  public partial class __default {
    public static int[] newInitializedSeq(int n, int d)
    {
      int[] r = new int[0];
      int[] _nw2 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(n, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      r = _nw2;
      int _31_index;
      _31_index = 0;
      while ((_31_index) < (n)) {
        (r)[(int)((_31_index))] = d;
        _31_index = (_31_index) + (1);
      }
      return r;
    }
    public static int abs(int literal) {
      if ((literal) < (0)) {
        return (0) - (literal);
      } else {
        return literal;
      }
    }
  }
} // end of namespace Utils_Compile
namespace _module {

  public partial class __default {
    public static void _Main()
    {
      BigInteger _32_starttime;
      _32_starttime = Input_Compile.__default.getTimestamp();
      MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _33_input;
      MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _out4;
      _out4 = Input_Compile.__default.getInput();
      _33_input = _out4;
      Dafny.BigRational _34_totalTime;
      _34_totalTime = (new Dafny.BigRational(((Input_Compile.__default.getTimestamp()) - (_32_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Time to read: "));
      Dafny.Helpers.Print(_34_totalTime);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
      MyDatatypes_Compile._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _source3 = _33_input;
      if (_source3.is_Error) {
        Dafny.ISequence<char> _35___mcc_h0 = _source3.dtor_Error_a0;
        Dafny.ISequence<char> _36_m = _35___mcc_h0;
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Error: "));
        Dafny.Helpers.Print(_36_m);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      } else {
        _System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> _37___mcc_h1 = _source3.dtor_value;
        _System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> _38_z = _37___mcc_h1;
        _System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> _let_tmp_rhs0 = _38_z;
        int _39_variablesCount = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<Dafny.ISequence<int>> _40_clauses = _let_tmp_rhs0.dtor__1;
        _32_starttime = Input_Compile.__default.getTimestamp();
        Formula _41_formula;
        Formula _nw3 = new Formula();
        _nw3.__ctor(_39_variablesCount, _40_clauses);
        _41_formula = _nw3;
        SATSolver _42_solver;
        SATSolver _nw4 = new SATSolver();
        _nw4.__ctor(_41_formula);
        _42_solver = _nw4;
        _34_totalTime = (new Dafny.BigRational(((Input_Compile.__default.getTimestamp()) - (_32_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Time to initialize: "));
        Dafny.Helpers.Print(_34_totalTime);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
        _32_starttime = Input_Compile.__default.getTimestamp();
        _ISAT__UNSAT _43_solution;
        _ISAT__UNSAT _out5;
        _out5 = (_42_solver).start();
        _43_solution = _out5;
        _34_totalTime = (new Dafny.BigRational(((Input_Compile.__default.getTimestamp()) - (_32_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Time to solve: "));
        Dafny.Helpers.Print(_34_totalTime);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
        _ISAT__UNSAT _source4 = _43_solution;
        if (_source4.is_SAT) {
          Dafny.ISequence<int> _44___mcc_h2 = _source4.dtor_tau;
          Dafny.ISequence<int> _45_x = _44___mcc_h2;
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s SATISFIABLE\n"));
        } else {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s UNSATISFIABLE\n"));
        }
      }
    }
  }

  public interface _ISAT__UNSAT {
    bool is_SAT { get; }
    bool is_UNSAT { get; }
    Dafny.ISequence<int> dtor_tau { get; }
    _ISAT__UNSAT DowncastClone();
  }
  public abstract class SAT__UNSAT : _ISAT__UNSAT {
    public SAT__UNSAT() { }
    private static readonly _ISAT__UNSAT theDefault = create_SAT(Dafny.Sequence<int>.Empty);
    public static _ISAT__UNSAT Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ISAT__UNSAT> _TYPE = new Dafny.TypeDescriptor<_ISAT__UNSAT>(SAT__UNSAT.Default());
    public static Dafny.TypeDescriptor<_ISAT__UNSAT> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISAT__UNSAT create_SAT(Dafny.ISequence<int> tau) {
      return new SAT__UNSAT_SAT(tau);
    }
    public static _ISAT__UNSAT create_UNSAT() {
      return new SAT__UNSAT_UNSAT();
    }
    public bool is_SAT { get { return this is SAT__UNSAT_SAT; } }
    public bool is_UNSAT { get { return this is SAT__UNSAT_UNSAT; } }
    public Dafny.ISequence<int> dtor_tau {
      get {
        var d = this;
        return ((SAT__UNSAT_SAT)d).tau;
      }
    }
    public abstract _ISAT__UNSAT DowncastClone();
  }
  public class SAT__UNSAT_SAT : SAT__UNSAT {
    public readonly Dafny.ISequence<int> tau;
    public SAT__UNSAT_SAT(Dafny.ISequence<int> tau) {
      this.tau = tau;
    }
    public override _ISAT__UNSAT DowncastClone() {
      if (this is _ISAT__UNSAT dt) { return dt; }
      return new SAT__UNSAT_SAT(tau);
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_SAT;
      return oth != null && object.Equals(this.tau, oth.tau);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tau));
      return (int) hash;
    }
    public override string ToString() {
      string s = "SAT_UNSAT.SAT";
      s += "(";
      s += Dafny.Helpers.ToString(this.tau);
      s += ")";
      return s;
    }
  }
  public class SAT__UNSAT_UNSAT : SAT__UNSAT {
    public SAT__UNSAT_UNSAT() {
    }
    public override _ISAT__UNSAT DowncastClone() {
      if (this is _ISAT__UNSAT dt) { return dt; }
      return new SAT__UNSAT_UNSAT();
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_UNSAT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SAT_UNSAT.UNSAT";
      return s;
    }
  }

  public partial class SATSolver {
    public SATSolver() {
      this.formula = default(Formula);
    }
    public  Formula formula {get; set;}
    public void __ctor(Formula f_k)
    {
      (this).formula = f_k;
    }
    public _ISAT__UNSAT step(int literal, bool @value)
    {
      _ISAT__UNSAT result = SAT__UNSAT.Default();
      (this.formula).increaseDecisionLevel();
      (this.formula).setLiteral(literal, @value);
      _ISAT__UNSAT _out6;
      _out6 = (this).solve();
      result = _out6;
      (this.formula).revertLastDecisionLevel();
      result = result;
      return result;
      return result;
    }
    public _ISAT__UNSAT solve()
    {
      _ISAT__UNSAT result = SAT__UNSAT.Default();
      bool _46_hasEmptyClause;
      bool _out7;
      _out7 = (this.formula).getHasEmptyClause();
      _46_hasEmptyClause = _out7;
      if (_46_hasEmptyClause) {
        result = SAT__UNSAT.create_UNSAT();
        return result;
      }
      bool _47_isEmpty;
      bool _out8;
      _out8 = (this.formula).getIsEmpty();
      _47_isEmpty = _out8;
      if (_47_isEmpty) {
        result = SAT__UNSAT.create_SAT(Dafny.Helpers.SeqFromArray(this.formula.truthAssignment));
        result = result;
        return result;
      }
      int _48_literal;
      int _out9;
      _out9 = (this.formula).chooseLiteral();
      _48_literal = _out9;
      _ISAT__UNSAT _out10;
      _out10 = (this).step(_48_literal, true);
      result = _out10;
      if ((result).is_SAT) {
        result = result;
        return result;
      }
      _ISAT__UNSAT _out11;
      _out11 = (this).step(_48_literal, false);
      result = _out11;
      result = result;
      return result;
      return result;
    }
    public _ISAT__UNSAT start()
    {
      _ISAT__UNSAT result = SAT__UNSAT.Default();
      (this.formula).level0UnitPropagation();
      _ISAT__UNSAT _out12;
      _out12 = (this).solve();
      result = _out12;
      return result;
    }
  }

  public partial class Formula : DataStructures {
    public Formula() {
      this._variablesCount = 0;
      this._clauses = Dafny.Sequence<Dafny.ISequence<int>>.Empty;
      this._clausesCount = 0;
      this._clauseLength = new int[0];
      this._truthAssignment = new int[0];
      this._trueLiteralsCount = new int[0];
      this._falseLiteralsCount = new int[0];
      this._positiveLiteralsToClauses = new Dafny.ISequence<int>[0];
      this._negativeLiteralsToClauses = new Dafny.ISequence<int>[0];
      this._decisionLevel = 0;
      this._traceVariable = new int[0];
      this._traceValue = new bool[0];
      this._traceDLStart = new int[0];
      this._traceDLEnd = new int[0];
    }
    public  int _variablesCount {get; set;}
    public int variablesCount {
      get {
        return this._variablesCount;
      }
      set {
        this._variablesCount = value;
      }
    }
    public  Dafny.ISequence<Dafny.ISequence<int>> _clauses {get; set;}
    public Dafny.ISequence<Dafny.ISequence<int>> clauses {
      get {
        return this._clauses;
      }
      set {
        this._clauses = value;
      }
    }
    public  int _clausesCount {get; set;}
    public int clausesCount {
      get {
        return this._clausesCount;
      }
      set {
        this._clausesCount = value;
      }
    }
    public  int[] _clauseLength {get; set;}
    public int[] clauseLength {
      get {
        return this._clauseLength;
      }
      set {
        this._clauseLength = value;
      }
    }
    public  int[] _truthAssignment {get; set;}
    public int[] truthAssignment {
      get {
        return this._truthAssignment;
      }
      set {
        this._truthAssignment = value;
      }
    }
    public  int[] _trueLiteralsCount {get; set;}
    public int[] trueLiteralsCount {
      get {
        return this._trueLiteralsCount;
      }
      set {
        this._trueLiteralsCount = value;
      }
    }
    public  int[] _falseLiteralsCount {get; set;}
    public int[] falseLiteralsCount {
      get {
        return this._falseLiteralsCount;
      }
      set {
        this._falseLiteralsCount = value;
      }
    }
    public  Dafny.ISequence<int>[] _positiveLiteralsToClauses {get; set;}
    public Dafny.ISequence<int>[] positiveLiteralsToClauses {
      get {
        return this._positiveLiteralsToClauses;
      }
      set {
        this._positiveLiteralsToClauses = value;
      }
    }
    public  Dafny.ISequence<int>[] _negativeLiteralsToClauses {get; set;}
    public Dafny.ISequence<int>[] negativeLiteralsToClauses {
      get {
        return this._negativeLiteralsToClauses;
      }
      set {
        this._negativeLiteralsToClauses = value;
      }
    }
    public  int _decisionLevel {get; set;}
    public int decisionLevel {
      get {
        return this._decisionLevel;
      }
      set {
        this._decisionLevel = value;
      }
    }
    public  int[] _traceVariable {get; set;}
    public int[] traceVariable {
      get {
        return this._traceVariable;
      }
      set {
        this._traceVariable = value;
      }
    }
    public  bool[] _traceValue {get; set;}
    public bool[] traceValue {
      get {
        return this._traceValue;
      }
      set {
        this._traceValue = value;
      }
    }
    public  int[] _traceDLStart {get; set;}
    public int[] traceDLStart {
      get {
        return this._traceDLStart;
      }
      set {
        this._traceDLStart = value;
      }
    }
    public  int[] _traceDLEnd {get; set;}
    public int[] traceDLEnd {
      get {
        return this._traceDLEnd;
      }
      set {
        this._traceDLEnd = value;
      }
    }
    public int getVariableFromLiteral(int literal) {
      return _Companion_DataStructures.getVariableFromLiteral(this, literal);
    }
    public _System._ITuple2<int, int> convertLVtoVI(int literal, bool @value)
    {
      return _Companion_DataStructures.convertLVtoVI(this, literal, @value);
    }
    public bool isUnitClause(int index) {
      return _Companion_DataStructures.isUnitClause(this, index);
    }
    public bool isEmptyClause(int index) {
      return _Companion_DataStructures.isEmptyClause(this, index);
    }
    public void __ctor(int variablesCount, Dafny.ISequence<Dafny.ISequence<int>> clauses)
    {
      (this)._variablesCount = variablesCount;
      (this)._clauses = clauses;
      (this)._decisionLevel = -1;
      int[] _nw5 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._traceVariable = _nw5;
      bool[] _nw6 = new bool[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._traceValue = _nw6;
      int[] _nw7 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._traceDLStart = _nw7;
      int[] _nw8 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._traceDLEnd = _nw8;
      int _49_clsLength;
      _49_clsLength = (int)(clauses).Count;
      (this)._clausesCount = _49_clsLength;
      int[] _nw9 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(_49_clsLength, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._clauseLength = _nw9;
      int[] _nw10 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(_49_clsLength, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._trueLiteralsCount = _nw10;
      int[] _nw11 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(_49_clsLength, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._falseLiteralsCount = _nw11;
      Dafny.ISequence<int>[] _nw12 = Dafny.ArrayHelpers.InitNewArray1<Dafny.ISequence<int>>(Dafny.Sequence<int>.Empty, Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"));
      (this)._positiveLiteralsToClauses = _nw12;
      Dafny.ISequence<int>[] _nw13 = Dafny.ArrayHelpers.InitNewArray1<Dafny.ISequence<int>>(Dafny.Sequence<int>.Empty, Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"));
      (this)._negativeLiteralsToClauses = _nw13;
      int[] _nw14 = new int[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(variablesCount, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      (this)._truthAssignment = _nw14;
      int _50_k;
      _50_k = 0;
      while ((_50_k) < (this.clausesCount)) {
        var _arr0 = this.clauseLength;
        _arr0[(int)((_50_k))] = (int)((this.clauses).Select(_50_k)).Count;
        _50_k = (_50_k) + (1);
      }
      int _51_index;
      _51_index = 0;
      while ((_51_index) < (variablesCount)) {
        var _arr1 = this.truthAssignment;
        _arr1[(int)((_51_index))] = -1;
        _51_index = (_51_index) + (1);
      }
      (this).createTFLArrays();
      (this).createPositiveLiteralsToClauses();
      (this).createNegativeLiteralsToClauses();
    }
    public void createTFLArrays()
    {
      int _52_i;
      _52_i = 0;
      while ((_52_i) < (this.clausesCount)) {
        var _arr2 = this.trueLiteralsCount;
        _arr2[(int)((_52_i))] = 0;
        var _arr3 = this.falseLiteralsCount;
        _arr3[(int)((_52_i))] = 0;
        _52_i = (_52_i) + (1);
      }
    }
    public void createPositiveLiteralsToClauses()
    {
      int _53_variable;
      _53_variable = 0;
      while ((_53_variable) < (this.variablesCount)) {
        var _arr4 = this.positiveLiteralsToClauses;
        _arr4[(int)((_53_variable))] = Dafny.Sequence<int>.FromElements();
        int _54_clauseIndex;
        _54_clauseIndex = 0;
        while ((_54_clauseIndex) < (this.clausesCount)) {
          if (((this.clauses).Select(_54_clauseIndex)).Contains(((_53_variable) + (1)))) {
            var _arr5 = this.positiveLiteralsToClauses;
            _arr5[(int)((_53_variable))] = Dafny.Sequence<int>.Concat((this.positiveLiteralsToClauses)[(int)(_53_variable)], Dafny.Sequence<int>.FromElements(_54_clauseIndex));
          }
          _54_clauseIndex = (_54_clauseIndex) + (1);
        }
        _53_variable = (_53_variable) + (1);
      }
    }
    public void createNegativeLiteralsToClauses()
    {
      int _55_variable;
      _55_variable = 0;
      while ((_55_variable) < (this.variablesCount)) {
        var _arr6 = this.negativeLiteralsToClauses;
        _arr6[(int)((_55_variable))] = Dafny.Sequence<int>.FromElements();
        int _56_clauseIndex;
        _56_clauseIndex = 0;
        while ((_56_clauseIndex) < (this.clausesCount)) {
          if (((this.clauses).Select(_56_clauseIndex)).Contains((((0) - (_55_variable)) - (1)))) {
            var _arr7 = this.negativeLiteralsToClauses;
            _arr7[(int)((_55_variable))] = Dafny.Sequence<int>.Concat((this.negativeLiteralsToClauses)[(int)(_55_variable)], Dafny.Sequence<int>.FromElements(_56_clauseIndex));
          }
          _56_clauseIndex = (_56_clauseIndex) + (1);
        }
        _55_variable = (_55_variable) + (1);
      }
    }
    public void revertLastDecisionLevel()
    {
      while (((this.traceDLStart)[(int)(this.decisionLevel)]) < ((this.traceDLEnd)[(int)(this.decisionLevel)])) {
        (this).removeLastVariable();
      }
      (this).decisionLevel = (this.decisionLevel) - (1);
    }
    public void removeLastVariable()
    {
      int _57_k;
      _57_k = ((this.traceDLEnd)[(int)(this.decisionLevel)]) - (1);
      int _58_variable;
      _58_variable = (this.traceVariable)[(int)(_57_k)];
      bool _59_value;
      _59_value = (this.traceValue)[(int)(_57_k)];
      var _arr8 = this.traceDLEnd;
      var _index1 = this.decisionLevel;
      _arr8[(int)(_index1)] = _57_k;
      var _arr9 = this.truthAssignment;
      _arr9[(int)((_58_variable))] = -1;
      Dafny.ISequence<int> _60_positivelyImpactedClauses;
      _60_positivelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_58_variable)];
      Dafny.ISequence<int> _61_negativelyImpactedClauses;
      _61_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_58_variable)];
      if (!(_59_value)) {
        _61_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_58_variable)];
        _60_positivelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_58_variable)];
      }
      int _62_i;
      _62_i = 0;
      int _63_len;
      _63_len = (int)(_60_positivelyImpactedClauses).Count;
      while ((_62_i) < (_63_len)) {
        int _64_clauseIndex;
        _64_clauseIndex = (_60_positivelyImpactedClauses).Select(_62_i);
        var _arr10 = this.trueLiteralsCount;
        _arr10[(int)((_64_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_64_clauseIndex)]) - (1);
        _62_i = (_62_i) + (1);
      }
      _62_i = 0;
      _63_len = (int)(_61_negativelyImpactedClauses).Count;
      {
        while ((_62_i) < (_63_len)) {
          int _65_clauseIndex;
          _65_clauseIndex = (_61_negativelyImpactedClauses).Select(_62_i);
          var _arr11 = this.falseLiteralsCount;
          _arr11[(int)((_65_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_65_clauseIndex)]) - (1);
          _62_i = (_62_i) + (1);
        }
      }
    }
    public void setVariable(int variable, bool @value)
    {
      (this).addAssignment(variable, @value);
      if (@value) {
        var _arr12 = this.truthAssignment;
        _arr12[(int)((variable))] = 1;
      } else {
        var _arr13 = this.truthAssignment;
        _arr13[(int)((variable))] = 0;
      }
      int _66_i;
      _66_i = 0;
      Dafny.ISequence<int> _67_impactedClauses;
      _67_impactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      Dafny.ISequence<int> _68_impactedClauses_k;
      _68_impactedClauses_k = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _67_impactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
        _68_impactedClauses_k = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      int _69_impactedClausesLen;
      _69_impactedClausesLen = (int)(_67_impactedClauses).Count;
      while ((_66_i) < (_69_impactedClausesLen)) {
        int _70_clauseIndex;
        _70_clauseIndex = (_67_impactedClauses).Select(_66_i);
        var _arr14 = this.trueLiteralsCount;
        _arr14[(int)((_70_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_70_clauseIndex)]) + (1);
        _66_i = (_66_i) + (1);
      }
      int _71_i_k;
      _71_i_k = 0;
      int _72_impactedClausesLen_k;
      _72_impactedClausesLen_k = (int)(_68_impactedClauses_k).Count;
      while ((_71_i_k) < (_72_impactedClausesLen_k)) {
        int _73_clauseIndex;
        _73_clauseIndex = (_68_impactedClauses_k).Select(_71_i_k);
        var _arr15 = this.falseLiteralsCount;
        _arr15[(int)((_73_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_73_clauseIndex)]) + (1);
        _71_i_k = (_71_i_k) + (1);
      }
    }
    public void addAssignment(int variable, bool @value)
    {
      var _arr16 = this.traceVariable;
      var _index2 = (this.traceDLEnd)[(int)(this.decisionLevel)];
      _arr16[(int)(_index2)] = variable;
      var _arr17 = this.traceValue;
      var _index3 = (this.traceDLEnd)[(int)(this.decisionLevel)];
      _arr17[(int)(_index3)] = @value;
      var _arr18 = this.traceDLEnd;
      var _index4 = this.decisionLevel;
      _arr18[(int)(_index4)] = ((this.traceDLEnd)[(int)(this.decisionLevel)]) + (1);
    }
    public void increaseDecisionLevel()
    {
      (this).decisionLevel = (this.decisionLevel) + (1);
      int _74_previous;
      _74_previous = 0;
      if ((this.decisionLevel) == (0)) {
        _74_previous = 0;
      } else {
        _74_previous = (this.traceDLEnd)[(int)((this.decisionLevel) - (1))];
      }
      var _arr19 = this.traceDLStart;
      var _index5 = this.decisionLevel;
      _arr19[(int)(_index5)] = _74_previous;
      var _arr20 = this.traceDLEnd;
      var _index6 = this.decisionLevel;
      _arr20[(int)(_index6)] = _74_previous;
    }
    public int extractUnsetLiteralFromClause(int clauseIndex)
    {
      int literal = 0;
      int _75_i;
      _75_i = 0;
      Dafny.ISequence<int> _76_clause;
      _76_clause = (this.clauses).Select(clauseIndex);
      while ((_75_i) < ((this.clauseLength)[(int)(clauseIndex)])) {
        if (((this.truthAssignment)[(int)((this).getVariableFromLiteral((_76_clause).Select(_75_i)))]) == (-1)) {
          literal = (_76_clause).Select(_75_i);
          return literal;
        }
        _75_i = (_75_i) + (1);
      }
      return literal;
    }
    public void propagate(int clauseIndex)
    {
      int _77_literal;
      int _out13;
      _out13 = (this).extractUnsetLiteralFromClause(clauseIndex);
      _77_literal = _out13;
      Dafny.ISequence<int> _78_clause;
      _78_clause = (this.clauses).Select(clauseIndex);
      (this).setLiteral(_77_literal, true);
    }
    public void unitPropagation(int variable, bool @value)
    {
      Dafny.ISequence<int> _79_negativelyImpactedClauses;
      _79_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _79_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      int _80_k;
      _80_k = 0;
      int _81_negativelyImpactedClausesLen;
      _81_negativelyImpactedClausesLen = (int)(_79_negativelyImpactedClauses).Count;
      while ((_80_k) < (_81_negativelyImpactedClausesLen)) {
        int _82_clauseIndex;
        _82_clauseIndex = (_79_negativelyImpactedClauses).Select(_80_k);
        if (((this.falseLiteralsCount)[(int)(_82_clauseIndex)]) < ((this.clauseLength)[(int)(_82_clauseIndex)])) {
          if ((((this.trueLiteralsCount)[(int)(_82_clauseIndex)]) == (0)) && ((((this.falseLiteralsCount)[(int)(_82_clauseIndex)]) + (1)) == ((this.clauseLength)[(int)(_82_clauseIndex)]))) {
            (this).propagate(_82_clauseIndex);
          }
        }
        _80_k = (_80_k) + (1);
      }
    }
    public void setLiteral(int literal, bool @value)
    {
      int _83_variable;
      _83_variable = (this).getVariableFromLiteral(literal);
      bool _84_value_k;
      _84_value_k = (((literal) > (0)) ? (@value) : (!(@value)));
      (this).setVariable(_83_variable, _84_value_k);
      (this).unitPropagation(_83_variable, _84_value_k);
    }
    public int chooseLiteral()
    {
      int x = 0;
      int _85_minim;
      _85_minim = Int32_Compile.__default.max;
      int _86_counter;
      _86_counter = 0;
      int _87_result;
      _87_result = -1;
      bool _88_ok;
      _88_ok = false;
      int _89_cI;
      _89_cI = 0;
      while ((_89_cI) < (this.clausesCount)) {
        int _90_diff;
        _90_diff = ((this.clauseLength)[(int)(_89_cI)]) - ((this.falseLiteralsCount)[(int)(_89_cI)]);
        if ((((this.trueLiteralsCount)[(int)(_89_cI)]) == (0)) && ((_90_diff) < (_85_minim))) {
          _85_minim = _90_diff;
        }
        if ((((this.trueLiteralsCount)[(int)(_89_cI)]) == (0)) && ((_90_diff) == (_85_minim))) {
          int _91_lI;
          _91_lI = 0;
          while ((_91_lI) < ((this.clauseLength)[(int)(_89_cI)])) {
            int _92_variable;
            _92_variable = (this).getVariableFromLiteral(((this.clauses).Select(_89_cI)).Select(_91_lI));
            if (((this.truthAssignment)[(int)(_92_variable)]) == (-1)) {
              _88_ok = true;
              if ((_86_counter) == (0)) {
                _87_result = (_92_variable) + (1);
                _86_counter = (_86_counter) + (1);
              } else if ((_87_result) == ((_92_variable) + (1))) {
                _86_counter = (_86_counter) + (1);
              } else {
                _86_counter = (_86_counter) - (1);
              }
            }
            _91_lI = (_91_lI) + (1);
          }
        }
        _89_cI = (_89_cI) + (1);
      }
      x = (0) - (_87_result);
      return x;
      return x;
    }
    public bool getHasEmptyClause()
    {
      bool ok = false;
      int _93_k;
      _93_k = 0;
      while ((_93_k) < (this.clausesCount)) {
        if (((this.falseLiteralsCount)[(int)(_93_k)]) == ((this.clauseLength)[(int)(_93_k)])) {
          ok = true;
          return ok;
        }
        _93_k = (_93_k) + (1);
      }
      ok = false;
      return ok;
      return ok;
    }
    public bool getIsEmpty()
    {
      bool ok = false;
      int _94_k;
      _94_k = 0;
      while ((_94_k) < (this.clausesCount)) {
        if (((this.trueLiteralsCount)[(int)(_94_k)]) == (0)) {
          ok = false;
          return ok;
        }
        _94_k = (_94_k) + (1);
      }
      ok = true;
      return ok;
      return ok;
    }
    public void level0UnitPropagation()
    {
      int _95_i;
      _95_i = 0;
      (this).increaseDecisionLevel();
      while ((_95_i) < (this.clausesCount)) {
        if ((((this.trueLiteralsCount)[(int)(_95_i)]) == (0)) && ((((this.falseLiteralsCount)[(int)(_95_i)]) + (1)) == ((this.clauseLength)[(int)(_95_i)]))) {
          (this).propagate(_95_i);
        }
        _95_i = (_95_i) + (1);
      }
      if (((this.traceDLStart)[(int)(this.decisionLevel)]) == ((this.traceDLEnd)[(int)(this.decisionLevel)])) {
        (this).revertLastDecisionLevel();
      }
    }
  }

  public interface DataStructures {
    int variablesCount { get; set; }
    Dafny.ISequence<Dafny.ISequence<int>> clauses { get; set; }
    int clausesCount { get; set; }
    int[] clauseLength { get; set; }
    int[] truthAssignment { get; set; }
    int[] trueLiteralsCount { get; set; }
    int[] falseLiteralsCount { get; set; }
    Dafny.ISequence<int>[] positiveLiteralsToClauses { get; set; }
    Dafny.ISequence<int>[] negativeLiteralsToClauses { get; set; }
    int decisionLevel { get; set; }
    int[] traceVariable { get; set; }
    bool[] traceValue { get; set; }
    int[] traceDLStart { get; set; }
    int[] traceDLEnd { get; set; }
    int getVariableFromLiteral(int literal);
    _System._ITuple2<int, int> convertLVtoVI(int literal, bool @value);
    bool isUnitClause(int index);
    bool isEmptyClause(int index);
  }
  public class _Companion_DataStructures {
    public static int getVariableFromLiteral(DataStructures _this, int literal) {
      return (Utils_Compile.__default.abs(literal)) - (1);
    }
    public static _System._ITuple2<int, int> convertLVtoVI(DataStructures _this, int literal, bool @value)
    {
      int _96_variable = (_this).getVariableFromLiteral(literal);
      int _97_v = ((@value) ? (1) : (0));
      int _98_val = (((literal) < (0)) ? ((1) - (_97_v)) : (_97_v));
      return _System.Tuple2<int, int>.create(_96_variable, _98_val);
    }
    public static bool isUnitClause(DataStructures _this, int index) {
      return (((_this.trueLiteralsCount)[(int)(index)]) == (0)) && ((((_this.clauseLength)[(int)(index)]) - ((_this.falseLiteralsCount)[(int)(index)])) == (1));
    }
    public static bool isEmptyClause(DataStructures _this, int index) {
      return ((_this.clauseLength)[(int)(index)]) == ((_this.falseLiteralsCount)[(int)(index)]);
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(_module.__default._Main);
  }
}
