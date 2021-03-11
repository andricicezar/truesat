// Dafny program truesat.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.3.0.10506
// Command Line Options: /trace /vcsCores 1 /errorLimit 5 /proc ** /compileTarget:cs /spillTargetCode:1 /compile:2 truesat.dfy file_input.cs
// truesat.dfy

method Main()
{
  var starttime := Input.getTimestamp();
  var input := Input.getInput();
  var totalTime: real := (Input.getTimestamp() - starttime) as real / 1000.0;
  print ""c Time to read: "", totalTime, ""s\n"";
  match input {
    case Error(m) =>
      print ""c Error: "", m, ""\n"";
    case Just(z) =>
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
        case SAT(x) =>
          print ""s SATISFIABLE\n"";
        case UNSAT =>
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
    ensures old(formula.decisionLevel) == formula.decisionLevel
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace
    ensures forall i: Int32.t :: 0 <= i <= formula.decisionLevel ==> old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i)
    ensures formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
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

  import Int32 = Int32

  import opened Useless = Useless

  import FileInput = FileInput

  import opened MyDatatypes = MyDatatypes

  import InputPredicate = InputPredicate
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

  import Int32 = Int32
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

  lemma /*{:_induction cI}*/ inputPredicate_countLiterals(cI: Int32.t)
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
    i := 0;
    len := |negativelyImpactedClauses| as Int32.t;
    while i < len
      invariant 0 <= i <= len
      invariant forall i': Int32.t :: 0 <= i' < i ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(newTau, clauses[negativelyImpactedClauses[i']])
      invariant forall i': Int32.t :: i <= i' < len ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(previousTau, clauses[negativelyImpactedClauses[i']])
      invariant forall i': Int32.t :: 0 <= i' < clausesCount && i' !in negativelyImpactedClauses ==> falseLiteralsCount[i'] == countFalseLiterals(newTau, clauses[i'])
      decreases len - i
      modifies falseLiteralsCount
    {
      var clauseIndex := negativelyImpactedClauses[i];
      unsetVariable_countFalseLiteralsDecreasesWithOne(previousTau, newTau, variable, clauses[clauseIndex]);
      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
      i := i + 1;
    }
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
    assert validFalseLiteralsCount(truthAssignment[..]);
    variableSet_countUnsetVariablesLessThanLength(newTau, variable);
    setVariable_unsetVariablesDecreasesWithOne(oldTau, newTau, variable);
  }

  lemma traceFull_variableInTrace(variable: Int32.t)
    requires valid()
    requires validVariable(variable)
    requires 0 <= decisionLevel
    requires traceDLEnd[decisionLevel] == variablesCount
    ensures exists i: Int32.t :: 0 <= i < traceDLEnd[decisionLevel] && traceVariable[i] == variable
    decreases variable
  {
  }

  lemma existsUnsetLiteral_traceNotFull(variable: Int32.t)
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

  lemma forall_validAssignmentTrace_traceDLStartStrictlyOrdered()
    requires 0 <= decisionLevel
    requires decisionLevel as int < traceDLStart.Length
    requires decisionLevel as int < traceDLEnd.Length
    ensures validVariablesCount() && validAssignmentTrace() ==> forall i: Int32.t, j: Int32.t :: 0 <= i < j <= decisionLevel ==> traceDLStart[i] < traceDLStart[j]
  {
  }

  lemma validAssignmentTrace_traceDLStartStrictlyOrdered(i: Int32.t, j: Int32.t)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= i < j <= decisionLevel
    ensures traceDLStart[i] < traceDLStart[j]
    decreases decisionLevel - i
  {
  }

  lemma forall_validAssignmentTrace_traceDLEndStrictlyOrdered()
    requires 0 <= decisionLevel
    requires decisionLevel as int < traceDLStart.Length
    requires decisionLevel as int < traceDLEnd.Length
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures validVariablesCount() && validAssignmentTrace() ==> forall i: Int32.t :: 0 <= i < decisionLevel ==> traceDLEnd[i] < traceDLEnd[decisionLevel]
  {
  }

  lemma validAssignmentTrace_traceDLEndStrictlyOrdered(i: Int32.t)
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
    var (v', val') := convertLVtoVI(literal, true);

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
    var (vari, val) := convertLVtoVI(literal, value);

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

  lemma maybeClause_existUnsetLiteralInClause(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= clauseIndex < clausesCount
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    ensures exists j': Int32.t :: 0 <= j' < clauseLength[clauseIndex] && validLiteral(clauses[clauseIndex][j']) && truthAssignment[getVariableFromLiteral(clauses[clauseIndex][j'])] == -1
    decreases clauseIndex
  {
  }

  lemma notEmptyNoEmptyClauses_existUnsetLiteralInClauses()
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
      var i: Int32.t :| 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i];
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
      var i: Int32.t :| 0 <= i < clausesCount && trueLiteralsCount[i] == 0;
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

  lemma notEmptyNoEmptyClauses_traceNotFull()
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

  lemma ifFull_containsAllVariables()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    requires decisionLevel == variablesCount - 1
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures forall v: Int32.t :: 0 <= v < variablesCount ==> occursInTrace(v)
    ensures forall v: Int32.t :: 0 <= v < variablesCount ==> occursInAssignmentsTrace(v)
  {
  }

  lemma allVariablesSet_done()
    requires valid()
    requires forall v: Int32.t :: validVariable(v) ==> isVariableSet(truthAssignment[..], v)
    ensures hasEmptyClause() || isEmpty()
  {
  }

  lemma tauFullClauseNotEmpty_clauseIsSatisfied(cI: int)
    requires valid()
    requires 0 <= cI < |clauses|
    requires validClause(clauses[cI])
    requires forall x: Int32.t :: x in clauses[cI] ==> isVariableSet(truthAssignment[..], getVariableFromLiteral(x))
    requires falseLiteralsCount[cI] as int < |clauses[cI]|
    ensures trueLiteralsCount[cI] > 0
    decreases cI
  {
  }

  lemma /*{:_induction clause, truthAssignment}*/ existsTrueLiteral_countTrueLiteralsPositive(clause: seq<Int32.t>, truthAssignment: seq<Int32.t>)
    requires valid()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires exists x: Int32.t :: x in clause && getLiteralValue(truthAssignment, x) == 1
    ensures countTrueLiterals(truthAssignment, clause) > 0
    decreases clause, truthAssignment
  {
  }

  lemma unitClause_existsUnsetLiteral(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    ensures exists literal: Int32.t :: literal in clauses[clauseIndex] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases clauseIndex
  {
  }

  lemma hasEmptyClause_notSatisfiable()
    requires valid()
    requires hasEmptyClause()
    ensures !isSatisfiableExtend(truthAssignment[..])
  {
  }

  lemma allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex: Int32.t)
    requires valid()
    requires 0 <= clauseIndex as int < |clauses|
    requires falseLiteralsCount[clauseIndex] as int == |clauses[clauseIndex]|
    requires validClause(clauses[clauseIndex])
    ensures forall literal: Int32.t :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment[..], literal) == 0
    decreases clauseIndex
  {
  }

  lemma isEmpty_sastisfied()
    requires valid()
    requires !hasEmptyClause()
    requires isEmpty()
    ensures isSatisfiableExtend(truthAssignment[..])
  {
  }

  lemma partialTauSatisfied_isSatisfiableExtend(tau: seq<Int32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClauses()
    requires isSatisfied(tau)
    ensures isSatisfiableExtend(tau)
    decreases countUnsetVariables(tau)
  {
  }

  lemma unitClause_allFalseExceptLiteral(truthAssignment: seq<Int32.t>, clauseIndex: Int32.t, literal: Int32.t)
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

  lemma unitClauseLiteralFalse_tauNotSatisfiable(truthAssignment: seq<Int32.t>, clauseIndex: Int32.t, literal: Int32.t)
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

  lemma /*{:_induction tau}*/ variableSet_countUnsetVariablesLessThanLength(tau: seq<Int32.t>, variable: Int32.t)
    requires |tau| <= Int32.max as int
    requires 0 <= variable as int < |tau|
    requires tau[variable] in [0, 1]
    ensures countUnsetVariables(tau) as int < |tau|
    decreases tau, variable
  {
  }

  lemma /*{:_induction tau, clause}*/ unsetVariable_countTrueLiteralsLessThanLength(tau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma /*{:_induction tau, clause}*/ unsetVariable_countFalseLiteralsLessThanLength(tau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma forVariableNotSatisfiableExtend_notSatisfiableExtend(tau: seq<Int32.t>, variable: Int32.t)
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

  lemma extensionSatisfiable_baseSatisfiable(tau: seq<Int32.t>, variable: Int32.t, value: Int32.t)
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

  import opened MyDatatypes = MyDatatypes

  import Int32 = Int32

  import InputPredicate = InputPredicate
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
        decreases contentLength as int - cursor as int
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
        decreases contentLength as int - cursor as int
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
            case Error(t) =>
              {
                return Error(t);
              }
            case Just(number) =>
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
            case Error(t) =>
              {
                return Error(t);
              }
            case Just(number) =>
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
            case Error(t) =>
              {
                return Error(t);
              }
            case Just(number) =>
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
    var variable: Int32.t := Utils.abs(literal) - 1;
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
      var ok: Int32.t := if truthAssignment[0] == -1 then 1 else 0; ok + countUnsetVariables(truthAssignment[1..])
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
      var ok: Int32.t := if getLiteralValue(truthAssignment, clause[0]) == 1 then 1 else 0; ok + countTrueLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction truthAssignment, clause}*/ prop_countTrueLiterals_initialTruthAssignment(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countTrueLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
  }

  lemma /*{:_induction truthAssignment, clause}*/ countTrueLiterals0_noLiteralsTrue(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) == 0
    ensures forall literal: Int32.t :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1
    decreases truthAssignment, clause
  {
  }

  lemma /*{:_induction truthAssignment, clause}*/ countTrueLiteralsX_existsTrueLiteral(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
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
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauseLength, clauseLength
    ensures 0 <= countFalseLiterals(truthAssignment, clause) as int <= |clause|
    decreases {this, this, clauseLength}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      var ok: Int32.t := if getLiteralValue(truthAssignment, clause[0]) == 0 then 1 else 0; ok + countFalseLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction truthAssignment, clause}*/ prop_countFalseLiterals_initialTruthAssignment(truthAssignment: seq<Int32.t>, clause: seq<Int32.t>)
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

  lemma /*{:_induction cI}*/ countLiterals_monotone(cI: Int32.t)
    requires validVariablesCount()
    requires validClauses()
    requires countLiterals(clausesCount) < Int32.max as int
    requires 0 <= cI <= clausesCount
    ensures 0 <= cI < clausesCount ==> countLiterals(cI) < countLiterals(cI + 1) < Int32.max as int
    decreases clausesCount - cI
  {
  }

  lemma /*{:_induction oldTau, newTau}*/ clausesNotImpacted_TFArraysSame(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, impactedClauses: seq<Int32.t>, impactedClauses': seq<Int32.t>)
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

  lemma /*{:_induction oldTau, newTau, clause}*/ setVariable_countTrueLiteralsIncreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma /*{:_induction oldTau, newTau, clause}*/ setVariable_countFalseLiteralsIncreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma /*{:_induction oldTau, clause}*/ literalTrue_countTrueLiteralsAtLeastOne(oldTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma /*{:_induction oldTau, newTau, clause}*/ unsetVariable_countTrueLiteralsDecreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma /*{:_induction oldTau, newTau, clause}*/ unsetVariable_countFalseLiteralsDecreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, clause: seq<Int32.t>)
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

  lemma /*{:_induction oldTau, newTau}*/ undoImpactedClauses_TFSArraysModified(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t, impactedClauses: seq<Int32.t>, impactedClauses': seq<Int32.t>)
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

  lemma notDone_literalsToSet(i: Int32.t)
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

  lemma /*{:_induction oldTau, newTau}*/ setVariable_unsetVariablesDecreasesWithOne(oldTau: seq<Int32.t>, newTau: seq<Int32.t>, variable: Int32.t)
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
    ensures var tau': seq<Int32.t> := getExtendedCompleteTau(tau); validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau')
    decreases {this, this, this, this, clauseLength}, tau
  {
    var tau': seq<Int32.t> :| validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau');
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

  import Int32 = Int32
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

namespace Dafny
{
  using System.Collections.Generic;
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
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
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
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
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Count {
      get { return this.setImpl.Count; }
    }
    public long LongCount {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
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
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Count < other.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, int> dict;
#else
    readonly Dictionary<T, int> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, int>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, int> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, int>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = 1;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
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
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      } else if (t is T && dict.ContainsKey((T)(object)t)) {
        return dict[(T)(object)t];
      } else {
        return BigInteger.Zero;
      }
    }
    public MultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = dict;
#endif
        return new MultiSet<T>(r, i);
      } else {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = new Dictionary<T, int>(dict);
#endif
        r[(T)(object)t] = (int)i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

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
          for (int i = 0; i < item.Value; i++) {
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
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Count);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Count {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !Dafny.Helpers.AreEqual(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!Dafny.Helpers.AreEqual(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
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
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public Set<U> Keys {
      get {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values {
      get {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<_System.Tuple2<U, V>> Items {
      get {
        HashSet<_System.Tuple2<U, V>> result = new HashSet<_System.Tuple2<U, V>>();
        if (hasNullValue) {
          result.Add(_System.Tuple2<U, V>.create(default(U), nullValue));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(_System.Tuple2<U, V>.create(kvp.Key, kvp.Value));
        }
        return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
      }
    }
  }

  public class Sequence<T>
  {
    readonly T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Count {
      get { return elmts.Length; }
    }
    public long LongCount {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
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
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!Dafny.Helpers.AreEqual(elmts[i], other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (Dafny.Helpers.AreEqual(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static bool AreEqual<G>(G a, G b) {
      return a == null ? b == null : a.Equals(b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
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
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    // Computing forall/exists quantifiers
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
      for (var j = new BigInteger(1);; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
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
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
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

  public struct BigRational
  {
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
}

namespace @_System
{
  public class Tuple2<T0,T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@Tuple2<T0,T1>;
      return oth != null && Dafny.Helpers.AreEqual(this._0, oth._0) && Dafny.Helpers.AreEqual(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
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
    static Tuple2<T0,T1> theDefault;
    public static Tuple2<T0,T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@Tuple2<T0,T1>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>());
        }
        return theDefault;
      }
    }
    public static Tuple2<T0,T1> _DafnyDefaultValue() { return Default; }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake3 { get { return true; } }
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
      for (int i0 = 0; i0 < s0; i0++)
        a[i0] = z;
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
  }








  public class Tuple0 {
    public Tuple0() {
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
    static Tuple0 theDefault;
    public static Tuple0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple0();
        }
        return theDefault;
      }
    }
    public static Tuple0 _DafnyDefaultValue() { return Default; }
    public static Tuple0 create() {
      return new Tuple0();
    }
    public bool is____hMake0 { get { return true; } }
    public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace _0_Int32_Compile {

  public partial class t {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public partial class __default {
    public static int max { get {
      return 2000000;
    } }
    public static int min { get {
      return (0) - (2000000);
    } }
  }
} // end of namespace _0_Int32_Compile
namespace _2_MyDatatypes_Compile {

  public abstract class Maybe<T> {
    public Maybe() { }
    static Maybe<T> theDefault;
    public static Maybe<T> Default {
      get {
        if (theDefault == null) {
          theDefault = new _2_MyDatatypes_Compile.Maybe_Error<T>(Dafny.Sequence<char>.Empty);
        }
        return theDefault;
      }
    }
    public static Maybe<T> _DafnyDefaultValue() { return Default; }
    public static Maybe<T> create_Error(Dafny.Sequence<char> _a0) {
      return new Maybe_Error<T>(_a0);
    }
    public static Maybe<T> create_Just(T @value) {
      return new Maybe_Just<T>(@value);
    }
    public bool is_Error { get { return this is Maybe_Error<T>; } }
    public bool is_Just { get { return this is Maybe_Just<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Maybe_Just<T>)d).@value; 
      }
    }
  }
  public class Maybe_Error<T> : Maybe<T> {
    public readonly Dafny.Sequence<char> _a0;
    public Maybe_Error(Dafny.Sequence<char> _a0) {
      this._a0 = _a0;
    }
    public override bool Equals(object other) {
      var oth = other as _2_MyDatatypes_Compile.Maybe_Error<T>;
      return oth != null && Dafny.Helpers.AreEqual(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_MyDatatypes_Compile.Maybe.Error";
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
    public override bool Equals(object other) {
      var oth = other as _2_MyDatatypes_Compile.Maybe_Just<T>;
      return oth != null && Dafny.Helpers.AreEqual(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_MyDatatypes_Compile.Maybe.Just";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

} // end of namespace _2_MyDatatypes_Compile
namespace _6_InputPredicate_Compile {


} // end of namespace _6_InputPredicate_Compile
namespace _8_Useless_Compile {




  public partial class Parser {
    public char[] content = new char[0];
    public int contentLength = 0;
    public int cursor = 0;
    public void __ctor(char[] c)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).content = c;
      (_this).contentLength = (int)(c).Length;
      (_this).cursor = 0;
    }
    public void skipLine()
    {
      var _this = this;
    TAIL_CALL_START: ;
      while (((_this.cursor) < (_this.contentLength)) && (((_this.content)[(int)(_this.cursor)]) != ('\n'))) {
        (_this).cursor = (_this.cursor) + (1);
      }
      if ((_this.cursor) < (_this.contentLength)) {
        (_this).cursor = (_this.cursor) + (1);
      }
    }
    public void toNextNumber()
    {
      var _this = this;
    TAIL_CALL_START: ;
      while (((_this.cursor) < (_this.contentLength)) && (!(((('0') <= ((_this.content)[(int)(_this.cursor)])) && (((_this.content)[(int)(_this.cursor)]) <= ('9'))) || (((_this.content)[(int)(_this.cursor)]) == ('-'))))) {
        (_this).cursor = (_this.cursor) + (1);
      }
    }
    public void extractNumber(out _2_MyDatatypes_Compile.Maybe<int> res)
    {
      var _this = this;
    TAIL_CALL_START: ;
      res = _2_MyDatatypes_Compile.Maybe<int>.Default;
      int _282_number;
      _282_number = 0;
      bool _283_isNegative;
      _283_isNegative = false;
      if (((_this.cursor) < (_this.contentLength)) && (((_this.content)[(int)(_this.cursor)]) == ('-'))) {
        _283_isNegative = true;
        (_this).cursor = (_this.cursor) + (1);
      }
      if ((_this.cursor) == (_this.contentLength)) {
        res = @_2_MyDatatypes_Compile.Maybe<int>.create_Error(Dafny.Sequence<char>.FromString("There is no number around here."));
        return;
      }
      while (((_this.cursor) < (_this.contentLength)) && ((('0') <= ((_this.content)[(int)(_this.cursor)])) && (((_this.content)[(int)(_this.cursor)]) <= ('9')))) {
        int _284_digit;
        _284_digit = ((int)((_this.content)[(int)(_this.cursor)])) - ((int)('0'));
        if ((_282_number) <= (Dafny.Helpers.EuclideanDivision_int((_0_Int32_Compile.__default.max) - (_284_digit), 10))) {
          { }
          _282_number = ((_282_number) * (10)) + (_284_digit);
        } else {
          res = @_2_MyDatatypes_Compile.Maybe<int>.create_Error(Dafny.Sequence<char>.FromString("There is a number bigger than Int32.max"));
          return;
        }
        (_this).cursor = (_this.cursor) + (1);
      }
      if (_283_isNegative) {
        _282_number = (0) - (_282_number);
      }
      res = @_2_MyDatatypes_Compile.Maybe<int>.create_Just(_282_number);
      return;
    }
    public void parse(out _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> result)
    {
      var _this = this;
    TAIL_CALL_START: ;
      result = _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.Default;
      int _285_variablesCount;
      _285_variablesCount = 0;
      int _286_clausesCount;
      _286_clausesCount = 0;
      Dafny.Sequence<Dafny.Sequence<int>> _287_clauses;
      _287_clauses = Dafny.Sequence<Dafny.Sequence<int>>.FromElements();
      int[] _288_clause;
      var _nw0 = new int[(int)(new BigInteger(1000))];
      _288_clause = _nw0;
      int _289_clauseLength;
      _289_clauseLength = 0;
      bool _290_ok;
      _290_ok = false;
      int _291_literalsCount;
      _291_literalsCount = 0;
      int _292_contentLength;
      _292_contentLength = (int)(_this.content).Length;
      while ((_this.cursor) < (_292_contentLength)) {
        int _293_oldCursor;
        _293_oldCursor = _this.cursor;
        if (((_this.content)[(int)(_this.cursor)]) == ('c')) {
          (_this).skipLine();
        } else if ((((_this.content)[(int)(_this.cursor)]) == ('p')) && ((_285_variablesCount) == (0))) {
          (_this).toNextNumber();
          _2_MyDatatypes_Compile.Maybe<int> _294_x;
          _2_MyDatatypes_Compile.Maybe<int> _out0;
          (_this).extractNumber(out _out0);
          _294_x = _out0;
          _2_MyDatatypes_Compile.Maybe<int> _source0 = _294_x;
          if (_source0.is_Error) {
            Dafny.Sequence<char> _295_t = ((_2_MyDatatypes_Compile.Maybe_Error<int>)_source0)._a0;
            {
              result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(_295_t);
              return;
            }
          } else  {
            int _296_number = ((_2_MyDatatypes_Compile.Maybe_Just<int>)_source0).@value;
            {
              if (((0) < (_296_number)) && ((_296_number) < (_0_Int32_Compile.__default.max))) {
                _285_variablesCount = _296_number;
                _290_ok = true;
              } else {
                result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("Variables count is bigger than Int32.max"));
                return;
              }
            }
          }
          (_this).toNextNumber();
          _2_MyDatatypes_Compile.Maybe<int> _out1;
          (_this).extractNumber(out _out1);
          _294_x = _out1;
_2_MyDatatypes_Compile.Maybe<int> _source1 = _294_x;
          if (_source1.is_Error) {
            Dafny.Sequence<char> _297_t = ((_2_MyDatatypes_Compile.Maybe_Error<int>)_source1)._a0;
            {
              result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(_297_t);
              return;
            }
          } else  {
            int _298_number = ((_2_MyDatatypes_Compile.Maybe_Just<int>)_source1).@value;
            {
              _286_clausesCount = _298_number;
            }
          }
          (_this).skipLine();
        } else if (((_this.content)[(int)(_this.cursor)]) == ('p')) {
          result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("Twice p? what are you doing?"));
          return;
        } else if (_290_ok) {
          (_this).toNextNumber();
          if (((_289_clauseLength) == (0)) && ((_this.cursor) == (_292_contentLength))) {
            goto after_0;
          }
          _2_MyDatatypes_Compile.Maybe<int> _299_x;
          _2_MyDatatypes_Compile.Maybe<int> _out2;
          (_this).extractNumber(out _out2);
          _299_x = _out2;
          _2_MyDatatypes_Compile.Maybe<int> _source2 = _299_x;
          if (_source2.is_Error) {
            Dafny.Sequence<char> _300_t = ((_2_MyDatatypes_Compile.Maybe_Error<int>)_source2)._a0;
            {
              result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(_300_t);
              return;
            }
          } else  {
            int _301_number = ((_2_MyDatatypes_Compile.Maybe_Just<int>)_source2).@value;
            {
              if (((_301_number) == (0)) && ((_289_clauseLength) > (0))) {
                _287_clauses = (_287_clauses).Concat(Dafny.Sequence<Dafny.Sequence<int>>.FromElements(Dafny.Helpers.SeqFromArray(_288_clause).Take(_289_clauseLength)));
                if (((_0_Int32_Compile.__default.max) - (_289_clauseLength)) > (_291_literalsCount)) {
                  _291_literalsCount = (_291_literalsCount) + (_289_clauseLength);
                } else {
                  result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("The number of literals is to big"));
                  return;
                }
                _289_clauseLength = 0;
              } else if ((_301_number) != (0)) {
                if ((_289_clauseLength) < (1000)) {
                  if ((((_301_number) < (0)) && (((0) < ((0) - (_301_number))) && (((0) - (_301_number)) <= (_285_variablesCount)))) || (((_301_number) > (0)) && (((0) < (_301_number)) && ((_301_number) <= (_285_variablesCount))))) {
                    (_288_clause)[(int)((_289_clauseLength))] = _301_number;
                    _289_clauseLength = (_289_clauseLength) + (1);
                    int _302_k;
                    _302_k = (_289_clauseLength) - (1);
                    while (((0) < (_302_k)) && (((_288_clause)[(int)((_302_k) - (1))]) > ((_288_clause)[(int)(_302_k)]))) {
                      int _303_aux;
                      _303_aux = (_288_clause)[(int)(_302_k)];
                      (_288_clause)[(int)((_302_k))] = (_288_clause)[(int)((_302_k) - (1))];
                      var _index0 = (_302_k) - (1);
                      (_288_clause)[(int)(_index0)] = _303_aux;
                      _302_k = (_302_k) - (1);
                    }
                    if (((_302_k) > (0)) && (((_288_clause)[(int)((_302_k) - (1))]) == ((_288_clause)[(int)(_302_k)]))) {
                      result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("duplice literal in clause"));
                      return;
                    }
                  } else {
                    result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("literal bigger than variablesCount"));
                    return;
                  }
                } else {
                  result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("clause longer than 1000"));
                  return;
                }
              }
            }
          }
        }
        if (((_this.cursor) < (_292_contentLength)) && ((_293_oldCursor) == (_this.cursor))) {
          (_this).cursor = (_this.cursor) + (1);
        }
      }
    after_0: ;
      if (!(((new BigInteger(0)) < (new BigInteger((_287_clauses).Count))) && ((new BigInteger((_287_clauses).Count)) < (new BigInteger(_0_Int32_Compile.__default.max))))) {
        result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("number of clauses incorrect"));
        return;
      }
      if ((new BigInteger((_287_clauses).Count)) != (new BigInteger(_286_clausesCount))) {
        result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("different number of clauses"));
        return;
      }
      if (_290_ok) {
        result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Just(@_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>.create(_285_variablesCount, _287_clauses));
        return;
      } else {
        result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("p not found"));
        return;
      }
    }
  }

} // end of namespace _8_Useless_Compile
namespace FileInput {

  public partial class Reader {
  }

} // end of namespace FileInput
namespace _14_Input_Compile {






  public partial class __default {
    public static void getInput(out _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> result)
    {
    TAIL_CALL_START: ;
      result = _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.Default;
      char[] _304_input;
      _304_input = FileInput.Reader.getContent();
      if (((new BigInteger(0)) < (new BigInteger((_304_input).Length))) && ((new BigInteger((_304_input).Length)) < (new BigInteger(_0_Int32_Compile.__default.max)))) {
        _8_Useless_Compile.Parser _305_parser;
        var _nw1 = new _8_Useless_Compile.Parser();
        _nw1.__ctor(_304_input);
        _305_parser = _nw1;
        _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> _306_x;
        _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> _out3;
        (_305_parser).parse(out _out3);
        _306_x = _out3;
        result = _306_x;
        return;
      } else {
        result = @_2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("the file contains more data than Int32.max"));
        return;
      }
    }
    public static BigInteger getTimestamp() {
      return FileInput.Reader.getTimestamp();
    }
  }
} // end of namespace _14_Input_Compile
namespace _16_Utils_Compile {


  public partial class __default {
    public static void newInitializedSeq(int n, int d, out int[] r)
    {
    TAIL_CALL_START: ;
      r = new int[0];
      var _nw2 = new int[(int)(n)];
      r = _nw2;
      int _307_index;
      _307_index = 0;
      while ((_307_index) < (n)) {
        (r)[(int)((_307_index))] = d;
        _307_index = (_307_index) + (1);
      }
    }
    public static int abs(int literal) {
      if ((literal) < (0)) {
        return (0) - (literal);
      } else  {
        return literal;
      }
    }
  }
} // end of namespace _16_Utils_Compile
namespace _module {

  public partial class __default {
    public static void Main()
    {
    TAIL_CALL_START: ;
      BigInteger _308_starttime;
      _308_starttime = _14_Input_Compile.__default.getTimestamp();
      _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> _309_input;
      _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> _out4;
      _14_Input_Compile.__default.getInput(out _out4);
      _309_input = _out4;
      Dafny.BigRational _310_totalTime;
      _310_totalTime = (new Dafny.BigRational(((_14_Input_Compile.__default.getTimestamp()) - (_308_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Time to read: "));
      Dafny.Helpers.Print(_310_totalTime);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
      _2_MyDatatypes_Compile.Maybe<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>> _source3 = _309_input;
      if (_source3.is_Error) {
        Dafny.Sequence<char> _311_m = ((_2_MyDatatypes_Compile.Maybe_Error<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>)_source3)._a0;
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Error: "));
        Dafny.Helpers.Print(_311_m);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      } else  {
        _System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>> _312_z = ((_2_MyDatatypes_Compile.Maybe_Just<_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>>)_source3).@value;
        _System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>> _let_tmp_rhs0 = _312_z;
        int _313_variablesCount = ((_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>)_let_tmp_rhs0)._0;
        Dafny.Sequence<Dafny.Sequence<int>> _314_clauses = ((_System.Tuple2<int,Dafny.Sequence<Dafny.Sequence<int>>>)_let_tmp_rhs0)._1;
        _308_starttime = _14_Input_Compile.__default.getTimestamp();
        Formula _315_formula;
        var _nw3 = new Formula();
        _nw3.__ctor(_313_variablesCount, _314_clauses);
        _315_formula = _nw3;
        SATSolver _316_solver;
        var _nw4 = new SATSolver();
        _nw4.__ctor(_315_formula);
        _316_solver = _nw4;
        _310_totalTime = (new Dafny.BigRational(((_14_Input_Compile.__default.getTimestamp()) - (_308_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Time to initialize: "));
        Dafny.Helpers.Print(_310_totalTime);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
        _308_starttime = _14_Input_Compile.__default.getTimestamp();
        SAT__UNSAT _317_solution;
        SAT__UNSAT _out5;
        (_316_solver).start(out _out5);
        _317_solution = _out5;
        _310_totalTime = (new Dafny.BigRational(((_14_Input_Compile.__default.getTimestamp()) - (_308_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("c Time to solve: "));
        Dafny.Helpers.Print(_310_totalTime);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s\n"));
        SAT__UNSAT _source4 = _317_solution;
        if (_source4.is_SAT) {
          Dafny.Sequence<int> _318_x = ((SAT__UNSAT_SAT)_source4).tau;
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s SATISFIABLE\n"));
        } else  {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("s UNSATISFIABLE\n"));
        }
      }
    }
  }


  public abstract class SAT__UNSAT {
    public SAT__UNSAT() { }
    static SAT__UNSAT theDefault;
    public static SAT__UNSAT Default {
      get {
        if (theDefault == null) {
          theDefault = new SAT__UNSAT_SAT(Dafny.Sequence<int>.Empty);
        }
        return theDefault;
      }
    }
    public static SAT__UNSAT _DafnyDefaultValue() { return Default; }
    public static SAT__UNSAT create_SAT(Dafny.Sequence<int> tau) {
      return new SAT__UNSAT_SAT(tau);
    }
    public static SAT__UNSAT create_UNSAT() {
      return new SAT__UNSAT_UNSAT();
    }
    public bool is_SAT { get { return this is SAT__UNSAT_SAT; } }
    public bool is_UNSAT { get { return this is SAT__UNSAT_UNSAT; } }
    public Dafny.Sequence<int> dtor_tau {
      get {
        var d = this;
        return ((SAT__UNSAT_SAT)d).tau; 
      }
    }
  }
  public class SAT__UNSAT_SAT : SAT__UNSAT {
    public readonly Dafny.Sequence<int> tau;
    public SAT__UNSAT_SAT(Dafny.Sequence<int> tau) {
      this.tau = tau;
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_SAT;
      return oth != null && Dafny.Helpers.AreEqual(this.tau, oth.tau);
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
    public Formula formula = default(Formula);
    public void __ctor(Formula f_k)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).formula = f_k;
    }
    public void step(int literal, bool @value, out SAT__UNSAT result)
    {
      result = SAT__UNSAT.Default;
      (this.formula).increaseDecisionLevel();
      (this.formula).setLiteral(literal, @value);
      SAT__UNSAT _out6;
      (this).solve(out _out6);
      result = _out6;
      (this.formula).revertLastDecisionLevel();
      { }
      result = result;
      return;
    }
    public void solve(out SAT__UNSAT result)
    {
      result = SAT__UNSAT.Default;
      bool _319_hasEmptyClause;
      bool _out7;
      (this.formula).getHasEmptyClause(out _out7);
      _319_hasEmptyClause = _out7;
      if (_319_hasEmptyClause) {
        { }
        result = @SAT__UNSAT.create_UNSAT();
        return;
      }
      bool _320_isEmpty;
      bool _out8;
      (this.formula).getIsEmpty(out _out8);
      _320_isEmpty = _out8;
      if (_320_isEmpty) {
        { }
        result = @SAT__UNSAT.create_SAT(Dafny.Helpers.SeqFromArray(this.formula.truthAssignment));
        { }
        result = result;
        return;
      }
      int _321_literal;
      int _out9;
      (this.formula).chooseLiteral(out _out9);
      _321_literal = _out9;
      { }
      SAT__UNSAT _out10;
      (this).step(_321_literal, true, out _out10);
      result = _out10;
      if ((result).is_SAT) {
        result = result;
        return;
      }
      SAT__UNSAT _out11;
      (this).step(_321_literal, false, out _out11);
      result = _out11;
      if ((result).is_UNSAT) {
        { }
        { }
      }
      result = result;
      return;
    }
    public void start(out SAT__UNSAT result)
    {
      var _this = this;
    TAIL_CALL_START: ;
      result = SAT__UNSAT.Default;
      (_this.formula).level0UnitPropagation();
      SAT__UNSAT _out12;
      (_this).solve(out _out12);
      result = _out12;
    }
  }




  public partial class Formula : DataStructures {
    public int _variablesCount = 0;
    public int variablesCount {
      get {
        return this._variablesCount;
      }
      set {
        this._variablesCount = value;
      }
    }
    public Dafny.Sequence<Dafny.Sequence<int>> _clauses = Dafny.Sequence<Dafny.Sequence<int>>.Empty;
    public Dafny.Sequence<Dafny.Sequence<int>> clauses {
      get {
        return this._clauses;
      }
      set {
        this._clauses = value;
      }
    }
    public int _clausesCount = 0;
    public int clausesCount {
      get {
        return this._clausesCount;
      }
      set {
        this._clausesCount = value;
      }
    }
    public int[] _clauseLength = new int[0];
    public int[] clauseLength {
      get {
        return this._clauseLength;
      }
      set {
        this._clauseLength = value;
      }
    }
    public int[] _truthAssignment = new int[0];
    public int[] truthAssignment {
      get {
        return this._truthAssignment;
      }
      set {
        this._truthAssignment = value;
      }
    }
    public int[] _trueLiteralsCount = new int[0];
    public int[] trueLiteralsCount {
      get {
        return this._trueLiteralsCount;
      }
      set {
        this._trueLiteralsCount = value;
      }
    }
    public int[] _falseLiteralsCount = new int[0];
    public int[] falseLiteralsCount {
      get {
        return this._falseLiteralsCount;
      }
      set {
        this._falseLiteralsCount = value;
      }
    }
    public Dafny.Sequence<int>[] _positiveLiteralsToClauses = new Dafny.Sequence<int>[0];
    public Dafny.Sequence<int>[] positiveLiteralsToClauses {
      get {
        return this._positiveLiteralsToClauses;
      }
      set {
        this._positiveLiteralsToClauses = value;
      }
    }
    public Dafny.Sequence<int>[] _negativeLiteralsToClauses = new Dafny.Sequence<int>[0];
    public Dafny.Sequence<int>[] negativeLiteralsToClauses {
      get {
        return this._negativeLiteralsToClauses;
      }
      set {
        this._negativeLiteralsToClauses = value;
      }
    }
    public int _decisionLevel = 0;
    public int decisionLevel {
      get {
        return this._decisionLevel;
      }
      set {
        this._decisionLevel = value;
      }
    }
    public int[] _traceVariable = new int[0];
    public int[] traceVariable {
      get {
        return this._traceVariable;
      }
      set {
        this._traceVariable = value;
      }
    }
    public bool[] _traceValue = new bool[0];
    public bool[] traceValue {
      get {
        return this._traceValue;
      }
      set {
        this._traceValue = value;
      }
    }
    public int[] _traceDLStart = new int[0];
    public int[] traceDLStart {
      get {
        return this._traceDLStart;
      }
      set {
        this._traceDLStart = value;
      }
    }
    public int[] _traceDLEnd = new int[0];
    public int[] traceDLEnd {
      get {
        return this._traceDLEnd;
      }
      set {
        this._traceDLEnd = value;
      }
    }
    public int getVariableFromLiteral(int literal) {
      return (_16_Utils_Compile.__default.abs(literal)) - (1);
    }
    public _System.Tuple2<int,int> convertLVtoVI(int literal, bool @value)
    {
      int _322_variable = (this).getVariableFromLiteral(literal);
      int _323_v = (@value) ? (1) : (0);
      int _324_val = ((literal) < (0)) ? ((1) - (_323_v)) : (_323_v);
      return @_System.Tuple2<int,int>.create(_322_variable, _324_val);
    }
    public bool isUnitClause(int index) {
      return (((this.trueLiteralsCount)[(int)(index)]) == (0)) && ((((this.clauseLength)[(int)(index)]) - ((this.falseLiteralsCount)[(int)(index)])) == (1));
    }
    public bool isEmptyClause(int index) {
      return ((this.clauseLength)[(int)(index)]) == ((this.falseLiteralsCount)[(int)(index)]);
    }
    public void __ctor(int variablesCount, Dafny.Sequence<Dafny.Sequence<int>> clauses)
    {
      var _this = this;
    TAIL_CALL_START: ;
      { }
      { }
      { }
      (_this).variablesCount = variablesCount;
      (_this).clauses = clauses;
      (_this).decisionLevel = (0) - (1);
      var _nw5 = new int[(int)(variablesCount)];
      (_this).traceVariable = _nw5;
      var _nw6 = new bool[(int)(variablesCount)];
      (_this).traceValue = _nw6;
      var _nw7 = new int[(int)(variablesCount)];
      (_this).traceDLStart = _nw7;
      var _nw8 = new int[(int)(variablesCount)];
      (_this).traceDLEnd = _nw8;
      { }
      int _325_clsLength;
      _325_clsLength = (int)(clauses).Count;
      (_this).clausesCount = _325_clsLength;
      var _nw9 = new int[(int)(_325_clsLength)];
      (_this).clauseLength = _nw9;
      var _nw10 = new int[(int)(_325_clsLength)];
      (_this).trueLiteralsCount = _nw10;
      var _nw11 = new int[(int)(_325_clsLength)];
      (_this).falseLiteralsCount = _nw11;
      var _nw12 = Dafny.ArrayHelpers.InitNewArray1<Dafny.Sequence<int>>(Dafny.Sequence<int>.Empty, (variablesCount));
      (_this).positiveLiteralsToClauses = _nw12;
      var _nw13 = Dafny.ArrayHelpers.InitNewArray1<Dafny.Sequence<int>>(Dafny.Sequence<int>.Empty, (variablesCount));
      (_this).negativeLiteralsToClauses = _nw13;
      var _nw14 = new int[(int)(variablesCount)];
      (_this).truthAssignment = _nw14;
      int _326_k;
      _326_k = 0;
      while ((_326_k) < (_this.clausesCount)) {
        var _arr0 = _this.clauseLength;
        _arr0[(int)((_326_k))] = (int)((_this.clauses).Select(_326_k)).Count;
        _326_k = (_326_k) + (1);
      }
      int _327_index;
      _327_index = 0;
      while ((_327_index) < (variablesCount)) {
        var _arr1 = _this.truthAssignment;
        _arr1[(int)((_327_index))] = (0) - (1);
        { }
        { }
        _327_index = (_327_index) + (1);
      }
      (_this).createTFLArrays();
      (_this).createPositiveLiteralsToClauses();
      (_this).createNegativeLiteralsToClauses();
      { }
      { }
      { }
    }
    public void createTFLArrays()
    {
      var _this = this;
    TAIL_CALL_START: ;
      int _328_i;
      _328_i = 0;
      while ((_328_i) < (_this.clausesCount)) {
        { }
        var _arr2 = _this.trueLiteralsCount;
        _arr2[(int)((_328_i))] = 0;
        { }
        var _arr3 = _this.falseLiteralsCount;
        _arr3[(int)((_328_i))] = 0;
        _328_i = (_328_i) + (1);
      }
    }
    public void createPositiveLiteralsToClauses()
    {
      var _this = this;
    TAIL_CALL_START: ;
      int _329_variable;
      _329_variable = 0;
      while ((_329_variable) < (_this.variablesCount)) {
        var _arr4 = _this.positiveLiteralsToClauses;
        _arr4[(int)((_329_variable))] = Dafny.Sequence<int>.FromElements();
        int _330_clauseIndex;
        _330_clauseIndex = 0;
        while ((_330_clauseIndex) < (_this.clausesCount)) {
          if (((_this.clauses).Select(_330_clauseIndex)).Contains((_329_variable) + (1))) {
            var _arr5 = _this.positiveLiteralsToClauses;
            _arr5[(int)((_329_variable))] = ((_this.positiveLiteralsToClauses)[(int)(_329_variable)]).Concat(Dafny.Sequence<int>.FromElements(_330_clauseIndex));
          }
          _330_clauseIndex = (_330_clauseIndex) + (1);
        }
        _329_variable = (_329_variable) + (1);
      }
    }
    public void createNegativeLiteralsToClauses()
    {
      var _this = this;
    TAIL_CALL_START: ;
      int _331_variable;
      _331_variable = 0;
      while ((_331_variable) < (_this.variablesCount)) {
        var _arr6 = _this.negativeLiteralsToClauses;
        _arr6[(int)((_331_variable))] = Dafny.Sequence<int>.FromElements();
        int _332_clauseIndex;
        _332_clauseIndex = 0;
        while ((_332_clauseIndex) < (_this.clausesCount)) {
          if (((_this.clauses).Select(_332_clauseIndex)).Contains(((0) - (_331_variable)) - (1))) {
            var _arr7 = _this.negativeLiteralsToClauses;
            _arr7[(int)((_331_variable))] = ((_this.negativeLiteralsToClauses)[(int)(_331_variable)]).Concat(Dafny.Sequence<int>.FromElements(_332_clauseIndex));
          }
          _332_clauseIndex = (_332_clauseIndex) + (1);
        }
        _331_variable = (_331_variable) + (1);
      }
    }
    public void revertLastDecisionLevel()
    {
      { }
      while (((this.traceDLStart)[(int)(this.decisionLevel)]) < ((this.traceDLEnd)[(int)(this.decisionLevel)])) {
        (this).removeLastVariable();
        { }
      }
      (this).decisionLevel = (this.decisionLevel) - (1);
      { }
    }
    public void removeLastVariable()
    {
      { }
      int _333_k;
      _333_k = ((this.traceDLEnd)[(int)(this.decisionLevel)]) - (1);
      int _334_variable;
      _334_variable = (this.traceVariable)[(int)(_333_k)];
      bool _335_value;
      _335_value = (this.traceValue)[(int)(_333_k)];
      { }
      var _arr8 = this.traceDLEnd;
      var _index1 = this.decisionLevel;
      _arr8[(int)(_index1)] = _333_k;
      { }
      var _arr9 = this.truthAssignment;
      _arr9[(int)((_334_variable))] = (0) - (1);
      { }
      { }
      { }
      { }
      Dafny.Sequence<int> _336_positivelyImpactedClauses;
      _336_positivelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_334_variable)];
      Dafny.Sequence<int> _337_negativelyImpactedClauses;
      _337_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_334_variable)];
      if (!(_335_value)) {
        _337_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_334_variable)];
        _336_positivelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_334_variable)];
      }
      { }
      { }
      { }
      int _338_i;
      _338_i = 0;
      int _339_len;
      _339_len = (int)(_336_positivelyImpactedClauses).Count;
      while ((_338_i) < (_339_len)) {
        int _340_clauseIndex;
        _340_clauseIndex = (_336_positivelyImpactedClauses).Select(_338_i);
        { }
        { }
        { }
        var _arr10 = this.trueLiteralsCount;
        _arr10[(int)((_340_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_340_clauseIndex)]) - (1);
        _338_i = (_338_i) + (1);
      }
      _338_i = 0;
      _339_len = (int)(_337_negativelyImpactedClauses).Count;
      while ((_338_i) < (_339_len)) {
        int _341_clauseIndex;
        _341_clauseIndex = (_337_negativelyImpactedClauses).Select(_338_i);
        { }
        var _arr11 = this.falseLiteralsCount;
        _arr11[(int)((_341_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_341_clauseIndex)]) - (1);
        _338_i = (_338_i) + (1);
      }
      { }
    }
    public void setVariable(int variable, bool @value)
    {
      { }
      { }
      (this).addAssignment(variable, @value);
      if (@value) {
        var _arr12 = this.truthAssignment;
        _arr12[(int)((variable))] = 1;
      } else {
        var _arr13 = this.truthAssignment;
        _arr13[(int)((variable))] = 0;
      }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      int _342_i;
      _342_i = 0;
      Dafny.Sequence<int> _343_impactedClauses;
      _343_impactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      Dafny.Sequence<int> _344_impactedClauses_k;
      _344_impactedClauses_k = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _343_impactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
        _344_impactedClauses_k = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      { }
      int _345_impactedClausesLen;
      _345_impactedClausesLen = (int)(_343_impactedClauses).Count;
      while ((_342_i) < (_345_impactedClausesLen)) {
        int _346_clauseIndex;
        _346_clauseIndex = (_343_impactedClauses).Select(_342_i);
        { }
        { }
        var _arr14 = this.trueLiteralsCount;
        _arr14[(int)((_346_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_346_clauseIndex)]) + (1);
        { }
        { }
        _342_i = (_342_i) + (1);
      }
      { }
      int _347_i_k;
      _347_i_k = 0;
      int _348_impactedClausesLen_k;
      _348_impactedClausesLen_k = (int)(_344_impactedClauses_k).Count;
      while ((_347_i_k) < (_348_impactedClausesLen_k)) {
        int _349_clauseIndex;
        _349_clauseIndex = (_344_impactedClauses_k).Select(_347_i_k);
        { }
        { }
        var _arr15 = this.falseLiteralsCount;
        _arr15[(int)((_349_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_349_clauseIndex)]) + (1);
        _347_i_k = (_347_i_k) + (1);
      }
      { }
      { }
      { }
    }
    public void addAssignment(int variable, bool @value)
    {
      var _this = this;
    TAIL_CALL_START: ;
      var _arr16 = _this.traceVariable;
      var _index2 = (_this.traceDLEnd)[(int)(_this.decisionLevel)];
      _arr16[(int)(_index2)] = variable;
      var _arr17 = _this.traceValue;
      var _index3 = (_this.traceDLEnd)[(int)(_this.decisionLevel)];
      _arr17[(int)(_index3)] = @value;
      { }
      var _arr18 = _this.traceDLEnd;
      var _index4 = _this.decisionLevel;
      _arr18[(int)(_index4)] = ((_this.traceDLEnd)[(int)(_this.decisionLevel)]) + (1);
      { }
    }
    public void increaseDecisionLevel()
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).decisionLevel = (_this.decisionLevel) + (1);
      int _350_previous;
      _350_previous = 0;
      if ((_this.decisionLevel) == (0)) {
        _350_previous = 0;
      } else {
        _350_previous = (_this.traceDLEnd)[(int)((_this.decisionLevel) - (1))];
      }
      var _arr19 = _this.traceDLStart;
      var _index5 = _this.decisionLevel;
      _arr19[(int)(_index5)] = _350_previous;
      var _arr20 = _this.traceDLEnd;
      var _index6 = _this.decisionLevel;
      _arr20[(int)(_index6)] = _350_previous;
      { }
    }
    public void extractUnsetLiteralFromClause(int clauseIndex, out int literal)
    {
      var _this = this;
    TAIL_CALL_START: ;
      literal = 0;
      { }
      int _351_i;
      _351_i = 0;
      Dafny.Sequence<int> _352_clause;
      _352_clause = (_this.clauses).Select(clauseIndex);
      while ((_351_i) < ((_this.clauseLength)[(int)(clauseIndex)])) {
        if (((_this.truthAssignment)[(int)((_this).getVariableFromLiteral((_352_clause).Select(_351_i)))]) == ((0) - (1))) {
          literal = (_352_clause).Select(_351_i);
          return;
        }
        _351_i = (_351_i) + (1);
      }
      { }
    }
    public void propagate(int clauseIndex)
    {
      { }
      int _353_literal;
      int _out13;
      (this).extractUnsetLiteralFromClause(clauseIndex, out _out13);
      _353_literal = _out13;
      Dafny.Sequence<int> _354_clause;
      _354_clause = (this.clauses).Select(clauseIndex);
      { }
      { }
      (this).setLiteral(_353_literal, true);
      { }
      { }
      { }
      { }
    }
    public void unitPropagation(int variable, bool @value)
    {
      Dafny.Sequence<int> _355_negativelyImpactedClauses;
      _355_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _355_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      int _356_k;
      _356_k = 0;
      int _357_negativelyImpactedClausesLen;
      _357_negativelyImpactedClausesLen = (int)(_355_negativelyImpactedClauses).Count;
      while ((_356_k) < (_357_negativelyImpactedClausesLen)) {
        int _358_clauseIndex;
        _358_clauseIndex = (_355_negativelyImpactedClauses).Select(_356_k);
        if (((this.falseLiteralsCount)[(int)(_358_clauseIndex)]) < ((this.clauseLength)[(int)(_358_clauseIndex)])) {
          if ((((this.trueLiteralsCount)[(int)(_358_clauseIndex)]) == (0)) && ((((this.falseLiteralsCount)[(int)(_358_clauseIndex)]) + (1)) == ((this.clauseLength)[(int)(_358_clauseIndex)]))) {
            (this).propagate(_358_clauseIndex);
          }
        }
        _356_k = (_356_k) + (1);
      }
    }
    public void setLiteral(int literal, bool @value)
    {
      { }
      { }
      int _359_variable;
      _359_variable = (this).getVariableFromLiteral(literal);
      bool _360_value_k;
      _360_value_k = ((literal) > (0)) ? (@value) : (!(@value));
      (this).setVariable(_359_variable, _360_value_k);
      (this).unitPropagation(_359_variable, _360_value_k);
    }
    public void chooseLiteral(out int x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = 0;
      { }
      int _361_minim;
      _361_minim = _0_Int32_Compile.__default.max;
      int _362_counter;
      _362_counter = 0;
      int _363_result;
      _363_result = (0) - (1);
      bool _364_ok;
      _364_ok = false;
      int _365_cI;
      _365_cI = 0;
      while ((_365_cI) < (_this.clausesCount)) {
        int _366_diff;
        _366_diff = ((_this.clauseLength)[(int)(_365_cI)]) - ((_this.falseLiteralsCount)[(int)(_365_cI)]);
        if ((((_this.trueLiteralsCount)[(int)(_365_cI)]) == (0)) && ((_366_diff) < (_361_minim))) {
          _361_minim = _366_diff;
        }
        if ((((_this.trueLiteralsCount)[(int)(_365_cI)]) == (0)) && ((_366_diff) == (_361_minim))) {
          { }
          int _367_lI;
          _367_lI = 0;
          while ((_367_lI) < ((_this.clauseLength)[(int)(_365_cI)])) {
            { }
            { }
            int _368_variable;
            _368_variable = (_this).getVariableFromLiteral(((_this.clauses).Select(_365_cI)).Select(_367_lI));
            if (((_this.truthAssignment)[(int)(_368_variable)]) == ((0) - (1))) {
              _364_ok = true;
              if ((_362_counter) == (0)) {
                _363_result = (_368_variable) + (1);
                _362_counter = (_362_counter) + (1);
              } else if ((_363_result) == ((_368_variable) + (1))) {
                _362_counter = (_362_counter) + (1);
              } else {
                _362_counter = (_362_counter) - (1);
              }
            }
            _367_lI = (_367_lI) + (1);
          }
        }
        _365_cI = (_365_cI) + (1);
      }
      x = (0) - (_363_result);
      return;
    }
    public void getHasEmptyClause(out bool ok)
    {
      var _this = this;
    TAIL_CALL_START: ;
      ok = false;
      int _369_k;
      _369_k = 0;
      while ((_369_k) < (_this.clausesCount)) {
        if (((_this.falseLiteralsCount)[(int)(_369_k)]) == ((_this.clauseLength)[(int)(_369_k)])) {
          ok = true;
          return;
        }
        _369_k = (_369_k) + (1);
      }
      ok = false;
      return;
    }
    public void getIsEmpty(out bool ok)
    {
      var _this = this;
    TAIL_CALL_START: ;
      ok = false;
      int _370_k;
      _370_k = 0;
      while ((_370_k) < (_this.clausesCount)) {
        if (((_this.trueLiteralsCount)[(int)(_370_k)]) == (0)) {
          ok = false;
          return;
        }
        _370_k = (_370_k) + (1);
      }
      ok = true;
      return;
    }
    public void level0UnitPropagation()
    {
      var _this = this;
    TAIL_CALL_START: ;
      int _371_i;
      _371_i = 0;
      (_this).increaseDecisionLevel();
      while ((_371_i) < (_this.clausesCount)) {
        if ((((_this.trueLiteralsCount)[(int)(_371_i)]) == (0)) && ((((_this.falseLiteralsCount)[(int)(_371_i)]) + (1)) == ((_this.clauseLength)[(int)(_371_i)]))) {
          (_this).propagate(_371_i);
        }
        _371_i = (_371_i) + (1);
      }
      if (((_this.traceDLStart)[(int)(_this.decisionLevel)]) == ((_this.traceDLEnd)[(int)(_this.decisionLevel)])) {
        (_this).revertLastDecisionLevel();
      }
    }
  }



  public interface DataStructures {
    int variablesCount { get; set; }
    Dafny.Sequence<Dafny.Sequence<int>> clauses { get; set; }
    int clausesCount { get; set; }
    int[] clauseLength { get; set; }
    int[] truthAssignment { get; set; }
    int[] trueLiteralsCount { get; set; }
    int[] falseLiteralsCount { get; set; }
    Dafny.Sequence<int>[] positiveLiteralsToClauses { get; set; }
    Dafny.Sequence<int>[] negativeLiteralsToClauses { get; set; }
    int decisionLevel { get; set; }
    int[] traceVariable { get; set; }
    bool[] traceValue { get; set; }
    int[] traceDLStart { get; set; }
    int[] traceDLEnd { get; set; }
    int getVariableFromLiteral(int literal);
    _System.Tuple2<int,int> convertLVtoVI(int literal, bool @value);
    bool isUnitClause(int index);
    bool isEmptyClause(int index);
  }
  public class _Companion_DataStructures {
  }

} // end of namespace _module
