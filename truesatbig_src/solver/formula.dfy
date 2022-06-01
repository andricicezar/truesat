include "data_structures.dfy"
include "utils.dfy"
include "../int32.dfy"
include "../input_predicate.dfy"

class Formula extends DataStructures {
  constructor(
    variablesCount : Int32.t,
    clauses : seq<seq<Int32.t>>
  )
    requires InputPredicate.valid((variablesCount, clauses));

    ensures valid();

    ensures fresh(this.traceVariable) && fresh(this.traceValue) &&
      fresh(this.traceDLStart) && fresh(this.traceDLEnd) &&
      fresh(this.clauseLength) && fresh(this.trueLiteralsCount) &&
      fresh(this.falseLiteralsCount) && fresh(this.positiveLiteralsToClauses) &&
      fresh(this.negativeLiteralsToClauses) && fresh(this.truthAssignment);

    ensures this.decisionLevel == -1;
  {
    assert 0 < variablesCount < Int32.max;
    assert 0 < |clauses| <= Int32.max as int;
    assert forall clause :: (clause in clauses) ==>
               forall literal :: (literal in clause) ==> (
                 (literal < 0 && 0 < -literal <= variablesCount) ||
                 (literal > 0 && 0 < literal <= variablesCount));
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

    var k : Int32.t := 0;
    while (k < this.clausesCount)
      modifies this.clauseLength;
      invariant this.clauseLength.Length == this.clausesCount as int;
      invariant (forall i : Int32.t :: 0 <= i < k <= this.clausesCount ==>
                  this.clauseLength[i] as int == |clauses[i]|);
      invariant 0 <= k <= this.clausesCount;
    {
      this.clauseLength[k] := |this.clauses[k]| as Int32.t;
      k := k + 1;
    }

    var index : Int32.t := 0;
    while (index < variablesCount)
      modifies truthAssignment;
      invariant 0 <= index <= variablesCount;
      invariant forall j :: 0 <= j < index ==> truthAssignment[j] == -1;
      invariant forall j :: 0 <= j < index && truthAssignment[j] == -1 ==>
                  (j, false) !in assignmentsTrace && (j, true) !in assignmentsTrace;
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

  lemma inputPredicate_countLiterals(cI : Int32.t)
    requires validVariablesCount();
    requires validClauses();
    requires 0 <= cI <= clausesCount;
    ensures countLiterals(cI) == InputPredicate.countLiterals(clauses[..cI]);
  {
    if (cI == 0) {}
    else {
      inputPredicate_countLiterals(cI-1);
      var cl := clauses[..cI];
      assert clauses[..cI-1] == cl[..cI-1];
      assert countLiterals(cI-1) == InputPredicate.countLiterals(cl[..cI-1]);
      assert countLiterals(cI) == countLiterals(cI-1) + |clauses[cI-1]|;
      assert cI as int == |clauses[..cI]|;
      assert InputPredicate.countLiterals(cl) == InputPredicate.countLiterals(cl[..cI-1]) + |cl[cI-1]|;
    }
  }

  method createTFLArrays()
    requires validReferences();
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires validTruthAssignment();
    requires validClauses();

    requires trueLiteralsCount.Length == |clauses|;
    requires falseLiteralsCount.Length == |clauses|;

    requires forall value :: 0 <= value < truthAssignment.Length ==>
                truthAssignment[value] == -1;

    modifies trueLiteralsCount, falseLiteralsCount;

    ensures validTrueLiteralsCount(truthAssignment[..]);
    ensures validFalseLiteralsCount(truthAssignment[..]);
  {
    var i : Int32.t := 0;

    while (i < clausesCount)
      invariant 0 <= i <= clausesCount;
      invariant forall j :: 0 <= j < i ==>
          trueLiteralsCount[j] == countTrueLiterals(truthAssignment[..], clauses[j]);
      invariant forall j :: 0 <= j < i ==>
          falseLiteralsCount[j] == countFalseLiterals(truthAssignment[..], clauses[j]);

      decreases clausesCount - i;
    {
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      trueLiteralsCount[i] := 0;

      prop_countFalseLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      falseLiteralsCount[i] := 0;

      i := i + 1;
    }
  }

  method createPositiveLiteralsToClauses()
    requires validReferences();
    requires validVariablesCount();
    requires validClauses();
    requires positiveLiteralsToClauses.Length == variablesCount as int;

    modifies positiveLiteralsToClauses;

    ensures validPositiveLiteralsToClauses();
  {
    var variable := 0;

    while (variable < variablesCount)
      invariant 0 <= variable <= variablesCount;

      invariant forall v :: 0 <= v < variable ==>
        validPositiveLiteralToClause(v, positiveLiteralsToClauses[v]);

      invariant forall v :: 0 <= v < variable ==>
        |positiveLiteralsToClauses[v]| <= clausesCount as int;

      decreases variablesCount - variable;
    {
      positiveLiteralsToClauses[variable] := [];

      var clauseIndex : Int32.t := 0;
      while (clauseIndex < clausesCount)
        invariant 0 <= clauseIndex <= clausesCount;

        invariant forall v :: 0 <= v < variable ==>
          validPositiveLiteralToClause(v, positiveLiteralsToClauses[v]);
        invariant forall v :: 0 <= v < variable ==>
          |positiveLiteralsToClauses[v]| <= clausesCount as int;
        invariant |positiveLiteralsToClauses[variable]| <= clauseIndex as int;

        invariant Utils.valuesBoundedBy(positiveLiteralsToClauses[variable], 0, |clauses|);
        invariant |positiveLiteralsToClauses[variable]| > 0 ==>
                    positiveLiteralsToClauses[variable][|positiveLiteralsToClauses[variable]|-1] < clauseIndex;
        invariant Utils.orderedAsc(positiveLiteralsToClauses[variable]);
        invariant forall cI :: cI in positiveLiteralsToClauses[variable] ==>
                    variable+1 in clauses[cI];
        invariant forall cI :: 0 <= cI < clauseIndex ==>
                    cI !in positiveLiteralsToClauses[variable] ==>
                      variable+1 !in clauses[cI];

        decreases clausesCount - clauseIndex;
      {
        if (variable+1 in clauses[clauseIndex]) {
          positiveLiteralsToClauses[variable] :=
            positiveLiteralsToClauses[variable] + [clauseIndex];
        }

        clauseIndex := clauseIndex + 1;
      }

      variable := variable + 1;
    }
  }

  method createNegativeLiteralsToClauses()
    requires validReferences();
    requires validVariablesCount();
    requires validClauses();
    requires negativeLiteralsToClauses.Length == variablesCount as int;

    modifies negativeLiteralsToClauses;

    ensures validNegativeLiteralsToClauses();
  {
    var variable : Int32.t := 0;

    while (variable < variablesCount)
      invariant 0 <= variable <= variablesCount;
      invariant forall v :: 0 <= v < variable ==>
                  validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v]);
      invariant forall v :: 0 <= v < variable ==>
                  |negativeLiteralsToClauses[v]| <= clausesCount as int;

      decreases variablesCount - variable;
    {
      negativeLiteralsToClauses[variable] := [];

      var clauseIndex : Int32.t := 0;
      while (clauseIndex < clausesCount)
        invariant 0 <= clauseIndex <= clausesCount;

        invariant forall v :: 0 <= v < variable ==>
                    validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v]);

        invariant forall v :: 0 <= v < variable ==>
                    |negativeLiteralsToClauses[v]| <= clausesCount as int;

        invariant |negativeLiteralsToClauses[variable]| <= clauseIndex as int;


        invariant Utils.valuesBoundedBy(negativeLiteralsToClauses[variable], 0, |clauses|);
        invariant |negativeLiteralsToClauses[variable]| > 0 ==>
                    negativeLiteralsToClauses[variable][|negativeLiteralsToClauses[variable]|-1] < clauseIndex;
        invariant Utils.orderedAsc(negativeLiteralsToClauses[variable]);
        invariant forall cI :: cI in negativeLiteralsToClauses[variable] ==>
                    -variable-1 in clauses[cI];
        invariant forall cI :: 0 <= cI < clauseIndex ==>
                    cI !in negativeLiteralsToClauses[variable] ==>
                      -variable-1 !in clauses[cI];

        decreases |clauses| - clauseIndex as int;
      {
        if (-variable-1 in clauses[clauseIndex]) {
          negativeLiteralsToClauses[variable] :=
            negativeLiteralsToClauses[variable] + [clauseIndex];
        }

        clauseIndex := clauseIndex + 1;
      }

      variable := variable + 1;
    }
  }

  method revertLastDecisionLevel()
    requires valid();
    requires 0 <= decisionLevel;

    modifies `assignmentsTrace, `decisionLevel, truthAssignment, trueLiteralsCount,
             falseLiteralsCount, traceDLEnd;

    ensures decisionLevel == old(decisionLevel) - 1;
    ensures assignmentsTrace == old(assignmentsTrace) - old(getDecisionLevel(decisionLevel));
    ensures valid();
    ensures forall i :: 0 <= i <= decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);
    ensures decisionLevel > -1 ==>
      traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
  {
    ghost var k : Int32.t := traceDLEnd[decisionLevel]-1;

    while (traceDLStart[decisionLevel] < traceDLEnd[decisionLevel])
      modifies `assignmentsTrace, traceDLEnd, truthAssignment,
               trueLiteralsCount, falseLiteralsCount;

      invariant traceDLStart[decisionLevel]-1 <= k < traceDLEnd[decisionLevel];
      invariant k == traceDLEnd[decisionLevel]-1;

      invariant valid();
      invariant forall i :: 0 <= i < decisionLevel ==>
        old(getDecisionLevel(i)) == getDecisionLevel(i);
    {
      removeLastVariable();
      k := k - 1;
    }

    decisionLevel := decisionLevel - 1;

    assert old(traceVariable[..]) == traceVariable[..];
  }

  method removeLastVariable()
    requires valid();
    requires 0 <= decisionLevel < variablesCount;
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
    modifies `assignmentsTrace,
             traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount;

    ensures traceDLEnd[decisionLevel] == old(traceDLEnd[decisionLevel]) - 1;
    ensures valid();
    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);
  {
    forall_validAssignmentTrace_traceDLEndStrictlyOrdered();
    var k : Int32.t := traceDLEnd[decisionLevel]-1;
    var variable := traceVariable[k];
    var value := traceValue[k];

    assignmentsTrace := assignmentsTrace - { (variable, value) };
    traceDLEnd[decisionLevel] := k;

    ghost var previousTau := truthAssignment[..];
    truthAssignment[variable] := -1;
    ghost var newTau := truthAssignment[..];
    assert forall i :: 0 <= i < decisionLevel ==>
      traceDLEnd[i] == old(traceDLEnd[i]) && traceDLStart[i] == old(traceDLStart[i]);
    assert traceVariable[..traceDLEnd[decisionLevel]] == old(traceVariable[..traceDLEnd[decisionLevel]-1]);
    assert forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);

    var positivelyImpactedClauses : seq<Int32.t> := positiveLiteralsToClauses[variable]; // decrease true counter
    var negativelyImpactedClauses : seq<Int32.t> := negativeLiteralsToClauses[variable];  // decrease false counters

    if (!value) {
      negativelyImpactedClauses := positiveLiteralsToClauses[variable]; // decrease true counter
      positivelyImpactedClauses := negativeLiteralsToClauses[variable];  // decrease false counters
    }

    assert Utils.valuesBoundedBy(positivelyImpactedClauses, 0, |clauses|);
    assert Utils.valuesBoundedBy(negativelyImpactedClauses, 0, |clauses|);

    undoImpactedClauses_TFSArraysModified(
      previousTau,
      newTau,
      variable,
      positivelyImpactedClauses,
      negativelyImpactedClauses
    );

    var i : Int32.t := 0;
    var len := |positivelyImpactedClauses| as Int32.t;
    while (i < len)
      modifies trueLiteralsCount;

      invariant len as int == |positivelyImpactedClauses|;
      invariant 0 <= i <= len;

      invariant forall i' :: 0 <= i' < clausesCount && i' !in positivelyImpactedClauses ==>
        trueLiteralsCount[i']
          == countTrueLiterals(newTau, clauses[i']);

      invariant forall i' :: 0 <= i' < i ==>
        trueLiteralsCount[positivelyImpactedClauses[i']]
          == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']]);

      invariant forall i' :: i <= i' < len ==>
        trueLiteralsCount[positivelyImpactedClauses[i']]
          == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']]);
    {
      var clauseIndex := positivelyImpactedClauses[i];
      ghost var clause := clauses[clauseIndex];
      assert validClause(clause);

      unsetVariable_countTrueLiteralsDecreasesWithOne(previousTau, newTau, variable, clause);
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;

      i := i + 1;
    }

    assert trueLiteralsCount.Length == |clauses|;
    forall i : Int32.t | 0 <= i as int < |clauses|
      ensures trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i])
    {
      if (i !in positivelyImpactedClauses)
      {
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
      else
      {
        var j : Int32.t :| 0 <= j as int < |positivelyImpactedClauses| && positivelyImpactedClauses[j] == i;
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];

    i := 0;

    len := |negativelyImpactedClauses| as Int32.t;
    modify falseLiteralsCount {
    while (i < len)
      modifies falseLiteralsCount;
      invariant 0 <= i <= len;

      invariant forall i' :: 0 <= i' < i ==>
        falseLiteralsCount[negativelyImpactedClauses[i']]
          == countFalseLiterals(newTau, clauses[negativelyImpactedClauses[i']]);

      invariant forall i' :: i <= i' < len ==>
        falseLiteralsCount[negativelyImpactedClauses[i']]
          == countFalseLiterals(previousTau, clauses[negativelyImpactedClauses[i']]);

      invariant forall i' :: 0 <= i' < clausesCount && i' !in negativelyImpactedClauses ==>
        falseLiteralsCount[i']
          == countFalseLiterals(newTau, clauses[i']);

      invariant forall i' :: 0 <= i' < clausesCount && i' !in positivelyImpactedClauses ==>
        trueLiteralsCount[i']
          == countTrueLiterals(newTau, clauses[i']);

      invariant forall i' :: 0 <= i' < |positivelyImpactedClauses| ==>
        trueLiteralsCount[positivelyImpactedClauses[i']]
          == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']]);

      // invariant forall i' :: 0 <= i' < |positivelyImpactedClauses| ==>
      //   trueLiteralsCount[positivelyImpactedClauses[i']]
      //     == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']]);
      invariant validTrueLiteralsCount(truthAssignment[..]);

      decreases len - i;
    {
      var clauseIndex := negativelyImpactedClauses[i];

      unsetVariable_countFalseLiteralsDecreasesWithOne(previousTau, newTau, variable, clauses[clauseIndex]);
      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
      i := i + 1;
    }
    }
    assert falseLiteralsCount.Length == |clauses|;
    forall i : Int32.t | 0 <= i as int < |clauses|
      ensures falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i])
    {
      if (i !in negativelyImpactedClauses)
      {
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
      else
      {
        var j : Int32.t :| 0 <= j as int < |negativelyImpactedClauses| && negativelyImpactedClauses[j] == i;
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert old(traceVariable[..]) == traceVariable[..];
  }

  method setVariable(variable : Int32.t, value : bool)
    requires valid();
    requires validVariable(variable);
    requires truthAssignment[variable] == -1;
    requires 0 <= decisionLevel; // not empty

    modifies truthAssignment, traceVariable, traceValue,
             traceDLEnd, `assignmentsTrace, trueLiteralsCount,
             falseLiteralsCount;

    ensures valid();
    ensures value == false ==> old(truthAssignment[..])[variable as int := 0]
      == truthAssignment[..];
    ensures value == true ==> old(truthAssignment[..])[variable as int := 1]
      == truthAssignment[..];
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
    ensures traceVariable[traceDLEnd[decisionLevel]-1] == variable;
    ensures traceValue[traceDLEnd[decisionLevel]-1] == value;
    ensures forall i :: 0 <= i < variablesCount && i != decisionLevel ==>
              traceDLEnd[i] == old(traceDLEnd[i]);
    ensures forall i :: 0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==>
              traceVariable[i] == old(traceVariable[i]) && traceValue[i] == old(traceValue[i]);
		ensures forall x :: 0 <= x < old(traceDLEnd[decisionLevel]) ==>
			traceVariable[x] == old(traceVariable[x]);

    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);

    ensures assignmentsTrace == old(assignmentsTrace) + { (variable, value) };
    ensures countUnsetVariables(truthAssignment[..]) + 1 ==
      old(countUnsetVariables(truthAssignment[..]));
  {
    ghost var oldTau : seq<Int32.t> := truthAssignment[..];

    existsUnsetLiteral_traceNotFull(variable);

    addAssignment(variable, value);

    if (value) {
      truthAssignment[variable] := 1;
    } else {
      truthAssignment[variable] := 0;
    }

    assert validTruthAssignment();
    ghost var newTau := truthAssignment[..];

    ghost var trueLiteral := variable+1;
    ghost var falseLiteral := -variable-1;

    if (!value) {
      trueLiteral := -variable-1;
      falseLiteral := variable+1;
    }

    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;

    var i : Int32.t := 0;

    var impactedClauses := positiveLiteralsToClauses[variable];
    var impactedClauses' := negativeLiteralsToClauses[variable];

    if (!value) {
      impactedClauses := negativeLiteralsToClauses[variable];
      impactedClauses' := positiveLiteralsToClauses[variable];
    }

    clausesNotImpacted_TFArraysSame(
      oldTau,
      newTau,
      variable,
      impactedClauses,
      impactedClauses'
    );

    var impactedClausesLen : Int32.t := |impactedClauses| as Int32.t;
    while (i < impactedClausesLen)
      modifies trueLiteralsCount;

      invariant 0 <= i <= impactedClausesLen;

      invariant forall j : Int32.t :: 0 <= j < clausesCount && j !in impactedClauses
        ==> trueLiteralsCount[j] == countTrueLiterals(newTau, clauses[j]);

      invariant forall j :: 0 <= j < i ==>
        trueLiteralsCount[impactedClauses[j]]
          == countTrueLiterals(newTau, clauses[impactedClauses[j]]);

      invariant forall j :: i <= j < impactedClausesLen ==>
        trueLiteralsCount[impactedClauses[j]]
          == countTrueLiterals(oldTau, clauses[impactedClauses[j]]);

      decreases impactedClausesLen - i;
    {
      var clauseIndex := impactedClauses[i];

      unsetVariable_countTrueLiteralsLessThanLength(oldTau, variable, clauses[clauseIndex]);
      setVariable_countTrueLiteralsIncreasesWithOne(
        oldTau,
        newTau,
        variable,
        clauses[clauseIndex]
      );

      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] + 1;

      assert trueLiteral in clauses[clauseIndex]
        && getLiteralValue(newTau, trueLiteral) == 1;
      assert isClauseSatisfied(newTau, clauseIndex);

      i := i + 1;
    }

    assert trueLiteralsCount.Length == |clauses|;
    forall i : Int32.t | 0 <= i as int < |clauses|
      ensures trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i])
    {
      if (i !in impactedClauses)
      {
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
      else
      {
        var j : Int32.t :| 0 <= j as int < |impactedClauses| && impactedClauses[j] == i;
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert validTrueLiteralsCount(truthAssignment[..]);

    var i' : Int32.t := 0;

    var impactedClausesLen' : Int32.t := |impactedClauses'| as Int32.t;
    while (i' < impactedClausesLen')
      modifies falseLiteralsCount;

      invariant 0 <= i' <= impactedClausesLen';

      invariant forall j : Int32.t :: 0 <= j < clausesCount && j !in impactedClauses'
        ==> falseLiteralsCount[j] == countFalseLiterals(newTau, clauses[j]);

      invariant forall j :: 0 <= j < i' ==>
        falseLiteralsCount[impactedClauses'[j]] ==
          countFalseLiterals(newTau, clauses[impactedClauses'[j]]);

      invariant forall j :: i' <= j < impactedClausesLen' ==>
        falseLiteralsCount[impactedClauses'[j]] ==
          countFalseLiterals(oldTau, clauses[impactedClauses'[j]]);

      decreases impactedClausesLen' - i';
    {
      var clauseIndex := impactedClauses'[i'];

      unsetVariable_countFalseLiteralsLessThanLength(oldTau, variable, clauses[clauseIndex]);
      setVariable_countFalseLiteralsIncreasesWithOne(
        oldTau,
        newTau,
        variable,
        clauses[clauseIndex]
      );

      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] + 1;

      i' := i' + 1;
    }

    assert falseLiteralsCount.Length == |clauses|;
    forall i : Int32.t | 0 <= i as int < |clauses|
      ensures falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i])
    {
      if (i !in impactedClauses)
      {
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
      else
      {
        var j : Int32.t :| 0 <= j as int < |impactedClauses| && impactedClauses[j] == i;
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert validFalseLiteralsCount(truthAssignment[..]);

    variableSet_countUnsetVariablesLessThanLength(newTau, variable);
    setVariable_unsetVariablesDecreasesWithOne(oldTau, newTau, variable);
  }

  lemma traceFull_variableInTrace(variable : Int32.t)
    requires valid();
    requires validVariable(variable);
    requires 0 <= decisionLevel;
    requires traceDLEnd[decisionLevel] == variablesCount;

    ensures exists i :: 0 <= i < traceDLEnd[decisionLevel] &&
      traceVariable[i] == variable;
  {
    var L : set<Int32.t>, R : set<Int32.t> := {}, Utils.RangeSet(0, variablesCount);
    var i : Int32.t := 0;
    Utils.CardinalityRangeSet(0, variablesCount);

    while (i < variablesCount)
      invariant 0 <= i <= variablesCount;
      invariant L == set j | 0 <= j < i :: traceVariable[j];
      invariant forall v :: 0 <= v < variablesCount ==>
        v in L || v in R;
      invariant |R| == (variablesCount - i) as int;

      decreases variablesCount - i;
    {
      L, R := L + {traceVariable[i]}, R - {traceVariable[i]};
      i := i + 1;
    }

    assert variable in L;
  }

  lemma existsUnsetLiteral_traceNotFull(variable : Int32.t)
    requires valid();
    requires validVariable(variable);
    requires truthAssignment[variable] == -1;
    requires 0 <= decisionLevel;

    ensures traceDLEnd[decisionLevel] < variablesCount;
    ensures forall x :: x in assignmentsTrace ==>
      x.0 != variable;
  {
    if (traceDLEnd[decisionLevel] == variablesCount) {
      traceFull_variableInTrace(variable);

      var i :| 0 <= i < traceDLEnd[decisionLevel] &&
        traceVariable[i] == variable;

      assert (traceVariable[i], traceValue[i]) in assignmentsTrace;
      assert traceVariable[i] == variable;
      assert traceValue[i] == false || traceValue[i] || true;
      assert (variable, true) in assignmentsTrace ||
        (variable, false) in assignmentsTrace;

      assert truthAssignment[variable] == -1 ==>
        (variable, false) !in assignmentsTrace
          && (variable, true) !in assignmentsTrace;


      assert false;
    }

    if (exists x :: x in assignmentsTrace && x.0 == variable) {
      var x :| x in assignmentsTrace && x.0 == variable;
      var (a, b) := x;
      assert a == variable;
      assert b == true || b == false;
      assert (variable, false) !in assignmentsTrace
          && (variable, true) !in assignmentsTrace;
      assert false;
    }
  }

  method addAssignment(variable : Int32.t, value : bool)
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires 0 <= decisionLevel;
    requires 0 <= variable < variablesCount;
    requires forall x :: x in assignmentsTrace ==> x.0 != variable; // not already assigned
    requires traceDLEnd[decisionLevel] < variablesCount; // not full

    modifies `assignmentsTrace, traceDLEnd, traceVariable, traceValue;

    ensures traceDLEnd[decisionLevel] == old(traceDLEnd[decisionLevel]) + 1;
    ensures traceVariable[traceDLEnd[decisionLevel]-1] == variable;
    ensures traceValue[traceDLEnd[decisionLevel]-1] == value;
    ensures forall i :: 0 <= i < variablesCount && i != decisionLevel ==>
              traceDLEnd[i] == old(traceDLEnd[i]);
    ensures forall i :: 0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==>
              traceVariable[i] == old(traceVariable[i]) && traceValue[i] == old(traceValue[i]);
    ensures assignmentsTrace == old(assignmentsTrace) + { (variable, value) };
    ensures validAssignmentTrace();

    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);
  {
    traceVariable[traceDLEnd[decisionLevel]] := variable;
    traceValue[traceDLEnd[decisionLevel]] := value;
    assignmentsTrace := assignmentsTrace + { (variable, value) };

    traceDLEnd[decisionLevel] := traceDLEnd[decisionLevel] + 1;

    forall_validAssignmentTrace_traceDLEndStrictlyOrdered();
  }

  lemma forall_validAssignmentTrace_traceDLStartStrictlyOrdered()
    requires 0 <= decisionLevel;
    requires decisionLevel as int < traceDLStart.Length;
    requires decisionLevel as int < traceDLEnd.Length;

    ensures validVariablesCount() && validAssignmentTrace() ==>
      (forall i, j :: 0 <= i < j <= decisionLevel ==>
        traceDLStart[i] < traceDLStart[j]);
  {
    if (validVariablesCount() && validAssignmentTrace()) {
      forall (i, j | 0 <= i < j <= decisionLevel)
        ensures traceDLStart[i] < traceDLStart[j];
      {
        validAssignmentTrace_traceDLStartStrictlyOrdered(i, j);
      }
    }
  }

  lemma validAssignmentTrace_traceDLStartStrictlyOrdered(i : Int32.t, j : Int32.t)
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires 0 <= i < j <= decisionLevel;

    ensures traceDLStart[i] < traceDLStart[j];
    decreases decisionLevel - i;
  {
    if (i == j - 1) {
    } else if (i < j - 1) {
      validAssignmentTrace_traceDLStartStrictlyOrdered(i+1, j);
    }
  }

  lemma forall_validAssignmentTrace_traceDLEndStrictlyOrdered()
    requires 0 <= decisionLevel;
    requires decisionLevel as int < traceDLStart.Length;
    requires decisionLevel as int < traceDLEnd.Length;
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];

    ensures validVariablesCount() && validAssignmentTrace() ==>
      (forall i :: 0 <= i < decisionLevel ==>
        traceDLEnd[i] < traceDLEnd[decisionLevel]);
  {
    if (validVariablesCount() && validAssignmentTrace()) {
      forall (i | 0 <= i < decisionLevel)
        ensures traceDLEnd[i] < traceDLEnd[decisionLevel];
      {
        validAssignmentTrace_traceDLEndStrictlyOrdered(i);
      }
    }
  }

  lemma validAssignmentTrace_traceDLEndStrictlyOrdered(i : Int32.t)
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires 0 <= i < decisionLevel;
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];

    ensures traceDLEnd[i] < traceDLEnd[decisionLevel];

    decreases decisionLevel - i;
  {
    if (i == decisionLevel - 1) {
    } else if (i < decisionLevel - 1) {
      validAssignmentTrace_traceDLEndStrictlyOrdered(i+1);
    }
  }

  method increaseDecisionLevel()
    requires validVariablesCount();
    requires validAssignmentTrace();
    requires decisionLevel < variablesCount - 1; // not full
    requires decisionLevel >= 0 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];

    modifies `decisionLevel, traceDLStart, traceDLEnd;

    ensures decisionLevel == old(decisionLevel) + 1;
    ensures validAssignmentTrace();
    ensures traceDLStart[decisionLevel] == traceDLEnd[decisionLevel];
    ensures getDecisionLevel(decisionLevel) == {};
    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);
  {
    decisionLevel := decisionLevel + 1;

    var previous : Int32.t := 0;
    if (decisionLevel == 0) {
      previous := 0;
    } else {
      previous := traceDLEnd[decisionLevel-1];
    }

    traceDLStart[decisionLevel] := previous;
    traceDLEnd[decisionLevel] := previous;

    assert old(traceVariable[..]) == traceVariable[..];
  }

  function getDecisionLevel(dL : Int32.t) : set<(Int32.t, bool)>
    reads `variablesCount, `decisionLevel, `traceDLStart,
          `traceDLEnd, `traceVariable, `traceValue,
          traceDLStart, traceDLEnd, traceVariable,
          traceValue, `assignmentsTrace;
    requires validVariablesCount();
    requires validAssignmentTrace()
    requires -1 <= dL <= decisionLevel;
    requires traceVariable.Length == variablesCount as int;
    ensures getDecisionLevel(dL) <= assignmentsTrace;
  {
    if dL == -1 then {}
    else (set j | j in assignmentsTrace && j.0 in traceVariable[traceDLStart[dL]..traceDLEnd[dL]])
  }

  method extractUnsetLiteralFromClause(clauseIndex : Int32.t) returns (literal : Int32.t)
    requires valid();
    requires 0 <= clauseIndex < clausesCount;
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex];
    requires trueLiteralsCount[clauseIndex] == 0 &&
      falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex];

    ensures validLiteral(literal);
    ensures literal in clauses[clauseIndex];
    ensures truthAssignment[getVariableFromLiteral(literal)] == -1;
  {
    unitClause_existsUnsetLiteral(clauseIndex);

    var i : Int32.t := 0;

    var clause := clauses[clauseIndex];
    while (i < clauseLength[clauseIndex])
      invariant 0 <= i < clauseLength[clauseIndex];
      invariant exists literal :: literal in clause[i..]
          && truthAssignment[getVariableFromLiteral(literal)] == -1;

      decreases clauseLength[clauseIndex] - i;
    {
      if truthAssignment[getVariableFromLiteral(clause[i])] == -1 {
        return clause[i];
      }

      i := i + 1;
    }

    assert false;
  }

  method propagate(clauseIndex : Int32.t)
    requires valid();
    requires 0 <= decisionLevel; // not empty
    requires 0 <= clauseIndex < clausesCount;
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex];
    requires trueLiteralsCount[clauseIndex] == 0 &&
      falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex];

    modifies truthAssignment, trueLiteralsCount,
             falseLiteralsCount, traceDLEnd, traceValue,
             traceVariable, `assignmentsTrace;

    ensures valid();

    ensures forall x :: 0 <= x < old(traceDLEnd[decisionLevel]) ==>
      traceVariable[x] == old(traceVariable[x]);

    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
    ensures assignmentsTrace == old(assignmentsTrace) +
      getDecisionLevel(decisionLevel);
    ensures countUnsetVariables(truthAssignment[..]) <
      old(countUnsetVariables(truthAssignment[..]));
    ensures old(assignmentsTrace) <= assignmentsTrace;
    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);

    ensures (
      ghost var tau := old(truthAssignment[..]);

      isSatisfiableExtend(tau) <==>
              isSatisfiableExtend(truthAssignment[..])
    );

		decreases countUnsetVariables(truthAssignment[..]), 1;
  {
    ghost var tau'' := truthAssignment[..];

    var literal := extractUnsetLiteralFromClause(clauseIndex);
    var clause := clauses[clauseIndex];

    ghost var (v', val') := convertLVtoVI(literal, true);

    unitClauseLiteralFalse_tauNotSatisfiable(tau'', clauseIndex, literal);
    setLiteral(literal, true);

    assert isSatisfiableExtend(tau''[v' as int := val']) <==>
            isSatisfiableExtend(truthAssignment[..]);

    if (isSatisfiableExtend(truthAssignment[..])) {
      extensionSatisfiable_baseSatisfiable(tau'', v', val');
    } else {
      forVariableNotSatisfiableExtend_notSatisfiableExtend(tau'', v');
    }
    assert !isSatisfiableExtend(tau'') <==>
              !isSatisfiableExtend(truthAssignment[..]);

    assert countUnsetVariables(truthAssignment[..]) <
      old(countUnsetVariables(truthAssignment[..]));
  }

  method unitPropagation(variable : Int32.t, value : bool)
    requires valid();
    requires validVariable(variable);
    requires 0 <= decisionLevel; // not empty
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];

    modifies truthAssignment, trueLiteralsCount,
             falseLiteralsCount, traceDLEnd, traceValue,
             traceVariable, `assignmentsTrace;

    ensures valid();
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
		ensures old(assignmentsTrace) <= assignmentsTrace;
    ensures assignmentsTrace == old(assignmentsTrace) +
      getDecisionLevel(decisionLevel);
		ensures forall x :: 0 <= x < old(traceDLEnd[decisionLevel]) ==>
			traceVariable[x] == old(traceVariable[x]);

    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);
    ensures countUnsetVariables(truthAssignment[..]) <=
      old(countUnsetVariables(truthAssignment[..]));

    ensures (
      ghost var tau := old(truthAssignment[..]);

      isSatisfiableExtend(tau) <==>
              isSatisfiableExtend(truthAssignment[..])
							);

		decreases countUnsetVariables(truthAssignment[..]), 2;
  {
    var negativelyImpactedClauses := negativeLiteralsToClauses[variable];
    if (!value) {
      negativelyImpactedClauses := positiveLiteralsToClauses[variable];
    }
    var k : Int32.t := 0;
    var negativelyImpactedClausesLen : Int32.t := |negativelyImpactedClauses| as Int32.t;

    while (k < negativelyImpactedClausesLen)
      invariant 0 <= k <= negativelyImpactedClausesLen;
      invariant valid();
			invariant decisionLevel == old(decisionLevel);
      invariant traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
      invariant assignmentsTrace == old(assignmentsTrace) +
        getDecisionLevel(decisionLevel);
			invariant countUnsetVariables(truthAssignment[..]) <=
				old(countUnsetVariables(truthAssignment[..]));
			invariant isSatisfiableExtend(old(truthAssignment[..])) <==>
        isSatisfiableExtend(truthAssignment[..]);
			invariant forall x :: 0 <= x < old(traceDLEnd[decisionLevel]) ==>
				traceVariable[x] == old(traceVariable[x]);
      invariant forall i :: 0 <= i < decisionLevel ==>
        old(getDecisionLevel(i)) == getDecisionLevel(i);
			decreases |negativelyImpactedClauses| - k as int;
    {
      var clauseIndex := negativelyImpactedClauses[k];

			if (falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]) {
				if (trueLiteralsCount[clauseIndex] == 0 &&
					falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex]) {
            propagate(clauseIndex);
				}
			}

      k := k + 1;
    }
  }

  method setLiteral(literal : Int32.t, value : bool)
    requires valid();
    requires validLiteral(literal);
    requires getLiteralValue(truthAssignment[..], literal) == -1;
    requires 0 <= decisionLevel; // not empty

    modifies truthAssignment, trueLiteralsCount,
             falseLiteralsCount, traceDLEnd, traceValue,
             traceVariable, `assignmentsTrace;

    ensures valid();
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
    ensures forall x :: 0 <= x < old(traceDLEnd[decisionLevel]) ==>
      traceVariable[x] == old(traceVariable[x]);
    ensures assignmentsTrace == old(assignmentsTrace) +
      getDecisionLevel(decisionLevel);
    ensures forall i :: 0 <= i < decisionLevel ==>
      old(getDecisionLevel(i)) == getDecisionLevel(i);
    ensures countUnsetVariables(truthAssignment[..]) <
      old(countUnsetVariables(truthAssignment[..]));
    ensures (
      ghost var (variable, val) := convertLVtoVI(literal, value);
      isSatisfiableExtend(old(truthAssignment[..])[variable as int := val]) <==>
              isSatisfiableExtend(truthAssignment[..])
    );

    decreases countUnsetVariables(truthAssignment[..]), 0;
  {
    ghost var (vari, val) := convertLVtoVI(literal, value);
    ghost var tau' := truthAssignment[..][vari as int := val];

    var variable := getVariableFromLiteral(literal);
    var value' := if literal > 0 then value else !value;

    setVariable(variable, value');
    unitPropagation(variable, value');
  }

  method chooseLiteral() returns (x : Int32.t)
    requires valid();
    requires !hasEmptyClause();
    requires !isEmpty();

    ensures valid();
    ensures validLiteral(x);
    ensures truthAssignment[getVariableFromLiteral(x)] == -1;
    ensures getLiteralValue(truthAssignment[..], x) == -1;
  {
    notEmptyNoEmptyClauses_existUnsetLiteralInClauses();

    var minim : Int32.t := Int32.max;
    var counter : Int32.t := 0;
    var result : Int32.t := -1;
    var ok := false;

    var cI : Int32.t := 0;
    while (cI < clausesCount)
      invariant 0 <= cI <= clausesCount;
      invariant !ok ==> counter == 0 && minim == Int32.max && (exists i', k' ::
        cI <= i' < clausesCount &&
        0 <= k' < |clauses[i']| &&
        trueLiteralsCount[i'] == 0 &&
        validLiteral(clauses[i'][k']) &&
        truthAssignment[getVariableFromLiteral(clauses[i'][k'])] == -1 &&
        getLiteralValue(truthAssignment[..], clauses[i'][k']) == -1);
      invariant (exists i', k' ::
        0 <= i' < cI &&
        0 <= k' < |clauses[i']| &&
        trueLiteralsCount[i'] == 0 &&
        validLiteral(clauses[i'][k']) &&
        truthAssignment[getVariableFromLiteral(clauses[i'][k'])] == -1 &&
        getLiteralValue(truthAssignment[..], clauses[i'][k']) == -1) ==> ok;
      invariant ok ==> validLiteral(result) &&
           truthAssignment[getVariableFromLiteral(result)] == -1 &&
           getLiteralValue(truthAssignment[..], result) == -1;
      invariant 0 <= counter as int <= countLiterals(cI);
    {
      var diff := clauseLength[cI] - falseLiteralsCount[cI];

      if (trueLiteralsCount[cI] == 0 && diff < minim) {
        minim := diff;
      }

      if (trueLiteralsCount[cI] == 0 && diff == minim) {
        assert validClause(clauses[cI]);

        var lI : Int32.t := 0;
        while (lI < clauseLength[cI])
          invariant 0 <= lI <= clauseLength[cI];
          invariant !ok ==> counter == 0 && (exists k' ::
            lI as int <= k' < |clauses[cI]| &&
            trueLiteralsCount[cI] == 0 &&
            validLiteral(clauses[cI][k']) &&
            truthAssignment[getVariableFromLiteral(clauses[cI][k'])] == -1 &&
            getLiteralValue(truthAssignment[..], clauses[cI][k']) == -1);
          invariant (exists k' ::
            0 <= k' < lI &&
            trueLiteralsCount[cI] == 0 &&
            validLiteral(clauses[cI][k']) &&
            truthAssignment[getVariableFromLiteral(clauses[cI][k'])] == -1 &&
            getLiteralValue(truthAssignment[..], clauses[cI][k']) == -1) ==> ok;

          invariant ok ==> validLiteral(result) &&
              truthAssignment[getVariableFromLiteral(result)] == -1 &&
              getLiteralValue(truthAssignment[..], result) == -1;
          invariant 0 <= counter as int <= countLiterals(cI) + lI as int;
        {
          countLiterals_monotone(cI);
          assert validLiteral(clauses[cI][lI]);
          var variable := getVariableFromLiteral(clauses[cI][lI]);
          if (truthAssignment[variable] == -1) {
            ok := true;
            if (counter == 0) {
              result := variable+1;
              counter := counter + 1;
            } else if (result == variable+1) {
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

  lemma maybeClause_existUnsetLiteralInClause(clauseIndex : Int32.t)
    requires valid();
    requires 0 <= clauseIndex < clausesCount;
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]

    ensures exists j' :: 0 <= j' < clauseLength[clauseIndex] &&
                        validLiteral(clauses[clauseIndex][j']) &&
        truthAssignment[getVariableFromLiteral(clauses[clauseIndex][j'])] == -1;
  {
    ghost var tau := truthAssignment[..];
    var clause := clauses[clauseIndex];

    countTrueLiterals0_noLiteralsTrue(tau, clause);

    var clauseLen := clauseLength[clauseIndex];
    var k := clauseLen - 1;
    var flc := 0;
    var ok := false;
    var index : Int32.t := 0;

    assert clauseLen > 0;

    while (k >= 0)
      invariant -1 <= k < clauseLen;
      invariant forall k' :: k < k' < clauseLen ==>
        getLiteralValue(tau, clause[k']) != 1;
      invariant countTrueLiterals(tau, clause[k + 1..]) == 0;
      invariant countFalseLiterals(tau, clause[k+1..]) == flc;
      invariant flc == clauseLen-1-k ==> ok == false;
      invariant flc < clauseLen-1-k ==> ok == true;
      invariant ok ==> 0 <= index < clauseLen;
      invariant ok ==> getLiteralValue(tau, clause[index]) == -1;
      decreases k;
    {
      if (getLiteralValue(tau, clause[k]) == 0) {
        flc := flc + 1;
      }

      if (getLiteralValue(tau, clause[k]) == -1) {
        ok := true;
        index := k;
      }

      k := k - 1;
    }

    assert ok;
    assert clause[index] in clauses[clauseIndex];
    assert 0 <= index < clauseLen;
    assert validLiteral(clauses[clauseIndex][index]);
    assert truthAssignment[getVariableFromLiteral(clauses[clauseIndex][index])] == -1;
  }

  lemma notEmptyNoEmptyClauses_existUnsetLiteralInClauses()
    requires valid();
    requires !hasEmptyClause();
    requires !isEmpty();

    ensures forall i :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0
                    && falseLiteralsCount[i] < clauseLength[i] ==>
            exists j' :: 0 <= j' < clauseLength[i] &&
                        validLiteral(clauses[i][j']) &&
        truthAssignment[getVariableFromLiteral(clauses[i][j'])] == -1;
  {
    forall (i | 0 <= i < clausesCount && trueLiteralsCount[i] == 0
                    && falseLiteralsCount[i] < clauseLength[i])
        ensures exists j' :: 0 <= j' < clauseLength[i] &&
                    validLiteral(clauses[i][j']) &&
        truthAssignment[getVariableFromLiteral(clauses[i][j'])] == -1;
    {
      maybeClause_existUnsetLiteralInClause(i);
    }
  }

  function hasEmptyClause() : bool
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue,
          truthAssignment, trueLiteralsCount,
          falseLiteralsCount, clauseLength,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    ensures hasEmptyClause() == true ==>
      exists i :: 0 <= i < |clauses|
               && falseLiteralsCount[i] as int == |clauses[i]|;
    ensures hasEmptyClause() == false ==>
      forall i :: 0 <= i < |clauses| ==>
        falseLiteralsCount[i] as int < |clauses[i]|;
  {
    if i : Int32.t :| 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i]
      then true
      else false
  }

  method getHasEmptyClause() returns (ok : bool)
    requires valid();

    ensures ok <==> hasEmptyClause();
    ensures ok ==>
      exists i :: 0 <= i < clausesCount
               && falseLiteralsCount[i] == clauseLength[i];

    ensures !ok ==>
      forall i :: 0 <= i < clausesCount ==>
        falseLiteralsCount[i] < clauseLength[i];
  {
    var k : Int32.t := 0;
    while (k < clausesCount)
      invariant 0 <= k <= clausesCount;
      invariant forall k' :: 0 <= k' < k ==>
        falseLiteralsCount[k'] < clauseLength[k'];
    {
      if (falseLiteralsCount[k] == clauseLength[k]) {
        return true;
      }
      k := k + 1;
    }

    return false;
  }

  function isEmpty() : bool
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue,
          truthAssignment, trueLiteralsCount,
          falseLiteralsCount, clauseLength,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    requires !hasEmptyClause();
    ensures isEmpty() == true ==>
      forall i :: 0 <= i < |clauses| ==>
        trueLiteralsCount[i] > 0;
    ensures isEmpty() == false ==>
      exists i :: 0 <= i < |clauses|
               && trueLiteralsCount[i] == 0;
  {
    if i : Int32.t :| 0 <= i < clausesCount && trueLiteralsCount[i] == 0
      then false
      else true
  }

  method getIsEmpty() returns (ok : bool)
    requires valid();
    requires !hasEmptyClause();

    ensures ok <==> isEmpty();
    ensures ok ==>
      forall i :: 0 <= i < clausesCount ==>
        trueLiteralsCount[i] > 0;
    ensures !ok ==>
      exists i :: 0 <= i < clausesCount
               && trueLiteralsCount[i] == 0;
  {
    var k : Int32.t := 0;
    while (k < clausesCount)
      invariant 0 <= k <= clausesCount;
      invariant forall k' :: 0 <= k' < k ==>
        trueLiteralsCount[k'] > 0;
    {
      if (trueLiteralsCount[k] == 0) {
        return false;
      }
      k := k + 1;
    }

    return true;
  }

  method level0UnitPropagation()
    requires valid();
    requires decisionLevel == -1;

    modifies truthAssignment, trueLiteralsCount,
             falseLiteralsCount, traceDLStart, traceDLEnd, traceValue,
             traceVariable, `assignmentsTrace, `decisionLevel;

    ensures valid();
    ensures decisionLevel > -1 ==>
      traceDLStart[decisionLevel] <
        traceDLEnd[decisionLevel];

    ensures (
      isSatisfiableExtend(old(truthAssignment[..])) <==>
        isSatisfiableExtend(truthAssignment[..])
    );
  {
    var i := 0;
    increaseDecisionLevel();

    while (i < clausesCount)
      modifies truthAssignment, trueLiteralsCount,
             falseLiteralsCount, traceDLStart, traceDLEnd, traceValue,
             traceVariable, `assignmentsTrace;
      invariant 0 <= i <= clausesCount;
      invariant valid();
      invariant (
        isSatisfiableExtend(old(truthAssignment[..])) <==>
          isSatisfiableExtend(truthAssignment[..])
      );
    {
      if (trueLiteralsCount[i] == 0 &&
        falseLiteralsCount[i] + 1 == clauseLength[i]) {
        propagate(i);
      }

      i := i + 1;
    }

    if (traceDLStart[decisionLevel] == traceDLEnd[decisionLevel]) {
      revertLastDecisionLevel();
    }
  }

  lemma notEmptyNoEmptyClauses_traceNotFull()
    requires valid();
    requires !hasEmptyClause();
    requires !isEmpty();
    requires decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];

    ensures decisionLevel < variablesCount - 1;
  {
    if (decisionLevel == variablesCount - 1) {
      ifFull_containsAllVariables();

      forall v | 0 <= v < variablesCount
        ensures truthAssignment[v] != -1;
      {
        if (truthAssignment[v] == -1) {
          assert (v, true) !in assignmentsTrace;
          assert (v, false) !in assignmentsTrace;
          assert occursInAssignmentsTrace(v);
          var x :| x in assignmentsTrace && x.0 == v;
          var (i, b) := x;

          assert x == (v, true) || x == (v, false);
          assert false;
        }
      }

      allVariablesSet_done();
      assert false;
    }
  }

  predicate occursInTrace(variable : Int32.t)
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue,
          truthAssignment, trueLiteralsCount,
          falseLiteralsCount, clauseLength,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    requires validVariable(variable);
    requires decisionLevel > -1;
  {
    exists j :: 0 <= j < traceDLEnd[decisionLevel] &&
      traceVariable[j] == variable
  }

  predicate occursInAssignmentsTrace(variable : Int32.t)
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue,
          truthAssignment, trueLiteralsCount,
          falseLiteralsCount, clauseLength,
          positiveLiteralsToClauses, negativeLiteralsToClauses;
    requires valid();
    requires validVariable(variable);
    requires decisionLevel > -1;
    requires decisionLevel == variablesCount - 1;
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];
  {
    exists x :: x in assignmentsTrace && x.0 == variable
  }



  lemma ifFull_containsAllVariables()
    requires valid();
    requires !hasEmptyClause();
    requires !isEmpty();
    requires decisionLevel == variablesCount - 1;
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel];

    ensures forall v :: 0 <= v < variablesCount ==>
      occursInTrace(v);

    ensures forall v :: 0 <= v < variablesCount ==>
      occursInAssignmentsTrace(v);
  {
    var L: set<Int32.t>, R: set<Int32.t> := {}, Utils.RangeSet(0, variablesCount);
    var i : Int32.t := 0;
    Utils.CardinalityRangeSet(0, variablesCount);

    forall_validAssignmentTrace_traceDLStartStrictlyOrdered();

    while (i < variablesCount)
      invariant 0 <= i <= variablesCount;
      invariant L == set j | 0 <= j < i :: traceVariable[traceDLStart[j]];
      invariant forall v :: v in L ==> validVariable(v);
      invariant forall v :: v in L ==> occursInTrace(v);
      invariant forall v :: 0 <= v < variablesCount ==>
        v in L || v in R;
      invariant |R| == (variablesCount - i) as int;

      decreases variablesCount - i;
    {
      L, R := L + {traceVariable[traceDLStart[i]]}, R - {traceVariable[traceDLStart[i]]};
      i := i + 1;
    }

    assert forall v :: 0 <= v < variablesCount ==>
      v in L && occursInTrace(v);

    forall v | 0 <= v < variablesCount
      ensures occursInAssignmentsTrace(v);
    {
      assert occursInTrace(v);
      var j :| 0 <= j < variablesCount && traceVariable[traceDLStart[j]] == v;
      if (j < decisionLevel) {
        validAssignmentTrace_traceDLStartStrictlyOrdered(j, decisionLevel);
      }
      assert traceDLStart[j] < traceDLEnd[decisionLevel];
      assert (traceVariable[traceDLStart[j]], traceValue[traceDLStart[j]]) in assignmentsTrace;
      assert occursInAssignmentsTrace(v);
    }

    assert forall v :: 0 <= v < variablesCount ==>
      occursInAssignmentsTrace(v);
  }

  lemma allVariablesSet_done()
    requires valid();
    requires forall v :: validVariable(v) ==>
      isVariableSet(truthAssignment[..], v);
    ensures hasEmptyClause() || isEmpty();
  {
    if (!hasEmptyClause()) {
      if (!isEmpty()) {
        var k := 0;

        assert forall k :: 0 <= k < |clauses| ==>
          falseLiteralsCount[k] as int < |clauses[k]|;

        while (k < |clauses|)
          invariant 0 <= k <= |clauses|;
          invariant forall k' :: 0 <= k' < k ==>
                      trueLiteralsCount[k'] > 0;

          decreases |clauses| - k;
        {
          assert validClause(clauses[k]);
          assert falseLiteralsCount[k] as int < |clauses[k]|;

          assert forall x :: x in clauses[k] ==>
            isVariableSet(truthAssignment[..], getVariableFromLiteral(x));

          tauFullClauseNotEmpty_clauseIsSatisfied(k);

          k := k + 1;
        }
      } else {
      }
    } else {
    }
  }

  lemma tauFullClauseNotEmpty_clauseIsSatisfied(cI : int)
    requires valid();
    requires 0 <= cI < |clauses|;
    requires validClause(clauses[cI]);
    requires forall x :: x in clauses[cI] ==>
      isVariableSet(truthAssignment[..], getVariableFromLiteral(x));
    requires falseLiteralsCount[cI] as int < |clauses[cI]|;

    ensures trueLiteralsCount[cI] > 0;
  {
    var tau := truthAssignment[..];
    var clause := clauses[cI];

    assert forall x :: x in clause ==>
      getLiteralValue(tau, x) in [0, 1];

    if forall x :: x in clause ==> getLiteralValue(tau, x) == 0 {
      var k := |clause| - 1;

      while (k > 0)
        invariant 0 <= k <= |clause|;

        invariant countFalseLiterals(tau, clause[k..]) as int == |clause| - k;

        decreases k;
      {
        k := k - 1;
      }

      assert countFalseLiterals(tau, clause) as int == |clause| == |clauses[cI]|;
    } else {
      assert exists x :: x in clause && getLiteralValue(tau, x) == 1;
      existsTrueLiteral_countTrueLiteralsPositive(clause, tau);
    }
  }

  lemma existsTrueLiteral_countTrueLiteralsPositive(clause : seq<Int32.t>, truthAssignment : seq<Int32.t>)
    requires valid();
    requires validValuesTruthAssignment(truthAssignment);
    requires validClause(clause);
    requires exists x :: x in clause && getLiteralValue(truthAssignment, x) == 1;

    ensures countTrueLiterals(truthAssignment, clause) > 0;
  {
    if (|clause| == 0) {}
    else if (getLiteralValue(truthAssignment, clause[0]) == 1) {}
    else {
      existsTrueLiteral_countTrueLiteralsPositive(clause[1..], truthAssignment);
    }
  }





  lemma unitClause_existsUnsetLiteral(clauseIndex : Int32.t)
    requires valid();
    requires 0 <= clauseIndex as int < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires trueLiteralsCount[clauseIndex] == 0;
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|;

    ensures exists literal :: literal in clauses[clauseIndex]
                && truthAssignment[getVariableFromLiteral(literal)] == -1;
  {
    maybeClause_existUnsetLiteralInClause(clauseIndex);
  }

  lemma hasEmptyClause_notSatisfiable()
    requires valid();
    requires hasEmptyClause();

    ensures !isSatisfiableExtend(truthAssignment[..]);
  {
    var tau := truthAssignment[..];
    var clauseIndex : Int32.t :| 0 <= clauseIndex as int < |clauses|
               && falseLiteralsCount[clauseIndex] as int == |clauses[clauseIndex]|;
    var clause := clauses[clauseIndex];
    assert validClause(clause);
    allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex);

    if tau' :| validValuesTruthAssignment(tau')
        && isTauComplete(tau')
        && isExtendingTau(tau, tau')
        && isSatisfied(tau') {
      assert forall l :: l in clause ==>
        getLiteralValue(tau, l) == getLiteralValue(tau', l) == 0;
      assert !isClauseSatisfied(tau', clauseIndex);
      assert false;
    }
  }

  lemma allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex : Int32.t)
    requires valid();
    requires 0 <= clauseIndex as int < |clauses|;
    requires falseLiteralsCount[clauseIndex] as int == |clauses[clauseIndex]|;
    requires validClause(clauses[clauseIndex]);

    ensures forall literal :: literal in clauses[clauseIndex] ==>
              getLiteralValue(truthAssignment[..], literal) == 0;
  {
    var clause := clauses[clauseIndex];
    var k : Int32.t := 0;
    var flc := 0;
    var tau := truthAssignment[..];

    while (k as int < |clause|)
      invariant 0 <= k as int <= |clause|;
      invariant countFalseLiterals(tau, clause[k..]) ==
                  falseLiteralsCount[clauseIndex] - k;
      invariant forall k' :: 0 <= k' < k ==>
        getLiteralValue(tau, clause[k']) == 0;
      decreases |clause| - k as int;
    {
      k := k + 1;
    }
  }

  lemma isEmpty_sastisfied()
    requires valid();
    requires !hasEmptyClause();
    requires isEmpty();

    ensures isSatisfiableExtend(truthAssignment[..]);
  {
    assert forall i :: 0 <= i < |clauses| ==>
        trueLiteralsCount[i] > 0;

    forall i : Int32.t | 0 <= i as int < |clauses|
      ensures isClauseSatisfied(truthAssignment[..], i);
    {
      countTrueLiteralsX_existsTrueLiteral(truthAssignment[..], clauses[i]);
    }

    assert isSatisfied(truthAssignment[..]);

    assert variablesCount > 0;

    partialTauSatisfied_isSatisfiableExtend(truthAssignment[..]);
  }

  lemma partialTauSatisfied_isSatisfiableExtend(tau : seq<Int32.t>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
    requires validClauses();
    requires isSatisfied(tau);

    ensures isSatisfiableExtend(tau);
    decreases countUnsetVariables(tau);
  {
    if (isTauComplete(tau)) {
    } else {
      var x :| 0 <= x < |tau| && tau[x] == -1;
      var tau' := tau[x := 0];
      forall i : Int32.t | 0 <= i as int < |clauses|
        ensures isClauseSatisfied(tau', i);
      {
        assert isClauseSatisfied(tau, i);
      }
      assert isSatisfied(tau');
      var k := |tau'|-1;

      while (k > 0)
        invariant 0 <= k < |tau'|;
        invariant x < k < |tau'| ==>
          countUnsetVariables(tau'[k..]) == countUnsetVariables(tau[k..]);
        invariant 0 <= k <= x ==>
          countUnsetVariables(tau'[k..])+1 == countUnsetVariables(tau[k..]);
      {
        k := k - 1;
      }
      assert countUnsetVariables(tau) - 1 == countUnsetVariables(tau');
      partialTauSatisfied_isSatisfiableExtend(tau');
    }

  }

  lemma unitClause_allFalseExceptLiteral(
    truthAssignment : seq<Int32.t>,
    clauseIndex : Int32.t,
    literal : Int32.t
  )
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
    requires validTrueLiteralsCount(truthAssignment);
    requires validFalseLiteralsCount(truthAssignment);
    requires 0 <= clauseIndex as int < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires validLiteral(literal);

    // the clause is unit
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|;
    requires literal in clauses[clauseIndex];
    requires getLiteralValue(truthAssignment, literal) == -1;
    requires forall literal :: literal in clauses[clauseIndex] ==>
              getLiteralValue(truthAssignment, literal) != 1;

    ensures forall literal' :: literal' in clauses[clauseIndex] && literal' != literal ==>
            getLiteralValue(truthAssignment, literal') != -1;
  {
    var clause := clauses[clauseIndex];
    var literalIndex :| 0 <= literalIndex < |clause| && clause[literalIndex] == literal;

    if i :| 0 <= i < |clause|
        && i != literalIndex
        && getLiteralValue(truthAssignment, clause[i]) == -1 {

        var a := i;
        var b := literalIndex;
        if (b < a) {
          a := literalIndex;
          b := i;
        }

        assert a < b;
        assert getLiteralValue(truthAssignment, clause[a]) == -1;
        assert getLiteralValue(truthAssignment, clause[b]) == -1;


        var k := |clause|-1;
        while (k >= 0)
          invariant -1 <= k < |clause|;
          invariant 0 <= a < b < |clause|;
          invariant b <= k ==>
            countFalseLiterals(truthAssignment, clause[k+1..]) as int <= |clause|-(k+1);
          invariant a <= k < b  ==>
            countFalseLiterals(truthAssignment, clause[k+1..]) as int <= |clause|-(k+1)-1;
          invariant k < a  ==>
            countFalseLiterals(truthAssignment, clause[k+1..]) as int <= |clause|-(k+1)-2;

          decreases k;
        {
          k := k-1;
        }

        assert false;
    }
  }

  lemma unitClauseLiteralFalse_tauNotSatisfiable(
    truthAssignment : seq<Int32.t>,
    clauseIndex : Int32.t,
    literal : Int32.t
  )
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(truthAssignment);
    requires validTrueLiteralsCount(truthAssignment);
    requires validFalseLiteralsCount(truthAssignment);
    requires 0 <= clauseIndex as int < |clauses|;
    requires validClause(clauses[clauseIndex]);
    requires validLiteral(literal);
    requires trueLiteralsCount[clauseIndex] == 0;
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|;
    requires truthAssignment[getVariableFromLiteral(literal)] == -1;
    requires literal in clauses[clauseIndex];

    ensures (
      ghost var (variable, value) := convertLVtoVI(literal, false);
      !isSatisfiableExtend(truthAssignment[variable as int := value])
    );
  {
    var clause := clauses[clauseIndex];
    var (variable, value) := convertLVtoVI(literal, false);


    countTrueLiterals0_noLiteralsTrue(truthAssignment, clause);

    unitClause_allFalseExceptLiteral(truthAssignment, clauseIndex, literal);

    var tau := truthAssignment[variable as int := value];
    var k := |clause| - 1;

    while (k >= 0)
      invariant -1 <= k < |clause|;
      invariant forall k' :: k < k' < |clause| ==>
        getLiteralValue(tau, clause[k']) == 0;
      decreases k;
    {
      if (getLiteralValue(tau, clause[k]) == 1) {
        assert literal in clause;
        assert clause[k] in clause;
        if (literal == clause[k]) {
          assert getLiteralValue(truthAssignment, literal) == -1;
          assert getLiteralValue(tau, literal) == 0;
          assert false;
        } else if (-literal == clause[k]) {
          assert false;
        } else {
          assert getLiteralValue(truthAssignment, clause[k]) != 1;
          assert getVariableFromLiteral(clause[k]) != variable;
          assert tau[getVariableFromLiteral(clause[k])]
              == truthAssignment[getVariableFromLiteral(clause[k])];
          assert getLiteralValue(tau, clause[k]) != 1;
          assert false;
        }

        assert false;
      }

      if (getLiteralValue(tau, clause[k]) == -1) {
        assert false;
      }

      k := k - 1;
    }

    if tau' :| validValuesTruthAssignment(tau')
        && isTauComplete(tau')
        && isExtendingTau(tau, tau')
        && isSatisfied(tau') {
      assert forall l :: l in clause ==>
        getLiteralValue(tau, l) == getLiteralValue(tau', l) == 0;
      assert !isClauseSatisfied(tau', clauseIndex);
      assert false;
    }
  }

  lemma variableSet_countUnsetVariablesLessThanLength(
    tau : seq<Int32.t>,
    variable : Int32.t
  )
    requires |tau| <= Int32.max as int;
    requires 0 <= variable as int < |tau|;
    requires tau[variable] in [0, 1];
    ensures countUnsetVariables(tau) as int < |tau|;
  {
    var k := |tau| - 1;

    while (k >= 0)
      invariant -1 <= k < |tau|;

      invariant forall j :: k < j < |tau| && j > variable as int ==>
            countUnsetVariables(tau[j..]) as int <= |tau[j..]|;
      invariant forall j :: k < j < |tau| && j <= variable as int ==>
            countUnsetVariables(tau[j..]) as int < |tau[j..]|;
      decreases k;
    {
      if (k == variable as int) {
        assert tau[variable] != -1;
      }

      k := k - 1;
    }
  }

  lemma unsetVariable_countTrueLiteralsLessThanLength(
    tau : seq<Int32.t>,
    variable : Int32.t,
    clause : seq<Int32.t>
  )
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
    requires validClause(clause);
    requires validVariable(variable);
    requires tau[variable] == -1;
    requires variable+1 in clause || -variable-1 in clause;
    ensures countTrueLiterals(tau, clause) as int < |clause|;
  {
    var literal : Int32.t := variable + 1;
    if (variable+1 !in clause) {
      literal := -variable-1;
    }
    var k := |clause| - 1;

    while (k >= 0 && clause[k] != literal)
      invariant -1 <= k < |clause|;
      invariant countTrueLiterals(tau, clause[k + 1..]) as int <= |clause[k + 1..]|;
      invariant forall j :: k < j < |clause| ==> clause[j] != literal;
      decreases k;
    {
      k := k - 1;
    }
    if (k < 0)
    {
      assert false;
    }
    else
    {
      assert clause[k] == literal;
      assert getLiteralValue(tau, clause[k]) == -1;
      assert countTrueLiterals(tau, clause[k..]) as int < |clause[k..]|;
      k := k - 1;
      while (k >= 0)
        invariant -1 <= k < |clause|;
        invariant countTrueLiterals(tau, clause[k + 1..]) as int < |clause[k + 1..]|;
        decreases k;
      {
        k := k - 1;
      }
    }
  }

  lemma unsetVariable_countFalseLiteralsLessThanLength(tau : seq<Int32.t>, variable : Int32.t, clause : seq<Int32.t>)
    requires validVariablesCount();
    requires validValuesTruthAssignment(tau);
    requires validClause(clause);
    requires validVariable(variable);
    requires tau[variable] == -1;
    requires variable+1 in clause || -variable-1 in clause;
    ensures countFalseLiterals(tau, clause) as int < |clause|;
  {
    var literal : Int32.t := variable + 1;
    if (variable+1 !in clause) {
      literal := -variable-1;
    }
    var k := |clause| - 1;

    while (k >= 0 && clause[k] != literal)
      invariant -1 <= k < |clause|;
      invariant countFalseLiterals(tau, clause[k + 1..]) as int <= |clause[k + 1..]|;
      invariant forall j :: k < j < |clause| ==> clause[j] != literal;
      decreases k;
    {
      k := k - 1;
    }
    if (k < 0)
    {
      assert false;
    }
    else
    {
      assert clause[k] == literal;
      assert getLiteralValue(tau, clause[k]) == -1;
      assert countFalseLiterals(tau, clause[k..]) as int < |clause[k..]|;
      k := k - 1;
      while (k >= 0)
        invariant -1 <= k < |clause|;
        invariant countFalseLiterals(tau, clause[k + 1..]) as int < |clause[k + 1..]|;
        decreases k;
      {
        k := k - 1;
      }
    }
  }

  lemma forVariableNotSatisfiableExtend_notSatisfiableExtend(
    tau : seq<Int32.t>,
    variable : Int32.t
  )
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
    requires validVariable(variable);

    requires !isSatisfiableExtend(tau[variable as int := 0]);
    requires !isSatisfiableExtend(tau[variable as int := 1]);

    ensures !isSatisfiableExtend(tau);
  {
    if (isSatisfiableExtend(tau)) {
      ghost var tauT := getExtendedCompleteTau(tau);

      if (tauT[variable] == 0) {
        assert isExtendingTau(tau[variable as int := 0], tauT);
      } else if (tauT[variable] == 1) {
        assert isExtendingTau(tau[variable as int := 1], tauT);
      }
    }
  }

  lemma extensionSatisfiable_baseSatisfiable(
    tau : seq<Int32.t>,
    variable : Int32.t,
    value : Int32.t
  )
    requires validVariablesCount();
    requires validClauses();
    requires validValuesTruthAssignment(tau);
    requires validVariable(variable);
    requires value in [0,1];
    requires tau[variable] == -1;

    requires isSatisfiableExtend(tau[variable as int := value]);

    ensures isSatisfiableExtend(tau);
  {
    ghost var tau' := tau[variable as int := value];
    assert isSatisfiableExtend(tau');

    ghost var tau'' := getExtendedCompleteTau(tau');
    assert isExtendingTau(tau, tau'');
  }
}

