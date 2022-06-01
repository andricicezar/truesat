include "int32.dfy"
include "my_datatypes.dfy"
include "input_predicate.dfy"

module Useless {
  import opened MyDatatypes
  import Int32
  import InputPredicate

  predicate valid'(c : array<char>) {
    0 < c.Length < Int32.max as int
  }

  class Parser {
    var content : array<char>;
    var contentLength : Int32.t;
    var cursor : Int32.t;

    constructor(c : array<char>) 
      requires valid'(c);
      ensures valid();
    {
      content := c; 
      contentLength := c.Length as Int32.t;
      cursor := 0;
    }

    predicate valid() 
      reads `content, content, `contentLength, `cursor;
    {
      valid'(content) && 
      contentLength as int == content.Length &&
      0 <= cursor <= contentLength
    }

    method skipLine()
      requires valid();
      modifies `cursor;
      ensures valid();
      ensures old(cursor) <= cursor;
    {
      while (cursor < contentLength && content[cursor] != '\n')
        invariant 0 <= cursor <= contentLength;
      {
        cursor := cursor + 1;
      }

      if (cursor < contentLength) {
        cursor := cursor + 1;
      }
    }

    method toNextNumber()
      requires valid();
      modifies `cursor;
      ensures valid();
      ensures old(cursor) <= cursor;
      ensures cursor < contentLength ==>
        (content[cursor] == '-' || ('0' <= content[cursor] <= '9'));
    {
      while (cursor < contentLength && !('0' <= content[cursor] <= '9' || content[cursor] == '-'))
        invariant 0 <= cursor <= contentLength;
      {
        cursor := cursor + 1;
      }
    }

    method extractNumber() returns (res : Maybe<Int32.t>)
      requires valid();
      requires cursor < contentLength ==>
        (content[cursor] == '-' || ('0' <= content[cursor] <= '9'));
      modifies `cursor;
      ensures valid();
      ensures old(cursor) <= cursor;
      ensures res.Just? ==> old(cursor) < cursor;
    {
      var number := 0;
      var isNegative : bool := false;

      if (cursor < contentLength && content[cursor] == '-') {
        isNegative := true;
        cursor := cursor + 1;
      }

      if (cursor == contentLength) {
        return Error("There is no number around here.");
      }

      while (cursor < contentLength && ('0' <= content[cursor] <= '9'))
        invariant 0 <= cursor <= contentLength;
        invariant 0 <= number <= Int32.max;
      {
        var digit : Int32.t := content[cursor] as Int32.t - '0' as Int32.t;
        if (number <= (Int32.max - digit) / 10) {
          assert 0 <= (Int32.max - digit) / 10 - number;
          number := number * 10 + digit;
        } else {
          return Error("There is a number bigger than Int32.max");
        }
        cursor := cursor + 1;
      }

      if (isNegative) {
        number := -number;
      }

      /* print number, " ";*/
      return Just(number);
    }

    method parse() returns (result: Maybe<(Int32.t, seq<seq<Int32.t>>)>)
      requires valid();
      modifies `cursor;

      ensures result.Just? ==>
        InputPredicate.valid(result.value);
    {
      var variablesCount : Int32.t := 0;
      var clausesCount : Int32.t := 0;
      var clauses : seq<seq<Int32.t>> := [];
      var clause : array<Int32.t> := new Int32.t[1000];
      var clauseLength : Int32.t := 0;
      var ok := false; 
      var literalsCount : Int32.t := 0;

      var contentLength : Int32.t := content.Length as Int32.t;
      while (cursor < contentLength) 
        modifies `cursor, clause;

        invariant 0 <= cursor <= contentLength;
        invariant InputPredicate.checkClauses(variablesCount, clauses);
        invariant InputPredicate.sortedClauses(clauses);
        invariant clause.Length <= Int32.max as int;
        invariant forall z :: 0 <= z < clauseLength ==> (
            (clause[z] < 0 && 0 < -clause[z] <= variablesCount) ||
            (clause[z] > 0 && 0 < clause[z] <= variablesCount));
        invariant forall x, y :: 0 <= x < y < clauseLength ==>
            clause[x] < clause[y]
        invariant ok ==>  0 < variablesCount < Int32.max;
        invariant InputPredicate.countLiterals(clauses) == literalsCount as int;

        decreases contentLength - cursor;
      {
        var oldCursor := cursor;
        if (content[cursor] == 'c') {
          skipLine();
        } else if (content[cursor] == 'p' && variablesCount == 0) {
          toNextNumber();
          var x := extractNumber();
          match x {
            case Error(t) => {
              return Error(t);
            } 
            case Just(number) => {
              if (0 < number < Int32.max) {
                variablesCount := number;
                ok := true;
              } else {
                return Error("Variables count is bigger than Int32.max");
              }
            }
          }
          toNextNumber();
          x := extractNumber();
          match x {
            case Error(t) => {
              return Error(t);
            }
            case Just(number) => {
              clausesCount := number;
              /* print "clausesCount: ", clausesCount, "\n";*/
            }
          }
          skipLine();
        } else if (content[cursor] == 'p') {
          return Error ("Twice p? what are you doing?");
        } else if (ok) {
          toNextNumber();
          /* print clause, "\n";*/
          if (clauseLength == 0 && cursor == contentLength) {
            break;
          }
          var x := extractNumber();
          match x {
            case Error(t) => {
              return Error(t);
            } 
            case Just(number) => {
              if (number == 0 && clauseLength > 0) {
                clauses := clauses + [clause[..clauseLength]];
                if (Int32.max - clauseLength > literalsCount) {
                  literalsCount := literalsCount + clauseLength;
                } else {
                  return Error("The number of literals is to big");
                }
                clauseLength := 0;
                /* print "\n";*/
              } else if (number != 0) {
                if (clauseLength < 1000) {
                  if ((number < 0 && 0 < -number <= variablesCount) ||
                      (number > 0 && 0 < number <= variablesCount)) {
                    clause[clauseLength] := number;
                    clauseLength := clauseLength + 1;
                    var k : Int32.t := clauseLength-1;
                    while (0 < k && clause[k-1] > clause[k]) 
                      modifies clause;
                      invariant 0 <= k <= clauseLength; 
                      invariant forall z :: 0 <= z < clauseLength ==> (
                          (clause[z] < 0 && 0 < -clause[z] <= variablesCount) ||
                          (clause[z] > 0 && 0 < clause[z] <= variablesCount));
                      invariant forall x, y :: 0 <= x < y < clauseLength && x != k && y != k ==>
                          clause[x] < clause[y];
                      invariant forall x, y :: k <= x < y < clauseLength ==>
                          clause[x] < clause[y];
                      decreases k;
                    {
                      var aux := clause[k];
                      clause[k] := clause[k-1];
                      clause[k-1] := aux;
                      k := k - 1;
                    }
                    if (k > 0 && clause[k-1] == clause[k]) {
                      return Error("duplice literal in clause");
                    }
                  } else {
                    return Error("literal bigger than variablesCount");
                  }
                } else {
                  return Error("clause longer than 1000");
                }
              }
            }
          }
        }

        if (cursor < contentLength && oldCursor == cursor) {
          cursor := cursor + 1;
        }
      }

      if (!(0 < |clauses| < Int32.max as int)) {
        return Error("number of clauses incorrect");
      }

      if (|clauses| != clausesCount as int) {
        return Error("different number of clauses");
      }
      
      if (ok) {
        return Just((variablesCount, clauses));
      } else {
        return Error("p not found");
      }
    }
  }
}
