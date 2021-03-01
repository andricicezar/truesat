include "int32.dfy"
include "solver/solver.dfy"
include "input.dfy"
include "my_datatypes.dfy"
include "input_predicate.dfy"

method Main() 
  decreases *;
{
  var starttime := Input.getTimestamp();
  var input := Input.getInput();
  var totalTime : real := ((Input.getTimestamp()-starttime) as real)/1000.0;
  print "Time to read: ", totalTime, "s\n";

  match input {
    case Error(m) => print "Error: ", m, "\n";
    case Just(z) =>
      var (variablesCount, clauses) := z;
      starttime := Input.getTimestamp();
      var formula := new Formula(variablesCount, clauses);
      var solver := new SATSolver(formula);
      totalTime  := ((Input.getTimestamp()-starttime) as real)/1000.0;
      print "Time to initialize: ", totalTime, "s\n";

      starttime := Input.getTimestamp();
      var solution := solver.start();
      totalTime := ((Input.getTimestamp()-starttime) as real)/1000.0;
      print "Time to solve: ", totalTime, "s\n";

      match solution {
        case SAT(x) => print "Result:SAT\n";
        case UNSAT => print "Result:UNSAT\n";
      }
  }
}
