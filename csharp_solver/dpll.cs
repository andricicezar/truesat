using System;
using System.IO;
using System.Diagnostics;

namespace satsolver 
{
    class Formula
    {
        private int variablesCount;
        private int clausesCount;

        private int[][] clauses;

        private int decisionLevel;
        
        private int[] traceVariable;
        private bool[] traceValue;
        private int[] traceDLStart;
        private int[] traceDLEnd;

        private int[] truthAssignment;
        private int[] trueLiteralsCount;
        private int[] falseLiteralsCount;

        private int[][] positiveLiteralsToClauses;
        private int[][] negativeLiteralsToClauses;

        public Formula(int varC, int clsC, int[][] cls) {
            variablesCount = varC;
            clausesCount = clsC;
            clauses = cls;
            
            decisionLevel = -1;
            traceVariable = new int[variablesCount];
            traceValue = new bool[variablesCount];
            traceDLStart = new int[variablesCount];
            traceDLEnd = new int[variablesCount];

            truthAssignment = new int[variablesCount];
            Array.Fill(truthAssignment, -1);

            trueLiteralsCount = new int[clausesCount];
            Array.Fill(trueLiteralsCount, 0);
            falseLiteralsCount = new int[clausesCount];
            Array.Fill(falseLiteralsCount, 0);


            positiveLiteralsToClauses = new int[variablesCount][];
            for (int i = 0; i < variablesCount; ++i) {
                positiveLiteralsToClauses[i] = new int[clausesCount+1];
                Array.Fill(positiveLiteralsToClauses[i], 0);
            }
            negativeLiteralsToClauses = new int[variablesCount][];
            for (int i = 0; i < variablesCount; ++i) {
                negativeLiteralsToClauses[i] = new int[clausesCount+1];
                Array.Fill(negativeLiteralsToClauses[i], 0);
            }

            createPositiveNegativeLiteralsToClauses();
        }

        void createPositiveNegativeLiteralsToClauses() {
            for (int i = 0; i < clausesCount; ++i) {
                for (int j = 1; j <= clauses[i][0]; ++j) {
                    if (clauses[i][j] > 0) {
                        positiveLiteralsToClauses
                            [clauses[i][j]-1]
                            [++positiveLiteralsToClauses[clauses[i][j]-1][0]] = i;
                    } else if (clauses[i][j] < 0) {
                        negativeLiteralsToClauses
                            [-clauses[i][j]-1]
                            [++negativeLiteralsToClauses[-clauses[i][j]-1][0]] = i;
                    }
                }
            }
        }

        void revertLastDecisionLevel() {
            while (traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]) {
                int k = traceDLEnd[decisionLevel] - 1;
                int variable = traceVariable[k];
                bool value = traceValue[k];
                truthAssignment[variable] = -1;
                traceDLEnd[decisionLevel] = k;

                int[] positivelyImpacted = positiveLiteralsToClauses[variable];
                int[] negativelyImpacted = negativeLiteralsToClauses[variable];

                if (!value) {
                    negativelyImpacted = positiveLiteralsToClauses[variable];
                    positivelyImpacted = negativeLiteralsToClauses[variable];
                }

                for (int i = 1; i <= positivelyImpacted[0]; ++i)
                    trueLiteralsCount[positivelyImpacted[i]] -= 1;
                for (int i = 1; i <= negativelyImpacted[0]; ++i)
                    falseLiteralsCount[negativelyImpacted[i]] -= 1;
            }

            decisionLevel -= 1;
        }

        void setVariable(int variable, bool value) {
            traceVariable[traceDLEnd[decisionLevel]] = variable;
            traceValue[traceDLEnd[decisionLevel]] = value;
            traceDLEnd[decisionLevel] += 1;

            truthAssignment[variable] = value ? 1 : 0;

            int[] positivelyImpacted = positiveLiteralsToClauses[variable];
            int[] negativelyImpacted = negativeLiteralsToClauses[variable];

            if (!value) {
                negativelyImpacted = positiveLiteralsToClauses[variable];
                positivelyImpacted = negativeLiteralsToClauses[variable];
            }

            for (int i = 1; i <= positivelyImpacted[0]; ++i)
                trueLiteralsCount[positivelyImpacted[i]] += 1;
            for (int i = 1; i <= negativelyImpacted[0]; ++i)
                falseLiteralsCount[negativelyImpacted[i]] += 1;
        }

        int getVariableFromLiteral(int literal) {
          return (literal < 0) ? -literal-1 : literal-1;
        }

        void setLiteral(int literal, bool value) {
            int variable = getVariableFromLiteral(literal); 
            value = (literal < 0) ? !value : value;
            setVariable(variable, value);

            int[] negativelyImpacted = negativeLiteralsToClauses[variable];
            if (!value) {
              negativelyImpacted = positiveLiteralsToClauses[variable];
            }

            for (int i = 1; i <= negativelyImpacted[0]; ++i) {
                if (clauses[negativelyImpacted[i]][0] - 1 == falseLiteralsCount[negativelyImpacted[i]]
                    && trueLiteralsCount[negativelyImpacted[i]] == 0) {
                    for (int j = 1; j <= clauses[negativelyImpacted[i]][0]; ++j) {
                        int literal_l = clauses[negativelyImpacted[i]][j];
                        int variable_l = (literal_l < 0) ? -literal_l-1 : literal_l-1;
                        if (truthAssignment[variable_l] == -1) {
                            setLiteral(literal_l, true);
                            break;
                        }
                    }
                }
            }
        }

        void increaseDecisionLevel() {
          decisionLevel = decisionLevel + 1;
          var previous = 0;
          if (decisionLevel == 0) {
            previous = 0;
          } else {
            previous = traceDLEnd[decisionLevel-1];
          }

          traceDLStart[decisionLevel] = previous;
          traceDLEnd[decisionLevel] = previous;
        }

        bool step(int literal, bool value) {
            increaseDecisionLevel();
            setLiteral(literal, value);
            bool result = solve_loop();
            revertLastDecisionLevel();
            return result;
        }

        bool hasEmptyClauses() {
            for (int i = 0; i < clausesCount; ++i)
                if (clauses[i][0] == falseLiteralsCount[i])
                    return true;

            return false;
        }
        
        bool isEmpty() {
            for (int i = 0; i < clausesCount; ++i)
                if (trueLiteralsCount[i] == 0)
                    return false;

            return true;
        }

        int chooseLiteral() {
          int minim = Int32.MaxValue;
          int counter = 0;
          int result = -1;

          for (int cI = 0; cI < clausesCount; ++cI) {
            int diff = clauses[cI][0] - falseLiteralsCount[cI];

            if (trueLiteralsCount[cI] == 0 && diff < minim) {
              minim = diff;
            }

            if (trueLiteralsCount[cI] == 0 && diff == minim) {
              for (int lI = 1; lI <= clauses[cI][0]; ++lI) {
                int variable = getVariableFromLiteral(clauses[cI][lI]);
                if (truthAssignment[variable] == -1) {
                  if (counter == 0) {
                    result = variable+1;
                    counter = counter + 1;
                  } else if (result == variable+1) {
                    counter = counter + 1;
                  } else {
                    counter = counter - 1;
                  }
                }
              }
            }
          }

          Debug.Assert(truthAssignment[result-1] == -1);
          // Console.WriteLine("Decision variable {0}", -result);
          return -result;
        }

        public bool solve_loop() {
            if (hasEmptyClauses()) return false;
            if (isEmpty()) return true;

            int literal = chooseLiteral();
            if (step(literal, true)) {
                return true;
            }
            return step(literal, false);
        }

        public bool solve() {
          for (int i = 0; i < clausesCount; ++i) {
            if (clauses[i][0] == 1 && truthAssignment[getVariableFromLiteral(clauses[i][1])] == -1) {
              setLiteral(clauses[i][1], true);
            }
          }

          return solve_loop();
        }
    }

    class SATSolver 
    {
        static int Main(string[] args) 
        {
            Console.WriteLine("c Starting...");
            Console.WriteLine("c Notice! There is a hard-coded 7000 limit for the clauses count. Please increase this number for larger test cases.");

            if (args.Length == 0) {
                System.Console.WriteLine("Please enter a path.");
                return 1;
            }

            long tl = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            Console.WriteLine(args[0]);
            
            int variablesCount = 0;
            int clausesCount = 0;
            int[][] clauses = new int[7000][];
            int currentClause = 0;

            // inspired from https://github.com/helium729/heliSAT-legacy
            StreamReader reader = new StreamReader(args[0]);
            while (!reader.EndOfStream) {
              var line = reader.ReadLine();
              if (line == "")
                continue;
              else if (line == "%")
                  break;
              var splited = line.Split(" ", StringSplitOptions.RemoveEmptyEntries);
              if (splited[0] == "c")
                continue;
              else if (splited[0] == "p") {
                variablesCount = Convert.ToInt32(splited[2]);
                clauses[0] = new int[variablesCount*2+1];
                Array.Fill(clauses[0], 0);
                clausesCount = Convert.ToInt32(splited[3]);
                continue;
              } else {
                foreach (var a in splited) {
                  if (a == "0") {     
                    ++currentClause;
                    clauses[currentClause] = new int[variablesCount*2+1];
                    Array.Fill(clauses[currentClause], 0);
                    // Console.WriteLine("Clause: [{0}]", string.Join(", ", clauses[currentClause]));
                    break;
                  }
                  int temp = Convert.ToInt32(a);
                  int[] clause = clauses[currentClause];
                  clause[++clause[0]] = temp;
                  int k = clause[0];
                  while (1 < k && clause[k-1] > clause[k]) {
                      int aux = clause[k];
                      clause[k] = clause[k-1];
                      clause[k-1] = aux;
                      k = k - 1;
                  }
                }
              }
            }
            long tlf = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            Console.WriteLine("c Time to read: {0}s", ((double)tlf-tl)/1000.0);

            // for (int i = 0; i < clausesCount; ++i) {
            //   for (int j = 0; j <= clauses[i][0]; ++j) {
            //     Console.Write("{0} ", clauses[i][j]);
            //   }
            //   Console.Write("\n");
            // }

            tl = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            Formula formula = new Formula(variablesCount, clausesCount, clauses);
            tlf = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            Console.WriteLine("c Time to initialize: {0}s", ((double)tlf-tl)/1000.0);

            tl = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            if (formula.solve()) {
                Console.WriteLine("s SATISFIABLE");
            } else {
                Console.WriteLine("s UNSATISFIABLE");
            }
            tlf = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();

            Console.WriteLine("c Time to solve: {0}s", ((double)tlf-tl)/1000.0);

            return 0;
        }
    }
}
