#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>

using namespace std;

class Formula
{
    int variablesCount;
    int clausesCount;

    int **clauses;

    int decisionLevel;
    
    int *traceVariable;
    bool *traceValue;
    int *traceDLStart;
    int *traceDLEnd;

    int *truthAssignment;
    int *trueLiteralsCount;
    int *falseLiteralsCount;

    int **positiveLiteralsToClauses;
    int **negativeLiteralsToClauses;


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

            int *positivelyImpacted = positiveLiteralsToClauses[variable];
            int *negativelyImpacted = negativeLiteralsToClauses[variable];

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

        int *positivelyImpacted = positiveLiteralsToClauses[variable];
        int *negativelyImpacted = negativeLiteralsToClauses[variable];

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

        int *negativelyImpacted = negativeLiteralsToClauses[variable];
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
      int previous = 0;
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
        bool result = solve();
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
      int minim = 2147483647;
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

      // printf("Decision variable {0}", -result);
      return -result;
    }
  
  public:
    Formula(int varC, int clsC, int **cls) {
        variablesCount = varC;
        clausesCount = clsC;
        clauses = cls;
        
        decisionLevel = -1;
        traceVariable = new int[variablesCount];
        traceValue = new bool[variablesCount];
        traceDLStart = new int[variablesCount];
        traceDLEnd = new int[variablesCount];

        truthAssignment = new int[variablesCount];
        memset(truthAssignment, -1, sizeof(int)*variablesCount);

        trueLiteralsCount = new int[clausesCount];
        memset(trueLiteralsCount, 0, sizeof(int)*clausesCount);
        falseLiteralsCount = new int[clausesCount];
        memset(falseLiteralsCount, 0, sizeof(int)*clausesCount);


        positiveLiteralsToClauses = new int*[variablesCount];
        for (int i = 0; i < variablesCount; ++i) {
            positiveLiteralsToClauses[i] = new int[clausesCount+1];
            memset(positiveLiteralsToClauses[i], 0, sizeof(int)*(clausesCount+1));
        }
        negativeLiteralsToClauses = new int*[variablesCount];
        for (int i = 0; i < variablesCount; ++i) {
            negativeLiteralsToClauses[i] = new int[clausesCount+1];
            memset(negativeLiteralsToClauses[i], 0, sizeof(int)*(clausesCount+1));
        }

        createPositiveNegativeLiteralsToClauses();
    }

    bool solve() {
        if (hasEmptyClauses()) return false;
        if (isEmpty()) return true;

        int literal = chooseLiteral();
        if (step(literal, true)) {
            return true;
        }
        return step(literal, false);
    }
};

int main(int argc, char **argv) 
{
    if (argc != 2) {
      cout << "Syntax: basic_solver <filename.cnf>" << endl;
      return -1;
    }
    if (freopen(argv[1], "r", stdin) == 0) {
      cout << "Syntax: basic_solver <filename.cnf>" << endl;
      cout << "Cannot open " << argv[1] << endl;
      return -1;
    }
      
    int variablesCount = 0;
    int clausesCount = 0;

    clock_t t_start_parse = clock();
    cout << "Parsing SAT problem" << endl;
    if (!parse_problem_header(cin, variablesCount, clausesCount)) {
      cout << "Error reading problem header\n" << endl;
      return -1;
    }

    int **clauses = new int*[clausesCount];

    for (int i = 0; i < clausesCount; ++i) {
      int k;
      int size;
      int *buffer;
      buffer = read_next_clause(cin, variablesCount, k, size);
      if (!buffer) {
        cout << "Error reading clause " << i << endl;
        return -1;
      }
      clauses[i] = new int[k+1];
      clauses[i][0] = k;
      sort(buffer, buffer+k);
      memcpy(clauses[i]+1, buffer, size);
    }
    printf("Time to read: %.2fs\n", (double)(clock() - t_start_parse)/CLOCKS_PER_SEC);

    for (int i = 0; i < clausesCount; ++i) {
      for (int j = 0; j <= clauses[i][0]; ++j) {
        printf("%d ", clauses[i][j]);
      }
      printf("\n");
    }


    t_start_parse = clock();
    Formula formula(variablesCount, clausesCount, clauses);
    printf("Time to initialize: %.2fs\n", (double)(clock() - t_start_parse)/CLOCKS_PER_SEC);

    t_start_parse = clock();
    if (formula.solve()) {
        printf("SAT\n");
    } else {
        printf("UNSAT\n");
    }
    printf("Time to solve: %.2fs\n", (double)(clock() - t_start_parse)/CLOCKS_PER_SEC);

    return 0;
}
