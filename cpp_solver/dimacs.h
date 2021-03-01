#ifndef __DIMACS_H
#define __DIMACS_H

#include <istream>

/*
 * Input:
 * is - the stream from which to read the header
 * 
 * Output:
 * n - the number of variables in the problem
 * m - the number of clauses in the problem
 * returns true on success, false on failure
 * 
 * Skips comments and reads the header (number of variables, number of
 * clauses, problem type) of the problem. Checks that the problem is
 * in cnf format.
 */
bool parse_problem_header(std::istream &is, int &n, int &m);

/*
 * Input:
 * is - the stream from which to read the clause
 * n - the number of variables
 * 
 * Output:
 * k - the number of literals in the clause
 * size - the size of the allocated buffer
 * returns a pointer to a newly allocated memory area of at least k ints
 * containing the literals of the clause in DIMACS style
 * 
 * Will read the next clause in the input stream. Returns a buffer
 * with the literals or returns 0 on failure. If the buffer is
 * nonnull, it must be deallocated by the caller.
 */
int *read_next_clause(std::istream &is, int n, int &k, int &size);

#endif
