#include "dimacs.h"
#include <sstream>
#include <cstdlib>

using namespace std;

/*
 * Checks whether a line in a DIMACS file should be treated as a comment.
 */
bool is_comment(string line)
{
  return line[0] == 'c';
}

/*
 * Checks whether a line in a DIMACS file contains the problem description.
 */
bool is_problem(string line)
{
  return line[0] == 'p';
}

/*
 * Parses the problem header.
 */
bool parse_problem_header(istream &is, int &n, int &m)
{
  string line;
  while (getline(is, line)) {
    if (is_comment(line)) {
      continue;
    } else {
      break;
    }
  }
  if (!is_problem(line)) {
    return false;
  }
  istringstream iss(line);
  char c;
  string type;
  iss >> c >> type >> n >> m;
  return type == "cnf";
}

/*
 * Parses and returns the next clause in the stream.
 */
int *read_next_clause(istream &is, int n, int &k, int &size)
{
  size = 16;
  int *buffer = (int *)malloc(sizeof(int) * size);
  if (!buffer) {
    return 0;
  }
    
  int literal;
  k = 0;
  while (is >> literal && literal != 0) {
    // validate the literal is in range
    if (literal < -n || literal > n) {
      free(buffer);
      return 0;
    }
    
    // make sure there is room for the next literal
    if (k >= size) {
      size *= 2;
      int *old_buffer = buffer;
      buffer = (int *)realloc(buffer, sizeof(int) * size);
      if (!buffer) {
	free(old_buffer);
	return 0;
      }
    }

    // add the literal to the buffer
    buffer[k++] = literal;
  }
  return buffer;
}
