// clang-format off

const char *usage =
"usage: babysat [ <option> ... ] [ <dimacs> ]\n"
"\n"
"where '<option>' can be one of the following\n"
"\n"
"  -h | --help        print this command line option summary\n"
#ifdef LOGGING
"  -l | --logging     print very verbose logging information\n"
#endif
"  -q | --quiet       do not print any messages\n"
"  -n | --no-witness  do not print witness if satisfiable\n"
"  -v | --verbose     print verbose messages\n"
"  -p | --proof       print proof to <stdout>\n"
"\n"
"and '<dimacs>' is the input file in DIMACS format.  The solver\n"
"reads from '<stdin>' if no input file is specified.\n";

// clang-format on

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

// Global options accesible through the command line.

static bool witness = true;
static bool proof = false;

static int verbosity; // -1=quiet, 0=normal, 1=verbose, INT_MAX=logging

struct clause {
  unsigned id; // For debugging and sorting.
  unsigned size;
  unsigned counts; // Counter for propagation.
  int literals[];

  // The following two functions allow simple ranged-based for-loop
  // iteration over clause literals with the following idiom:
  //
  //   clause * c = ...
  //   for (auto lit : *c)
  //     do_something_with (lit);
  //
  int *begin () { return literals; }
  int *end () { return literals + size; }
};

static int variables;
static std::vector<clause *> clauses;
// Access clauses by literals for propagation.
static std::vector<clause *> *watches;
static clause *empty_clause;

static signed char *values;

static std::vector<int> trail;
static unsigned *levels;  // Mapping variables to decision level.
static clause **reasons;  // Mapping variables to reason clauses (0 = decision).
static bool *marks;       // Marking structure for conflict analysis.

static std::vector<int> learned; // learned lits
static std::vector<int> seen;    // tracks every marked variable index

static std::vector<unsigned> control;

static unsigned level;
static unsigned propagated;

// Statistics
static size_t conflicts;
static size_t decisions;
static size_t propagations;
static size_t added;

static size_t reports;

static bool iterating;
static int fixed;

// Generates nice compiler warnings if format string does not fit arguments.

static void message (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));
static void die (const char *, ...) __attribute__ ((format (printf, 1, 2)));

static void parse_error (const char *fmt, ...)
    __attribute__ ((format (printf, 1, 2)));

#ifdef LOGGING

static void debug (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void debug (clause *, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static bool logging () { return verbosity == INT_MAX; }

// Print debugging message if '--debug' is used.  This is only enabled
// if the solver is configured with './configure --logging' (which is the
// default for './configure --debug').  Even if logging code is included
// this way, it still needs to be enabled at run-time through '-l'.

static char debug_buffer[4][32];
static size_t next_debug_buffer;

// Get a statically allocate string buffer (of size 32 bytes).
// Used here only for printing literals.

static char *debug_string (void) {
  char *res = debug_buffer[next_debug_buffer++];
  if (next_debug_buffer == sizeof debug_buffer / sizeof *debug_buffer)
    next_debug_buffer = 0;
  return res;
}

static char *debug (int lit) {
  if (!logging ())
    return 0;
  char *res = debug_string ();
  sprintf (res, "%d", lit);
  int value = values[lit];
  if (value)
    sprintf (res + strlen (res), "@%u=%d", levels[abs (lit)], value);
  assert (strlen (res) <= sizeof debug_buffer[0]);
  return res;
}

static void debug_prefix (void) { printf ("c DEBUG %u ", level); }

static void debug_suffix (void) {
  fputc ('\n', stdout);
  fflush (stdout);
}

static void debug (const char *fmt, ...) {
  if (!logging ())
    return;
  debug_prefix ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  debug_suffix ();
}

static void debug (clause *c, const char *fmt, ...) {
  if (!logging ())
    return;
  debug_prefix ();
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  printf (" size %u count %u clause[%u]", c->size, c->counts, c->id);
  for (auto lit : *c)
    printf (" %s", debug (lit));
  debug_suffix ();
}

#else

#define debug(...) \
  do { \
  } while (0)

#endif

// Print message to '<stdout>' and flush it.

static void message (const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void line () {
  if (verbosity < 0)
    return;
  fputs ("c\n", stdout);
  fflush (stdout);
}

static void verbose (const char *fmt, ...) {
  if (verbosity <= 0)
    return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

// Print error message and 'die'.

static void die (const char *fmt, ...) {
  fprintf (stderr, "babysat: error: ");
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void initialize (void) {
  assert (variables < INT_MAX);
  unsigned size = variables + 1;

  unsigned twice = 2 * size;

  values = new signed char[twice];
  levels = new unsigned[size];
  reasons = new clause *[size];
  marks = new bool[size];
  watches = new std::vector<clause *>[twice];

  // We subtract 'variables' in order to be able to access
  // the arrays with a negative index (valid in C/C++).

  watches += variables;
  values += variables;

  for (int lit = -variables; lit <= variables; lit++)
    values[lit] = 0;

  for (int idx = 1; idx <= variables; idx++) {
    levels[idx] = 0;
    reasons[idx] = 0;
    marks[idx] = false;
  }

  assert (!propagated);
  assert (!level);
}

static clause pseudo_reason;
static clause *decision_reason = 0;
static clause *flipped_decision = &pseudo_reason;

static void delete_clause (clause *clause) {
  assert (clause != decision_reason);
  assert (clause != flipped_decision);
  debug (clause, "delete");
  delete[] clause;
}

static void release (void) {
  for (auto clause : clauses)
    delete_clause (clause);

  watches -= variables;
  values -= variables;

  delete[] watches;
  delete[] values;

  delete[] levels;
  delete[] reasons;
  delete[] marks;
}

static bool falsified (clause *c) {
  for (auto lit : *c)
    if (values[lit] >= 0)
      return false;
  return true;
}
static bool satisfied (clause *c) {
  for (auto lit : *c)
    if (values[lit] > 0)
      return true;
  return false;
}

static void assign (int lit, clause *reason) {
  int idx = abs (lit);
  levels[idx] = level;
  reasons[idx] = reason;   // 0 (decision_reason) for decisions, clause* for implications
  fixed += !level;
  iterating = !level;
#ifdef LOGGING
  if (logging ()) {
    if (reason == decision_reason)
      debug ("assign %s as decision", debug (lit));
    else if (reason == flipped_decision)
      debug ("assign %s as flipped decision", debug (lit));
    else
      debug (reason, "assign %s with reason", debug (lit));
  }
#endif
  assert (!values[lit]);
  assert (!values[-lit]);
  values[lit] = 1;
  values[-lit] = -1;
  trail.push_back (lit);
}

static void watch_literal (int lit, struct clause *c) {
  debug (c, "watching %s in", debug (lit));
  watches[lit].push_back (c);
}

static clause *add_clause (std::vector<int> &literals) {

  // First allocate clause and copy literals.

  size_t size = literals.size ();
  size_t bytes = sizeof (struct clause) + size * sizeof (int);
  clause *c = (clause *) new char[bytes];

  assert (size <= UINT_MAX);
  c->id = added++;

  assert (clauses.size () <= (size_t) INT_MAX);
  c->size = size;


  c->counts = size;

  int *q = c->literals;
  for (auto lit : literals)
    *q++ = lit;

  debug (c, "new");

  // Save it on global stack of clauses.

  clauses.push_back (c);

  // Connect the clause in any case.

  if (size > 1) {
    for (auto lit : *c)
      watch_literal (lit, c);
  }

  // Handle the special case of empty and unit clauses.

  if (!size) {
    debug (c, "parsed empty clause");
    empty_clause = c;
  } else if (size == 1) {
    int unit = literals[0];
    signed char value = values[unit];
    if (!value)
      assign (unit, c);
    else if (value < 0) {
      debug (c, "inconsistent unit clause");
      empty_clause = c;
    }
  }

  return c;
}

static const char *file_name;
static bool close_file;
static FILE *file;

static void parse_error (const char *fmt, ...) {
  fprintf (stderr, "babysat: parse error in '%s': ", file_name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void parse (void) {
  int ch;
  while ((ch = getc (file)) == 'c') {
    while ((ch = getc (file)) != '\n')
      if (ch == EOF)
        parse_error ("end-of-file in comment");
  }
  if (ch != 'p')
    parse_error ("expected 'c' or 'p'");
  int clauses;
  if (fscanf (file, " cnf %d %d", &variables, &clauses) != 2 ||
      variables < 0 || variables >= INT_MAX || clauses < 0 ||
      clauses >= INT_MAX)
    parse_error ("invalid header");
  message ("parsed header 'p cnf %d %d'", variables, clauses);
  initialize ();
  std::vector<int> clause;
  int lit = 0, parsed = 0;
  while (fscanf (file, "%d", &lit) == 1) {
    if (parsed == clauses)
      parse_error ("too many clauses");
    if (lit == INT_MIN || abs (lit) > variables)
      parse_error ("invalid literal '%d'", lit);
    if (lit)
      clause.push_back (lit);
    else {
      add_clause (clause);
      clause.clear ();
      parsed++;
    }
  }

  if (lit)
    parse_error ("terminating zero missing");

  if (parsed != clauses)
    parse_error ("clause missing");

  if (close_file)
    fclose (file);
}

// TODO: in debug mode check that counters are correct.
// It should throw an error when it fails (i.e. die (...))
static void check_counts (clause *c) 
{
  unsigned expected = 0;
  for(auto lit: *c)
  {
    if(values[lit] >= 0)
    {
      expected++;
    }
  }

  if(c->counts != expected)
  {
    fprintf(stderr, "clause[%u] lits:", c->id);
    for (auto lit : *c)
      fprintf(stderr, " %d(val=%d,lv=%u)", lit, (int)values[lit], levels[abs(lit)]);
    fprintf(stderr, "\n");
    die("clause[%u]: count %u (expected %u)", c->id, c->counts, expected);
  }

}

static clause *propagate (void) 
{
  clause *conflict = 0;

  while (!conflict && propagated != trail.size ()) 
  {
    // Whu exactly not_lit?
    int not_lit = -trail[propagated++];
    debug ("propagating %s", debug (-not_lit));
    propagations++;

    auto &not_lit_clauses = watches[not_lit];
 
    // Wisiting all clauses where negation of a literal occures
    for (auto clause : not_lit_clauses) {
      // TODO: what do we do with the clauses
      // containing -lit? Can we stop when we
      // reach a conflict?
    
      // Based on slide 80
      // clause.count = number of literals assigned to FALSE.
      assert (clause->counts > 0);
      clause->counts--;
      debug (clause, "decremented count of");

      // If counts = 0 then the clause if falsified by the assignment
      if(!clause->counts)
      {
        conflict = clause;
      }

      // If counts = 1 then there is exactly 1 unassigned literal in the clause. 
      // Go through the clause, find it and assign it to TRUE.
      else if(clause->counts == 1)
      {
        for(auto lit: *clause)
        {
          if(!values[lit])
          {
            assign(lit, clause);
            break;
          }
        }
      }
    }
  }

  if (conflict) {
    debug (conflict, "conflicting");
    assert (falsified (conflict));
    conflicts++;
  }

  #ifndef NDEBUG
    else
      for (auto c : clauses)
        check_counts (c);
  #endif

  return conflict;
}

static int decide (void) {
  decisions++;

  int decision = 0;

  while (values[++decision])
    ;

  debug ("decision %s", debug (decision));

  assert (level == control.size ());
  control.push_back (trail.size ());

  level++;

  return decision;
}

static void unassign (int lit, bool increase_counter) {
  debug ("unassign %s", debug (lit));
  assert (values[lit] > 0);
  assert (values[-lit] < 0);
  values[lit] = values[-lit] = 0;
  if (!increase_counter)
    return;

  // TODO: update counts inside of clauses.
  // watches[-lit] is basically a list of occurrences
  // of -lit.

  // Increasing counter = unassigning 
  // (changing decrease to increase makes more sense imo)
  for(auto c: watches[-lit])
  {
    c->counts++;
  }
}

static void backjump (unsigned jump) {
  assert (jump < level);

  debug ("backtracking to level %u", jump);

  // Pop control stack down to the jump level.
  while (control.size () > jump) {
    size_t previous = control.back ();
    control.pop_back ();

    while (trail.size () > previous) {
      int lit = trail.back ();
      assert (levels[abs (lit)] > jump);
      trail.pop_back ();
      
      // Is true when the the literal had already been processed through
      // the propagation queue. Otherwise it's false, which means that
      // the literal was put on the trail but propagated hadn;t reached it yet
      // (it's assignment never decr. any counts, so the unassignment must not increment them)
      bool increase_counter = (trail.size() < propagated);
      unassign (lit, increase_counter);
    }
  }

  level = jump;
  if (propagated > trail.size ())
    propagated = trail.size ();
  assert (level == jump);
}

static void process_conflict(clause *conflict, std::vector<int> &seen, int &lit_on_curr_level, std::vector<int> &learned)
{
  unsigned idx;
  unsigned literal_level;
  
  for (auto lit : *conflict) {

    //int idx = abs (lit);
    idx = abs(lit);

    // avoid already seen variables (double counting)
    if (marks[idx])
    {
      continue; 
    }

    marks[idx] = true;
    seen.push_back(idx);  // remember for cleanup
    literal_level = levels[idx];
    
    // needs to be resolved, since it came from the current level
    if (literal_level == level)
    {
      lit_on_curr_level++;
    }
    else if (literal_level > 0)
    {
      learned.push_back (lit); // Literals which will form the learned clause ( \lnot uip \lor learned)
    }

      // lv == 0 unit - ignore
    }
}

// CDCL: traverse the implication graph to derive the
// 1-UIP learned clause, add it, then backjump and assign
static bool backjump_and_flip (clause *conflict) {

  seen.clear();
  learned.clear();
  // If we've found conflict at level 0 return
  if (!level)
    return false;

  int lit_on_curr_level = 0;
  int uip = 0;

  // 
  process_conflict(conflict, seen, lit_on_curr_level, learned);

  // walk the trail backwards
  int trail_idx = trail.size () - 1;
  while (lit_on_curr_level > 0) {
    // find the next marked literal on the trail (at current level)
    while (!marks[abs (trail[trail_idx])])
    {
      trail_idx--;
    }

    uip = trail[trail_idx]; // pick current UIP candidate
    trail_idx--; 
    lit_on_curr_level--;

    if (!lit_on_curr_level)
      break; // 1-UIP was found


    clause *r = reasons[abs (uip)]; // Get reason of the current UIP candidate
    assert (r != decision_reason);  // must be an implication, not a decision
    
    // We haven't found 1-UIP so continue resolving
    process_conflict(r, seen, lit_on_curr_level, learned); // add other literals of that clause 
    // (all except the UIP candidate, since we are RESOLVING on it)
  }


  // Find backjump level (max level among non uip literals)
  unsigned jump_level = 0;
  for (auto lit : learned) {
    if (levels[abs(lit)] > jump_level)
    {
      jump_level = levels[abs (lit)];
    }
  }

  // The learned clause
  // -uip will be the unit propagated after backjump.
  learned.push_back (-uip);

  if (proof) {
    for (auto lit : learned)
      printf ("%d ", lit);
    printf ("0\n");
  }

  for (int idx : seen)
  {
    marks[idx] = false;
  }
  
  // backjump to the new level
  backjump(jump_level);

  // Add learned clause to CNF
  clause *learned_clause = add_clause (learned);
  learned_clause->counts = 1;

  // Check if add_clause assigned -uip (learned clause has < 2 lit)
  // if not assign it now
  if (!values[-uip])
  {
    assign (-uip, learned_clause);
  }


  return true;
}

static double process_time (void);

static void report (char type) {
  if (verbosity < 0)
    return;
  if (!(reports++ % 20)) {
    verbose ("");
    verbose ("          conflicts       variables");
    verbose ("    seconds        clauses     remaining");
    verbose ("");
  }
  int remaining = variables - fixed;
  verbose ("%c %7.2f %7zu %7zu %7d %3.0f%%", type, process_time (),
           conflicts, clauses.size (), remaining,
           variables ? 100.0 * remaining / variables : 0);
}

// Return value of '10' is the exit code for 'satisfiable' formula and '20'
// is the exit code for 'unsatisfiable' formula in the SAT competition.

// We use the same encoding for the return value of the 'solve' routine.
// Any other value (like '0') is considered 'unknown' and ignored.

static const int satisfiable = 10;
static const int unsatisfiable = 20;

static int cdcl (void) {
  for (;;) {
    
    clause *conflict = propagate();
    
    if (conflict) 
    {
      // If conflict is reached we want to
      // backtrack and try another direction (=flip)
      if (!backjump_and_flip(conflict))
        return unsatisfiable;
      continue;
    }
    
    if (iterating)
      iterating = false, report ('i');

    // All variables are assigned
    if (trail.size () == (size_t) variables)
      return satisfiable;
    
    // If there is no conflict and not all variables are
    // assigned proceed with the next variable
    int lit = decide ();
    assign (lit, decision_reason);
  }
}

static int solve (void) {
  if (empty_clause)
    return unsatisfiable;
  return cdcl ();
}

// Checking the model on the original formula is extremely useful for
// testing and debugging.  This 'checker' aborts if an unsatisfied clause is
// found and prints the clause on '<stderr>' for debugging purposes.

static void check_model (void) {
  debug ("checking model");
  for (auto clause : clauses) {
    if (satisfied (clause))
      continue;
    fputs ("babysat: unsatisfied clause:\n", stderr);
    for (auto lit : *clause)
      fprintf (stderr, "%d ", lit);
    fputs ("0\n", stderr);
    fflush (stderr);
    abort ();
    exit (1);
  }
}

// Printing the model in the format of the SAT competition, e.g.,
//
//   v -1 2 3 0
//
// Always prints a full assignments even if not all values are set.

static void print_model (void) {
  printf ("v ");
  for (int idx = 1; idx <= variables; idx++) {
    if (values[idx] < 0)
      printf ("-");
    printf ("%d ", idx);
  }
  printf ("0\n");
}

// Get process-time of this process.  This is not portable to Windows but
// should work on other Unixes such as MacOS as is.

#include <sys/resource.h>
#include <sys/time.h>

static double process_time (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// The main function expects at most one argument which is then considered
// as the path to a DIMACS file. Without argument the solver reads from
// '<stdin>' (the standard input connected for instance to the terminal).

static void print_statistics () {
  printf ("c %-30s %16zu\n", "conflicts:", conflicts);
  printf ("c %-30s %16zu\n", "decisions:", decisions);
  printf ("c %-30s %16zu\n", "propagations:", propagations);
  printf ("c %-30s %16.2f seconds\n", "process-time:", process_time ());
}

#include "config.hpp"

int main (int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h") || !strcmp (arg, "--help")) {
      fputs (usage, stdout);
      exit (0);
    } else if (!strcmp (arg, "-l") || !strcmp (arg, "--logging"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die ("compiled without logging code (use './configure --logging')");
#endif
    else if (!strcmp (arg, "-q") || !strcmp (arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp (arg, "-v") || !strcmp (arg, "--verbose"))
      verbosity = 1;
    else if (!strcmp (arg, "-n") || !strcmp (arg, "--no-witness"))
      witness = false;
    else if (!strcmp (arg, "-p") || !strcmp (arg, "--proof"))
      proof = true;
    else if (arg[0] == '-')
      die ("invalid option '%s' (try '-h')", arg);
    else if (file_name)
      die ("too many arguments '%s' and '%s' (try '-h')", file_name, arg);
    else
      file_name = arg;
  }

  if (!file_name) {
    file_name = "<stdin>";
    assert (!close_file);
    file = stdin;
  } else if (!(file = fopen (argv[1], "r")))
    die ("could not open and read '%s'", file_name);
  else
    close_file = true;

  message ("BabySAT CDCl SAT Solver");
  line ();
  message ("Copyright (c) 2022-2023, Armin Biere, University of Freiburg");
  message ("Version %s %s", VERSION, GITID);
  message ("Compiled with '%s'", BUILD);
  line ();
  message ("reading from '%s'", file_name);

  parse ();
  report ('*');

  int res = solve ();
  report (res == 10 ? '1' : res == 20 ? '0' : '?');
  line ();

  if (res == 10) {
    check_model ();
    printf ("s SATISFIABLE\n");
    if (witness)
      print_model ();
  } else if (res == 20)
    printf ("s UNSATISFIABLE\n");

  release ();

  if (verbosity >= 0)
    line (), print_statistics (), line ();

  message ("exit code %d", res);

  return res;
}
