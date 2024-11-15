#include <X11/Xlib.h>
#include <X11/Xos.h>
#include <X11/Xutil.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NUM_INSTANCES 50
#define VARIABLES_COUNT 70
#define ALPHA_STEPS 40
#define MAX_CLAUSES 400
#define TIME_SCALE 10
#define SAT_K 3

typedef struct sat_literal {
  bool sign;
  int value;
} sat_literal_t;

typedef struct sat_clause {
  sat_literal_t *literals;
  int size;
} sat_clause_t;

typedef struct sat {
  sat_clause_t *clauses;
  int clauses_size;
} sat_t;

bool satDPLL(sat_t *sat, int *assignments, int variables_count);
bool isSatisfied(const sat_t *sat, const int *assignments, int variables_count);
void unitPropagation(sat_t *sat, int *assignments, int variables_count);
bool pureLiteralElimination(sat_t *sat, int *assignments, int variables_count);
int chooseUnassignedVariable(const int *assignments, int variables_count);
void freeSAT(sat_t *sat);

sat_t *generateSAT(int k, int variables_count, int clauses_count) {
  int i, j;
  sat_t *sat = (sat_t *)malloc(sizeof(sat_t));
  sat->clauses_size = clauses_count;
  sat->clauses = (sat_clause_t *)malloc(clauses_count * sizeof(sat_clause_t));

  srand(time(NULL));

  for (i = 0; i < clauses_count; i++) {
    sat_clause_t *clause = &sat->clauses[i];
    clause->size = k;
    clause->literals = (sat_literal_t *)malloc(k * sizeof(sat_literal_t));

    for (j = 0; j < k; j++) {
      clause->literals[j].value = (rand() % variables_count) + 1;
      clause->literals[j].sign = rand() % 2;
    }
  }

  return sat;
}

void printSAT(const sat_t *sat) {
  int i, j;
  printf("%d-SAT: ", sat->clauses_size);
  for (i = 0; i < sat->clauses_size; i++) {
    printf("(");
    const sat_clause_t *clause = &sat->clauses[i];
    for (j = 0; j < clause->size; j++) {
      const sat_literal_t *literal = &clause->literals[j];
      printf("%s%d", literal->sign ? "" : "-", literal->value);
      if (j < sat->clauses_size - 1) {
        printf("V");
      }
    }
    printf(")");
    if (i < sat->clauses_size - 1) {
      printf("^");
    }
  }
  printf("\n");
}

void freeSAT(sat_t *sat) {
  int i;
  for (i = 0; i < sat->clauses_size; i++) {
    free(sat->clauses[i].literals);
  }
  free(sat->clauses);
  free(sat);
}

bool satDPLL(sat_t *sat, int *assignments, int variables_count) {
  if (isSatisfied(sat, assignments, variables_count)) {
    return true;
  }

  unitPropagation(sat, assignments, variables_count);

  if (pureLiteralElimination(sat, assignments, variables_count)) {
    return satDPLL(sat, assignments, variables_count);
  }

  int variable = chooseUnassignedVariable(assignments, variables_count);
  if (variable == -1) {
    return false;
  }

  assignments[variable - 1] = 1;
  if (satDPLL(sat, assignments, variables_count)) {
    return true;
  }

  assignments[variable - 1] = 0;
  if (satDPLL(sat, assignments, variables_count)) {
    return true;
  }

  assignments[variable - 1] = -1;
  return false;
}

bool isSatisfied(const sat_t *sat, const int *assignments,
                 int variables_count) {
  int i, j, value;
  bool clause_satisfied;
  for (i = 0; i < sat->clauses_size; i++) {
    clause_satisfied = false;
    for (j = 0; j < sat->clauses[i].size; j++) {
      sat_literal_t literal = sat->clauses[i].literals[j];
      value = assignments[literal.value - 1];
      if ((value == 1 && literal.sign) || (value == 0 && !literal.sign)) {
        clause_satisfied = true;
        break;
      }
    }
    if (!clause_satisfied) {
      return false;
    }
  }
  return true;
}

void unitPropagation(sat_t *sat, int *assignments, int variables_count) {
  int i, j, unassigned_count, value;
  bool changed, clause_satisfied;
  do {
    changed = false;
    for (i = 0; i < sat->clauses_size; i++) {
      sat_clause_t *clause = &sat->clauses[i];
      unassigned_count = 0;
      clause_satisfied = false;

      for (j = 0; j < clause->size; j++) {
        sat_literal_t literal = clause->literals[j];
        value = assignments[literal.value - 1];
        if ((value == 1 && literal.sign) || (value == 0 && !literal.sign)) {
          clause_satisfied = true;
          break;
        }
        if (value == -1) {
          unassigned_count++;
        }
      }

      if (clause_satisfied) {
        continue;
      }

      if (unassigned_count == 1) {
        for (j = 0; j < clause->size; j++) {
          sat_literal_t literal = clause->literals[j];
          if (assignments[literal.value - 1] == -1) {
            assignments[literal.value - 1] = literal.sign ? 1 : 0;
            changed = true;
            break;
          }
        }
      }
    }
  } while (changed);
}

bool pureLiteralElimination(sat_t *sat, int *assignments, int variables_count) {
  int i, j, index;
  bool changed = false;
  int literal_counts[variables_count * 2];
  memset(literal_counts, 0, sizeof(literal_counts));

  for (i = 0; i < sat->clauses_size; i++) {
    for (j = 0; j < sat->clauses[i].size; j++) {
      sat_literal_t literal = sat->clauses[i].literals[j];
      index = literal.sign ? literal.value - 1
                           : variables_count + literal.value - 1;
      literal_counts[index]++;
    }
  }

  for (i = 0; i < variables_count; i++) {
    if (assignments[i] == -1) {
      if (literal_counts[i] > 0 && literal_counts[variables_count + i] == 0) {
        assignments[i] = 1;
        changed = true;
      } else if (literal_counts[i] == 0 &&
                 literal_counts[variables_count + i] > 0) {
        assignments[i] = 0;
        changed = true;
      }
    }
  }

  return changed;
}

int chooseUnassignedVariable(const int *assignments, int variables_count) {
  int i;
  for (i = 0; i < variables_count; i++) {
    if (assignments[i] == -1) {
      return i + 1;
    }
  }
  return -1;
}

void plotResults(double *alphas, double *satisfiable, double *complexity,
                 int steps) {
  Display *display;
  Window window;
  int screen;
  GC gc;
  XEvent event;
  bool running = true;
  int width, height, margin, graph_width, graph_height, x1, x2, y1, y2, i;

  display = XOpenDisplay(NULL);
  if (display == NULL) {
    fprintf(stderr, "Unable to open X display\n");
    exit(1);
  }

  screen = DefaultScreen(display);
  width = 800;
  height = 600;
  window = XCreateSimpleWindow(display, RootWindow(display, screen), 10, 10,
                               width, height, 1, BlackPixel(display, screen),
                               WhitePixel(display, screen));
  XSelectInput(display, window, ExposureMask | KeyPressMask);
  XMapWindow(display, window);
  gc = XCreateGC(display, window, 0, NULL);

  while (running) {
    XNextEvent(display, &event);

    if (event.type == Expose) {
      XClearWindow(display, window);

      margin = 50;
      graph_width = width - 2 * margin;
      graph_height = height - 2 * margin;

      XDrawLine(display, window, gc, margin, height - margin,
                margin + graph_width, height - margin);
      XDrawLine(display, window, gc, margin, height - margin, margin, margin);

      for (i = 0; i < steps - 1; i++) {
        x1 = margin + i * graph_width / (steps - 1);
        x2 = margin + (i + 1) * graph_width / (steps - 1);
        y1 = height - margin - satisfiable[i] * graph_height / 100.0;
        y2 = height - margin - satisfiable[i + 1] * graph_height / 100.0;

        XSetForeground(display, gc, 0x00FF00);
        XDrawLine(display, window, gc, x1, y1, x2, y2);
      }

      for (i = 0; i < steps - 1; i++) {
        x1 = margin + i * graph_width / (steps - 1);
        x2 = margin + (i + 1) * graph_width / (steps - 1);
        y1 = height - margin - complexity[i] * graph_height / 2.0;
        y2 = height - margin - complexity[i + 1] * graph_height / 2.0;

        XSetForeground(display, gc, 0xFF0000);
        XDrawLine(display, window, gc, x1, y1, x2, y2);
      }

      XSetForeground(display, gc, BlackPixel(display, screen));
      XDrawString(display, window, gc, margin, margin - 10,
                  "k-SAT Phase Transition", 22);
      XDrawString(display, window, gc, margin + graph_width / 2,
                  height - margin + 20, "Alpha (Clauses/Variables)", 26);
      XDrawString(display, window, gc, 10, margin, "Percentage/Complexity", 22);
    } else if (event.type == KeyPress) {
      char key;
      KeySym keysym;
      XLookupString(&event.xkey, &key, 1, &keysym, NULL);

      if (key == 'q' || key == 'Q') {
        running = false;
      }
    }
  }

  XFreeGC(display, gc);
  XDestroyWindow(display, window);
  XCloseDisplay(display);
}

int main() {
  double alphas[ALPHA_STEPS];
  double satisfiable[ALPHA_STEPS];
  double complexity[ALPHA_STEPS];
  int step, i, j, clauses_count, sat_count;
  int assignments[VARIABLES_COUNT];

  for (step = 0; step < ALPHA_STEPS; step++) {
    clauses_count = (step + 1) * MAX_CLAUSES / ALPHA_STEPS;
    alphas[step] = (double)clauses_count / VARIABLES_COUNT;

    sat_count = 0;
    double total_time = 0.0;

    for (i = 0; i < NUM_INSTANCES; i++) {
      sat_t *sat = generateSAT(SAT_K, VARIABLES_COUNT, clauses_count);

      for (j = 0; j < VARIABLES_COUNT; j++) {
        assignments[j] = -1;
      }

      clock_t start = clock();
      bool result = satDPLL(sat, assignments, VARIABLES_COUNT);
      clock_t end = clock();
      total_time += (double)(end - start) / CLOCKS_PER_SEC;

      if (result) {
        sat_count++;
      }

      freeSAT(sat);
    }

    satisfiable[step] = (double)sat_count / NUM_INSTANCES * 100.0;
    complexity[step] = total_time / NUM_INSTANCES * TIME_SCALE;
  }

  plotResults(alphas, satisfiable, complexity, ALPHA_STEPS);

  return 0;
}
