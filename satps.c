#include <GL/glut.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define VARIABLES_COUNT 50
#define SAT_K 3
#define MAX_CLAUSES 500
#define ALPHA_STEPS 50
#define NUM_INSTANCES 10

double alphas[ALPHA_STEPS];
double satisfiable[ALPHA_STEPS];
double complexity[ALPHA_STEPS];
double max_complexity = 0.0;

typedef int sat_literal_value_t;
typedef bool sat_literal_sign_t;

typedef struct sat_literal {
  sat_literal_sign_t sign;
  sat_literal_value_t value;
} sat_literal_t;

typedef struct sat_clause {
  sat_literal_t *literals;
  int literals_count;
} sat_clause_t;

typedef struct sat {
  sat_clause_t *clauses;
  int clauses_count;
  int variables_count;
} sat_t;

sat_t *generate_k_sat(int k, int variables_count, int clauses_count) {
  int i, j;
  sat_t *formula = (sat_t *)malloc(sizeof(sat_t));
  formula->clauses =
      (sat_clause_t *)malloc(clauses_count * sizeof(sat_clause_t));
  formula->clauses_count = clauses_count;
  formula->variables_count = variables_count;
  for (i = 0; i < clauses_count; i++) {
    formula->clauses[i].literals_count = k;
    formula->clauses[i].literals =
        (sat_literal_t *)malloc(k * sizeof(sat_literal_t));
    for (j = 0; j < k; j++) {
      formula->clauses[i].literals[j].value = rand() % variables_count;
      formula->clauses[i].literals[j].sign = rand() % 2;
    }
  }
  return formula;
}

sat_t *duplicate(sat_t *formula) {
  int i, j;
  sat_t *copy = (sat_t *)malloc(sizeof(sat_t));
  copy->clauses =
      (sat_clause_t *)malloc(formula->clauses_count * sizeof(sat_clause_t));
  copy->clauses_count = formula->clauses_count;
  copy->variables_count = formula->variables_count;
  for (i = 0; i < formula->clauses_count; i++) {
    copy->clauses[i].literals_count = formula->clauses[i].literals_count;
    copy->clauses[i].literals = (sat_literal_t *)malloc(
        copy->clauses[i].literals_count * sizeof(sat_literal_t));
    for (j = 0; j < copy->clauses[i].literals_count; j++) {
      copy->clauses[i].literals[j].value =
          formula->clauses[i].literals[j].value;
      copy->clauses[i].literals[j].sign = formula->clauses[i].literals[j].sign;
    }
  }
  return copy;
}

void destroy_sat(sat_t *formula) {
  int i;
  for (i = 0; i < formula->clauses_count; i++) {
    free(formula->clauses[i].literals);
  }
  free(formula->clauses);
  free(formula);
}

void print_formula(sat_t *formula) {
  int i, j;
  for (i = 0; i < formula->clauses_count; i++) {
    printf("(");
    for (int j = 0; j < formula->clauses[i].literals_count; j++) {
      if (!formula->clauses[i].literals[j].sign)
        printf("¬");
      printf("%d", formula->clauses[i].literals[j].value + 1);
      if (j < formula->clauses[i].literals_count - 1)
        printf(" ∨ ");
    }
    printf(")");
    if (i < formula->clauses_count - 1) {
      printf("^");
      fflush(stdout);
    }
  }
  printf("\n");
}

sat_clause_t *get_unit_clause(sat_t *formula) {
  int i;
  for (i = 0; i < formula->clauses_count; i++) {
    if (formula->clauses[i].literals_count == 1) {
      return &formula->clauses[i];
    }
  }
  return NULL;
}

bool clause_contains(sat_clause_t *clause, sat_literal_value_t value,
                     sat_literal_sign_t sign) {
  for (int i = 0; i < clause->literals_count; i++) {
    if (clause->literals[i].value == value &&
        clause->literals[i].sign == sign) {
      return true;
    }
  }
  return false;
}

void remove_literal(sat_clause_t *clause, sat_literal_value_t value) {
  int new_count = 0;
  for (int i = 0; i < clause->literals_count; i++) {
    if (clause->literals[i].value != value) {
      clause->literals[new_count++] = clause->literals[i];
    }
  }
  clause->literals_count = new_count;
}

void remove_clause(sat_t *formula, int clause_index) {
  free(formula->clauses[clause_index].literals);
  for (int i = clause_index; i < formula->clauses_count - 1; i++) {
    formula->clauses[i] = formula->clauses[i + 1];
  }
  formula->clauses_count--;
}

void add_clause(sat_t *formula, sat_clause_t clause) {
  formula->clauses = (sat_clause_t *)realloc(
      formula->clauses, (formula->clauses_count + 1) * sizeof(sat_clause_t));
  formula->clauses[formula->clauses_count] = clause;
  formula->clauses_count++;
}

void add_literal(sat_clause_t *clause, sat_literal_t literal) {
  clause->literals = (sat_literal_t *)realloc(
      clause->literals, (clause->literals_count + 1) * sizeof(sat_literal_t));
  clause->literals[clause->literals_count] = literal;
  clause->literals_count++;
}

void unit_propagate(sat_t *formula, sat_literal_t unit) {
  for (int i = 0; i < formula->clauses_count;) {
    if (clause_contains(&formula->clauses[i], unit.value, unit.sign)) {
      remove_clause(formula, i);
    } else {
      remove_literal(&formula->clauses[i], unit.value);
      i++;
    }
  }
}

bool is_satisfiable(sat_t *formula) {
  if (formula->clauses_count == 0) {
    return true;
  }
  for (int i = 0; i < formula->clauses_count; i++) {
    if (formula->clauses[i].literals_count == 0) {
      return false;
    }
  }
  return false;
}

bool is_unsatisfiable(sat_t *formula) {
  for (int i = 0; i < formula->clauses_count; i++) {
    if (formula->clauses[i].literals_count == 0) {
      return true;
    }
  }
  return false;
}

sat_literal_t *get_pure_literal(sat_t *formula) {
  int *sign_count = (int *)calloc(formula->variables_count, sizeof(int));
  bool *found = (bool *)calloc(formula->variables_count, sizeof(bool));
  sat_literal_t *pure_literal = NULL;

  for (int i = 0; i < formula->clauses_count; i++) {
    for (int j = 0; j < formula->clauses[i].literals_count; j++) {
      sat_literal_t literal = formula->clauses[i].literals[j];
      int idx = literal.value;

      if (!found[idx]) {
        sign_count[idx] = literal.sign ? 1 : -1;
        found[idx] = true;
      } else if (sign_count[idx] != 0) {
        if (sign_count[idx] > 0 && !literal.sign) {
          sign_count[idx] = 0;
        } else if (sign_count[idx] < 0 && literal.sign) {
          sign_count[idx] = 0;
        }
      }
    }
  }

  for (int i = 0; i < formula->variables_count; i++) {
    if (sign_count[i] != 0) {
      pure_literal = (sat_literal_t *)malloc(sizeof(sat_literal_t));
      pure_literal->value = i;
      pure_literal->sign = sign_count[i] > 0;
      break;
    }
  }

  free(sign_count);
  free(found);
  return pure_literal;
}

void pure_literal_elimination(sat_t *formula, sat_literal_t literal) {
  for (int i = 0; i < formula->clauses_count;) {
    if (clause_contains(&formula->clauses[i], literal.value, literal.sign)) {
      remove_clause(formula, i);
    } else {
      i++;
    }
  }
}

bool dpll(sat_t *formula) {
  if (is_satisfiable(formula)) {
    return true;
  }
  if (is_unsatisfiable(formula)) {
    return false;
  }

  sat_clause_t *unit_clause = get_unit_clause(formula);
  while (unit_clause) {
    sat_literal_t unit = unit_clause->literals[0];
    unit_propagate(formula, unit);
    unit_clause = get_unit_clause(formula);
  }

  sat_literal_t *pure_literal = get_pure_literal(formula);
  while (pure_literal) {
    pure_literal_elimination(formula, *pure_literal);
    free(pure_literal);
    pure_literal = get_pure_literal(formula);
  }

  sat_literal_t chosen_literal;
  for (int i = 0; i < formula->clauses_count; i++) {
    if (formula->clauses[i].literals_count > 0) {
      chosen_literal = formula->clauses[i].literals[0];
      break;
    }
  }

  sat_t *formula_copy1 = duplicate(formula);
  sat_t *formula_copy2 = duplicate(formula);

  unit_propagate(formula_copy1, chosen_literal);
  chosen_literal.sign = !chosen_literal.sign;
  unit_propagate(formula_copy2, chosen_literal);

  bool result = dpll(formula_copy1) || dpll(formula_copy2);

  destroy_sat(formula_copy1);
  destroy_sat(formula_copy2);

  return result;
}

void compute_phase_transition() {
  int step, i, j, clauses_count, sat_count;
  int assignments[VARIABLES_COUNT];

  for (step = 0; step < ALPHA_STEPS; step++) {
    clauses_count = (step + 1) * MAX_CLAUSES / ALPHA_STEPS;
    alphas[step] = (double)clauses_count / VARIABLES_COUNT;

    sat_count = 0;
    double total_time = 0.0;

    for (i = 0; i < NUM_INSTANCES; i++) {
      sat_t *sat = generate_k_sat(SAT_K, VARIABLES_COUNT, clauses_count);

      for (j = 0; j < VARIABLES_COUNT; j++) {
        assignments[j] = -1;
      }

      clock_t start = clock();
      bool result = dpll(sat);
      clock_t end = clock();
      total_time += (double)(end - start) / CLOCKS_PER_SEC;

      if (result) {
        sat_count++;
      }

      destroy_sat(sat);
    }

    satisfiable[step] = (double)sat_count / NUM_INSTANCES * 100.0;
    complexity[step] = total_time / NUM_INSTANCES;

    if (complexity[step] > max_complexity) {
      max_complexity = complexity[step];
    }

    printf("Alpha: %f SAT: %f COMP: %f\n", alphas[step], satisfiable[step],
           complexity[step]);
  }
}

void draw_grid(double x_max, double y_max) {
  glColor3f(0.3, 0.3, 0.3);
  glBegin(GL_LINES);
  for (double x = 0.0; x <= x_max; x += x_max / 10.0) {
    glVertex2f(x, 0.0);
    glVertex2f(x, y_max);
  }
  for (double y = 0.0; y <= y_max; y += y_max / 10.0) {
    glVertex2f(0.0, y);
    glVertex2f(x_max, y);
  }
  glEnd();
}

void draw_axis_labels(double x_max, double y_max) {
  glColor3f(1.0, 1.0, 1.0);
  char label[10];

  for (int i = 0; i <= 10; i++) {
    sprintf(label, "%.1f", i * x_max / 10.0);
    glRasterPos2f(i * x_max / 10.0, -0.05 * y_max);
    for (char *c = label; *c != '\0'; c++) {
      glutBitmapCharacter(GLUT_BITMAP_HELVETICA_12, *c);
    }
  }

  for (int i = 0; i <= 10; i++) {
    sprintf(label, "%d", i * (int)(y_max / 10.0));
    glRasterPos2f(-0.05 * x_max, i * y_max / 10.0);
    for (char *c = label; *c != '\0'; c++) {
      glutBitmapCharacter(GLUT_BITMAP_HELVETICA_12, *c);
    }
  }
}

void draw_graph(double *x_values, double *y_values, int count, double y_scale,
                float r, float g, float b, const char *label, double x_legend,
                double y_legend) {
  glColor3f(r, g, b);
  glBegin(GL_LINE_STRIP);
  for (int i = 0; i < count; i++) {
    glVertex2f(x_values[i], y_values[i] / y_scale);
  }
  glEnd();

  glRasterPos2f(x_legend, y_legend);
  for (const char *c = label; *c != '\0'; c++) {
    glutBitmapCharacter(GLUT_BITMAP_8_BY_13, *c);
  }
}

void render() {
  double x_max = 10.0;
  double y_max = 100.0;

  glClear(GL_COLOR_BUFFER_BIT);

  draw_grid(x_max, y_max);

  glColor3f(1.0, 1.0, 1.0);
  glBegin(GL_LINES);
  glVertex2f(0.0, 0.0);
  glVertex2f(x_max, 0.0);
  glVertex2f(0.0, 0.0);
  glVertex2f(0.0, y_max);
  glEnd();

  draw_axis_labels(x_max, y_max);

  draw_graph(alphas, satisfiable, ALPHA_STEPS, 1.0, 1.0, 0.0, 0.0,
             "Satisfiable (%)", 1.0, 95.0);
  draw_graph(alphas, complexity, ALPHA_STEPS, max_complexity / y_max, 0.0, 1.0,
             0.0, "Complexity (scaled)", 7.5, 10.0);

  glutSwapBuffers();
}

void reshape(int w, int h) {
  glViewport(0, 0, w, h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  gluOrtho2D(-0.5, 10.5, -5.0, 105.0);
  glMatrixMode(GL_MODELVIEW);
}

int main(int argc, char **argv) {
  compute_phase_transition();

  glutInit(&argc, argv);
  glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB);
  glutInitWindowSize(800, 600);
  glutCreateWindow("3-SAT Phase Transition");

  glClearColor(0.0, 0.0, 0.0, 0.0);
  glutDisplayFunc(render);
  glutReshapeFunc(reshape);

  glutMainLoop();
  return 0;
}
