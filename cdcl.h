#ifndef CDCL_H
#define CDCL_H

#include <stdbool.h>
#include <stdlib.h>

#define CLAUSE_STATUS_SAT 0
#define CLAUSE_STATUS_UNSAT 1
#define CLAUSE_STATUS_UNIT 2
#define CLAUSE_STATUS_UNRESOLVED 3
#define CLAUSE_STATUS_CONFLICT 4

struct Clause {
    int *literals;
    int size;
};

struct Formula {
    struct Clause *clauses;
    int size;
};

struct Assignment {
    bool value;
    struct Clause *antecedent;
    int decisionLevel;
};

struct UnitPropagationResult {
    char reason;
    struct Clause *conflictClause;
};

struct ConflictAnalysisResult {
    struct Clause *clause;
    int backjumpLevel;
};

char clause_status(struct Clause *clause, struct Assignment** assignments) {    
    int falseCount = 0;
    for (int i = 0; i < clause->size; i++) {
        int literal = clause->literals[i];
        struct Assignment* assignment = assignments[abs(literal)];        
        if (assignment == NULL) continue;
        if (assignment->value == true) return CLAUSE_STATUS_SAT;
        falseCount++;
    }
    
    if (falseCount == clause->size) return CLAUSE_STATUS_UNSAT;
    if (falseCount == clause->size - 1) return CLAUSE_STATUS_UNIT;
    return CLAUSE_STATUS_UNRESOLVED;
}

void assign(struct Assignment** assignments, int literal, bool value, struct Clause* antecedent, int dl) {
    literal = abs(literal);
    assignments[literal] = malloc(sizeof(struct Assignment));
    assignments[literal]->value = value;
    assignments[literal]->antecedent = antecedent;
    assignments[literal]->decisionLevel = dl;
}

int unassigned_literal(struct Clause* clause , struct Assignment** assignments) {
    for (int i = 0; i < clause->size; i++) {
        int literal = clause->literals[i];
        struct Assignment* assignment = assignments[abs(literal)];
        if (assignment == NULL) return literal;
    }
    return 0;
}

struct UnitPropagationResult unit_propagation(int dl, struct Formula* formula, struct Assignment** assignments) {
    bool finished = false;

    while (!finished) {
        finished = true;

        for (int i = 0; i < formula->size; i++) {
            struct Clause clause = formula->clauses[i];
            char status = clause_status(&clause, assignments);

            if (status == CLAUSE_STATUS_UNRESOLVED || status == CLAUSE_STATUS_SAT) {
                continue;
            }
            else if (status == CLAUSE_STATUS_UNIT) {
                int unassignedLiteral = unassigned_literal(&clause, assignments);
                assign(assignments, unassignedLiteral, unassignedLiteral >= 0, &clause, dl);
                finished = false;
            }
            else {
                return (struct UnitPropagationResult){CLAUSE_STATUS_CONFLICT, &clause};   
            }
        }
    }

    return (struct UnitPropagationResult){CLAUSE_STATUS_UNRESOLVED, NULL};
}

int pick_branching_literal(struct Assignment** assignments, int n) {
    for (int i = 0; i < n; i++) {
        if (assignments[i] == NULL) return i;
    }
    return -1;
}

int first_implied_literal_at_dl(int dl, struct Clause* clause, struct Assignment** assignments) {
    for (int i = 0; i < clause->size; i++) {
        int literal = clause->literals[i];
        struct Assignment* assignment = assignments[abs(literal)];
        if (assignment != NULL && assignment->decisionLevel == dl && assignment->antecedent != NULL) return literal;
    }
    return -1;
}

struct Clause* resolve(struct Clause* clause1, struct Clause* clause2, int literal) {
    literal = abs(literal);

    int size = clause1->size + clause2->size - 2;
    int* literals = malloc(size * sizeof(int));

    int j = 0;
    for (int i = 0; i < clause1->size; i++) {
        if (abs(clause1->literals[i]) == literal) continue;
        literals[j++] = clause1->literals[i];
    }

    for (int i = 0; i < clause2->size; i++) {
        if (abs(clause2->literals[i]) == literal) continue;
        literals[j++] = clause2->literals[i];
    }

    return &(struct Clause){literals, size};
}

bool single_literal_at_dl(int dl, struct Clause* clause, struct Assignment** assignments) {
    int count = 0;
    for (int i = 0; i < clause->size; i++) {
        int literal = clause->literals[i];
        struct Assignment* assignment = assignments[abs(literal)];
        if (assignment != NULL && assignment->decisionLevel == dl) count++;
    }
    return count == 1;
}
 
struct ConflictAnalysisResult conflict_analysis(int dl, size_t n, struct Assignment** assignments, struct Clause* clause) {
    if (dl == 0) return (struct ConflictAnalysisResult){NULL, -1};

    while(!single_literal_at_dl(dl, clause, assignments)) {
        int literal = first_implied_literal_at_dl(dl, clause, assignments);
        clause = resolve(clause, assignments[abs(literal)]->antecedent, literal);        
    }

    // Compute backtrack level b (second largest decision level in the learned clause)
    int first = 0, second = 0;
    for (int i = 0; i < clause->size; i++) {
        int literal = clause->literals[i];
        struct Assignment* assignment = assignments[abs(literal)];
        if (assignment != NULL && assignment->decisionLevel != dl) {
            int level = assignment->decisionLevel;
            if (level > first) {
                second = first;
                first = level;
            } else if (level > second && level < first) {
                second = level;
            }
        }
    }

    return (struct ConflictAnalysisResult){clause, second};
}

void add_clause(struct Formula* formula, struct Clause* clause) {
    formula->clauses = realloc(formula->clauses, (formula->size + 1) * sizeof(struct Clause));
    formula->clauses[formula->size++] = *clause;
}

void backtrack(int dl, int n, struct Assignment** assignments) {
    for (int i = 0; i < n; i++) {
        if (assignments[i] != NULL && assignments[i]->decisionLevel > dl) {
            // free(assignments[i]);
            assignments[i] = NULL;
        }
    }
}

bool* CDCL(size_t n, struct Formula* formula) { 
    struct Assignment** assignments = malloc(n * sizeof(size_t));

    int dl = 0;
    struct UnitPropagationResult result = unit_propagation(dl, formula, assignments);

    while(true) {
        int pickBranchingLiteral = pick_branching_literal(assignments, n);
        if (pickBranchingLiteral < 0) break;

        dl++;
        assign(assignments, pickBranchingLiteral, false, NULL, dl);

        while(true) {
            result = unit_propagation(dl, formula, assignments);
            if (result.reason != CLAUSE_STATUS_CONFLICT) break;

            struct ConflictAnalysisResult conflictAnalysisResult = conflict_analysis(dl, n, assignments, result.conflictClause);
            if (conflictAnalysisResult.backjumpLevel < 0) return NULL;

            add_clause(formula, conflictAnalysisResult.clause);

            backtrack(conflictAnalysisResult.backjumpLevel, n, assignments);
            dl = conflictAnalysisResult.backjumpLevel;
        }

    }

    bool* model = malloc(n * sizeof(bool));
    for (int i = 0; i < n; i++) {
        if (assignments[i] == NULL) model[i] = false;
        else model[i] = assignments[i]->value;
    }
    return model;
}


#endif