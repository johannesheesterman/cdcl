#ifndef CDCL_H
#define CDCL_H

#include <stdbool.h>
#include <stdlib.h>

#define CLAUSE_STATUS_SAT 0
#define CLAUSE_STATUS_UNSAT 1
#define CLAUSE_STATUS_UNIT 2
#define CLAUSE_STATUS_UNRESOLVED 3
#define CLAUSE_STATUS_CONFLICT 4

#define da_append(xs, x) \
    do { \
        if (xs.count >= xs.capacity) { \
            if (xs.capacity == 0) xs.capacity = 256; \
            else xs.capacity *= 2; \
            xs.items = realloc(xs.items, xs.capacity * sizeof(*xs.items)); \
        } \
        xs.items[xs.count++] = x; \
    } while(0); \

struct Clause {
    int *literals;
    int size;

    int litWatch1;
    int litWatch2;
};

struct LiteralList {
    int* items;
    size_t count;
    size_t capacity;
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

struct Clauses {
    struct Clause** items; 
    size_t count;
    size_t capacity;
};

struct CdclState {
    struct Formula* formula;
    struct Assignment** assignments;
    int dl;

    // Watchlists
    struct Clauses** lit2Clauses;
};

int get_lit2Clauses_ix(int literal) {
    int abs_lit = abs(literal);
    return (abs_lit - 1) * 2 + (literal < 0 ? 1 : 0);
}

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

struct UnitPropagationResult unit_propagation(struct CdclState* state, struct LiteralList* to_propagate) {

    int i = 0;
    while (i < to_propagate->count) {
        int watching_literal = -to_propagate->items[i];
        int abs_lit = abs(to_propagate->items[i]);

        struct Clauses* watching_clauses = &state->lit2Clauses[abs_lit];

        for (int j = 0; j < watching_clauses->count; j++) {
            struct Clause* watching_clause = &watching_clauses->items[j];

            for (int k = 0; k < watching_clause->size; k++) {
                int lit = watching_clause->literals[k];

                if (watching_clause->litWatch1 == lit || watching_clause->litWatch2 == lit) {
                    continue;
                }
                else if (state->assignments[abs(lit)] != NULL && state->assignments[abs(lit)]->value == false) {
                    continue;
                }
                else {
                    // Swap watching_lit with lit
                    
                }
            }

            // We cannot find another literal to watch, so we need to resolve the clause.




        }
         

        i++;
    }


    // bool finished = false;
    // struct Formula* formula = state->formula;
    // struct Assignment** assignments = state->assignments;
    // int dl = state->dl;

    // while (!finished) {
    //     finished = true;

    //     for (int i = 0; i < formula->size; i++) {
    //         struct Clause clause = formula->clauses[i];
    //         char status = clause_status(&clause, assignments);

    //         if (status == CLAUSE_STATUS_UNRESOLVED || status == CLAUSE_STATUS_SAT) {
    //             continue;
    //         }
    //         else if (status == CLAUSE_STATUS_UNIT) {
    //             int unassignedLiteral = unassigned_literal(&clause, assignments);
    //             assign(assignments, unassignedLiteral, unassignedLiteral >= 0, &clause, dl);
    //             finished = false;
    //         }
    //         else {
    //             return (struct UnitPropagationResult){CLAUSE_STATUS_CONFLICT, &clause};   
    //         }
    //     }
    // }

    // return (struct UnitPropagationResult){CLAUSE_STATUS_UNRESOLVED, NULL};

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
            assignments[i] = NULL;
        }
    }
}

bool* CDCL(size_t n, struct Formula* formula) { 
    n = n + 1; // 0 is unused
    struct CdclState state = {
        formula, 
        malloc(n * sizeof(size_t)), 
        0,
        malloc(n * 2 * sizeof(struct Clauses))
    };

    for (int i = 0; i < n * 2; i++) {
        state.lit2Clauses[i] = malloc(sizeof(struct Clauses));
        state.lit2Clauses[i]->items = malloc(10 * sizeof(struct Clause));
        state.lit2Clauses[i]->count = 0;
        state.lit2Clauses[i]->capacity = 10;
    }

    struct LiteralList unit_clauses_to_propagate = {malloc(10 * sizeof(int)), 0, 10};

    // Initialize watchlists
    for (struct Clause *clause = formula->clauses; clause < formula->clauses + formula->size; clause++) {
        if (clause->size == 1) {
            const int lit = clause->literals[0];
            struct Clauses* lit2Clauses = state.lit2Clauses[get_lit2Clauses_ix(lit)];
            da_append((*lit2Clauses), clause);    
            clause->litWatch1 = lit;
            clause->litWatch2 = lit;    
            da_append(unit_clauses_to_propagate, lit);
        } else {
            const int lit0 = clause->literals[0];
            const int lit1 = clause->literals[1];
            struct Clauses* lit2Clauses1 = state.lit2Clauses[get_lit2Clauses_ix(lit0)];
            struct Clauses* lit2Clauses2 = state.lit2Clauses[get_lit2Clauses_ix(lit1)];    
            da_append((*lit2Clauses1), clause);
            da_append((*lit2Clauses2), clause);    
            clause->litWatch1 = lit0;
            clause->litWatch2 = lit1;
        }
    }

    struct UnitPropagationResult result = unit_propagation(&state, &unit_clauses_to_propagate);

    while(true) {
        int pickBranchingLiteral = pick_branching_literal(state.assignments, n);
        if (pickBranchingLiteral < 0) break;

        state.dl++;
        bool value = false;
        assign(state.assignments, pickBranchingLiteral, value, NULL, state.dl);
        struct LiteralList to_propagate = {malloc(10 * sizeof(int)), 0, 10};
        if (value) da_append(to_propagate, pickBranchingLiteral)
        else da_append(to_propagate, -pickBranchingLiteral);

        while(true) {            
            result = unit_propagation(&state, &to_propagate);
            if (result.reason != CLAUSE_STATUS_CONFLICT) break;

            struct ConflictAnalysisResult conflictAnalysisResult = conflict_analysis(state.dl, n, state.assignments, result.conflictClause);
            if (conflictAnalysisResult.backjumpLevel < 0) return NULL;

            add_clause(formula, conflictAnalysisResult.clause);

            backtrack(conflictAnalysisResult.backjumpLevel, n, state.assignments);
            state.dl = conflictAnalysisResult.backjumpLevel;

            // TODO: The learnt clause must be a unit clause, so the next step must again be unit propagation.
            // ...
        }

    }

    bool* model = malloc(n * sizeof(bool));
    for (int i = 0; i < n; i++) {
        if (state.assignments[i] == NULL) model[i] = false;
        else model[i] = state.assignments[i]->value;
    }
    return model;
}


#endif