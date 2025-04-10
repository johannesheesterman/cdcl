#include <stdio.h>
#include "cdcl.h"

int main() {
    struct Clause clauses[3] = {
        {(int[]){3}, 1},
        {(int[]){1, 2}, 2},
        {(int[]){2, 3}, 2}
    };

    struct Formula formula = {clauses, sizeof(clauses) / sizeof(struct Clause)};

    int n = 3;
    bool* result = CDCL(n, &formula);

    for (int i = 0; i < n; i++) {
        printf("%d\n", result[i]);
    }

    return 0;
}