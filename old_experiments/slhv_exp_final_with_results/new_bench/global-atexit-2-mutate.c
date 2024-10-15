#include <stdlib.h>
extern _Bool __VERIFIER_nondet_bool();
int **g = ((void *)0);
void free_g1() {
 free(g);
 g = ((void *)0);
}
void free_g2() {
 if (g != ((void *)0))
  free(*g);
}
int main() {
 g = (int **) malloc(sizeof(int *));
 *g = (int *) malloc(sizeof(int));
 if (__VERIFIER_nondet_bool()) return 0;
 free(*g);
 free(g);
 g = ((void *)0);
 free_g2();
 free_g1();
 return 0;
}

// invalid free : 4
// invalid memleak : 3
