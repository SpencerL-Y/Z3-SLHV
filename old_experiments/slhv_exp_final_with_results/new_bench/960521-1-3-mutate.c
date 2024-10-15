#include <stdlib.h>
int *a, *b;
int n;
int main ()
{
  n = 3;
  a = malloc (n * sizeof(*a));
  b = malloc (n * sizeof(*b));
  *b++ = 0;
  if (b[-2])
  { free(a); free(b-1); }
  else
  { free(a); free(b-1); }
  return 0;
}

// invalid deref : 1