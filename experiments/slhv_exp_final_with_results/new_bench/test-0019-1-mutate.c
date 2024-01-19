#include <stdlib.h>
typedef struct {
    void *lo;
    void *hi;
} TData;
int main() {
    TData* pdata = malloc(sizeof(TData));
    pdata->lo = malloc(8);
    pdata->hi = malloc(8);
    void *lo = pdata->lo;
    void *hi = pdata->hi;
    if (lo == hi)
        return 0;
    free(lo);
    free(hi);
    return 0;
}

// invalid memleak : 3