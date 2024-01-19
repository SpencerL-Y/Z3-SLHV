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
    if (lo == hi) {
        free(lo);
        free(hi);
    }
    pdata->lo = (void *) 0;
    pdata->hi = (void *) 0;
    free(pdata);
    return 0;
}

// invalid memleak : 3