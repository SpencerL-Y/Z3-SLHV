#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
struct item {
    struct item *next;
    struct item *data;
};
static void append(struct item **plist)
{
    struct item *item = malloc(sizeof *item);
    item->next = *plist;
    item->data = (item->next)
        ? item->next->data
        : malloc(sizeof *item);
    *plist = item;
}
int main()
{
    struct item *list = ((void *)0);
    append(&list);
    if (list) {
        struct item *next = list->next;
        free(list);
        list = next;
    }
    return 0;
}

// invalid memleak : 5