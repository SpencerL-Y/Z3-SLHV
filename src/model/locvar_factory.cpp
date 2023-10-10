#include "model/locvar_factory.h"


namespace smt {


// TODO adapt when pointer arithmetic is taken into consideration

expr* locvar_factory::get_some_value(sort* s)  {
    SASSERT(s->get_name() == INTLOC_SORT_STR);
    
    std::set<expr*> sortvalues = this->sort2values[s];
    if(sortvalues.size() == 0) {
        return nullptr;
    }

    return *sortvalues.begin();
}

bool locvar_factory::get_some_values(sort* s, expr_ref &v1, expr_ref &v2) {
    SASSERT(s->get_name() == INTLOC_SORT_STR);
    std::set<expr*> sortvalues = this->sort2values[s];
    if(sortvalues.size() < 2) {
        return false;
    }
    expr* r1 = nullptr;
    expr* r2 = nullptr;
    for(expr* e : sortvalues) {
        if(r1 == nullptr) {
            r1 = e;
            continue;
        }
        if(r1 != nullptr && r2 == nullptr) {
            r2 = e;
        }
    }
    v1 = r1;
    v2 = r2;
    return true;
}

expr* locvar_factory::get_fresh_value(sort* s) {
    SASSERT(s->get_name() == INTLOC_SORT_STR);
    expr* result = this->plug->mk_locint(this->heap_unused_top);
    this->heap_unused_top++;
    return result;
}

void locvar_factory::register_value(expr* n) {
    SASSERT(n->get_sort()->get_name() == INTLOC_SORT_STR);
    this->sort2values[n->get_sort()].insert(n);
}


}