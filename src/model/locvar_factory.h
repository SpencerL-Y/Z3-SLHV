#pragma once

#include "ast/slhv_decl_plugin.h"
#include "model/model_core.h"
#include "model/value_factory.h"

namespace smt {

class locvar_factory final : public value_factory {

    private:
    slhv_decl_plugin* plug;
    std::set<unsigned> used_addr;
    unsigned heap_unused_top;

    std::map<sort*, std::set<expr*>> sort2values;

    app* nil_loc;
    app* emp_heap;

    public:

    locvar_factory(ast_manager& m, family_id fid): 
    value_factory(m, fid),
    heap_unused_top(1)
    {
    }
    ~locvar_factory() {}
    expr* get_some_value(sort* s) override;
    bool get_some_values(sort* s, expr_ref &v1, expr_ref &v2) override;
    expr* get_fresh_value(sort* s) override;
    void register_value(expr* n) override;


    void set_slhv_decl_plugin(slhv_decl_plugin* plug) {
        this->plug = plug;
    }

    void set_nil_loc(app* nil)  {
        this->nil_loc = nil;
    }

    void set_emp_heap(app* emp) {
        this->emp_heap = emp;
    }
};
}