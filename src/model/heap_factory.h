#pragma once

#include "ast/slhv_decl_plugin.h"
#include "model/model_core.h"
#include "model/value_factory.h"

namespace smt {

class edge_labelled_dgraph;
class heap_factory final : public value_factory {

    private:
    edge_labelled_dgraph* heap_sat_model;
    std::set<unsigned> used_addr;
    unsigned heap_unused_top;

    app* nil_loc;
    app* emp_heap;

    public:

    heap_factory(ast_manager& m, family_id fid): 
    value_factory(m, fid),
    heap_unused_top(1)
    {
    }
    ~heap_factory() {}
    expr* get_some_value(sort* s) override;
    bool get_some_values(sort* s, expr_ref &v1, expr_ref &v2) override;
    expr* get_fresh_value(sort* s) override;
    void register_value(expr* n) override;


    void set_heap_sat_model(edge_labelled_dgraph* graph) {
        this->heap_sat_model = graph;
    }

    void set_nil_loc(app* nil)  {
        this->nil_loc = nil;
    }

    void set_emp_heap(app* emp) {
        this->emp_heap = emp;
    }
};
}