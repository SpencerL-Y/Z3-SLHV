
#pragma once
#include "ast/ast.h"

#define INTHEAP_SORT_STR "IntHeap"
#define INTLOC_SORT_STR "IntLoc"
#define INTDATA_SORT_STR "IntData"
// SLHV
enum slhv_sort_kind {
    INTHEAP_SORT,
    INTLOC_SORT,
    INTDATA_SORT
};

enum slhv_op_kind {
    OP_HEAP_DISJUNION,
    OP_POINTS_TO,
    OP_LIST_SEGMENT,
    OP_HVAR_CONST,
    OP_LOCVAR_CONST,
    OP_EMP,
    OP_NIL
};


class slhv_decl_plugin : public decl_plugin {
    symbol m_disj_union_sym;
    symbol m_points_to_sym;
    symbol m_list_segment_sym;
    symbol curr_locvar_name;
    symbol curr_hvar_name;

    public:

    app* global_emp;
    app* global_nil;

    bool pt_record_initialized;
    int pt_record_length;
    int pt_locnum;
    int pt_datanum;
    slhv_decl_plugin();

    void set_pt_record(int ln, int dn);

    decl_plugin * mk_fresh() override {
        return alloc(slhv_decl_plugin);
    }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void set_curr_locvar(symbol locvar_name) {
        this->curr_locvar_name = locvar_name;
    }
    
    void set_curr_hvar(symbol hvar_name) {
        this->curr_hvar_name = hvar_name;
    }

    func_decl* mk_uplus(unsigned arity, sort * const * domain);

    func_decl* mk_disj_union(unsigned arity, sort* const* domain);

    func_decl* mk_points_to(unsigned arity, sort * const* domain);

    func_decl* mk_const_hvar(symbol name, sort* range, unsigned arity, sort* const* domain);

    func_decl* mk_const_locvar(symbol name, sort* range, unsigned arity, sort* const* domain);

    func_decl* mk_const_emp(sort* range, unsigned arity, sort* const* domain);

    func_decl* mk_const_nil(sort* range, unsigned arity, sort* const* domain);

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;

    ///////////////////

};