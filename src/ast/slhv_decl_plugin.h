
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

    public:

    static func_decl* global_emp;
    static func_decl* global_nil;
    slhv_decl_plugin();

    decl_plugin * mk_fresh() override {
        return alloc(slhv_decl_plugin);
    }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    func_decl* mk_uplus(unsigned arity, sort * const * domain);

    func_decl* mk_disj_union(unsigned arity, sort* const* domain);

    func_decl* mk_points_to(unsigned arity, sort * const* domain);

    func_decl* mk_const_hvar(sort* range, unsigned arity, sort* const* domain);

    func_decl* mk_const_locvar(sort* range, unsigned arity, sort* const* domain);

    func_decl* mk_const_emp(sort* range, unsigned arity, sort* const* domain);

    func_decl* mk_const_nil(sort* range, unsigned arity, sort* const* domain);

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;

    ///////////////////

};