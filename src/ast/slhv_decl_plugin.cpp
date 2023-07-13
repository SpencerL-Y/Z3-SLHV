#include <sstream>

#include "ast/slhv_decl_plugin.h"
#include "util/warning.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/arith_decl_plugin.h"

// SLHV
slhv_decl_plugin::slhv_decl_plugin() :
    m_disj_union_sym("uplus"),
    m_list_segment_sym("lseg"),
    m_points_to_sym("pt")
{
    // this->m_family_id = this->m_manager->mk_family_id("slhv");
    
            #ifdef SLHV_DEBUG
            std::cout << "slhv_decl_plugin: family id " << this->m_family_id << std::endl;
            #endif
}



sort* slhv_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if(k == INTHEAP_SORT) {
        return m_manager->mk_sort(symbol(INTHEAP_SORT_STR), 
        sort_info(m_family_id, INTHEAP_SORT));
    } else if(k == INTLOC_SORT) {
        return m_manager->mk_sort(symbol(INTLOC_SORT_STR),
        sort_info(m_family_id, INTLOC_SORT));
    } else if(k == INTDATA_SORT) {
        return m_manager->mk_sort(symbol(INTDATA_SORT_STR), sort_info(m_family_id, INTDATA_SORT));
    }
    else {
        m_manager->raise_exception("invalid sort in slhv");
        return nullptr;
    }
    
}

void slhv_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    #ifdef SLHV_DEBUG
    std::cout << "register slhv sort names" << std::endl;
    #endif
    // add self-defined sort names here
    sort_names.push_back(builtin_name(INTHEAP_SORT_STR, INTHEAP_SORT));
    sort_names.push_back(builtin_name(INTLOC_SORT_STR, INTLOC_SORT));
}

void slhv_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    #ifdef SLHV_DEBUG
    std::cout << "register slhv op names" << std::endl;
    #endif
    op_names.push_back(builtin_name("uplus", OP_HEAP_DISJUNION));
    op_names.push_back(builtin_name("pt", OP_POINTS_TO));
    op_names.push_back(builtin_name("lseg", OP_LIST_SEGMENT));
}

func_decl* slhv_decl_plugin::mk_uplus(unsigned arity, sort * const * domain) {
    if(arity < 2) {
        m_manager->raise_exception("uplus takes at least 2 arguments");
        return nullptr;
    } 
    sort *s = domain[0];
    #ifdef SLHV_DEBUG
    std::cout << "mk_uplus sort name: " <<  s->get_name() << std::endl;
    #endif
    unsigned num_parameters = s->get_num_parameters();
    #ifdef SLHV_DEBUG
    std::cout << "mk_uplus num paramerters: " << num_parameters << " arity: " << arity << std::endl;
    #endif
    parameter param(s);
    func_decl_info info(m_family_id, OP_HEAP_DISJUNION, num_parameters, &param);
    info.set_associative();
    info.set_commutative();
    sort *domain2[arity];
    for(int i = 0; i < arity; i ++) {
        domain2[i] = domain[0];
    }
    func_decl* result_decl = m_manager->mk_func_decl(m_disj_union_sym, arity, domain2, domain[0], info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_uplus result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl;
    #endif
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_points_to(unsigned arity, sort * const* domain) {
    if (arity != 2) {
        m_manager->raise_exception("pt takes exactly two arguments");
        return nullptr;
    }
    sort* addr_sort = domain[0];
    sort* data_sort = domain[1];
    sort* final_sort = this->mk_sort(slhv_sort_kind::INTHEAP_SORT, 0, nullptr);
    func_decl_info info(m_family_id, OP_POINTS_TO);

    func_decl* result_decl = m_manager->mk_func_decl(m_points_to_sym, arity, domain, final_sort, func_decl_info(m_family_id, OP_POINTS_TO));
    #ifdef SLHV_DEBUG
    std::cout << "mk_points_to result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl;
    #endif
    return result_decl;

}

func_decl* slhv_decl_plugin::mk_const_hvar(sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);
    func_decl_info info(m_family_id, OP_HVAR_CONST);

    func_decl* result_decl = m_manager->mk_func_decl(arity, domain, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_const_hvar result: " << result_decl->get_name() << "family id: " << m_family_id << std::endl;
    #endif
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_const_locvar(sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);
    func_decl_info info(m_family_id, OP_LOCVAR_CONST);
    func_decl* result_decl = m_manager->mk_func_decl(arity, domain, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_const_locvar result: " << result_decl->get_name() << "family id: " << m_family_id << std::endl;
    #endif
    return result_decl;

}


func_decl* slhv_decl_plugin::mk_const_emp(sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);

    if(this->global_emp != nullptr) {
        return this->global_emp->get_decl();
    }
    func_decl_info info(m_family_id, OP_EMP);

    func_decl* result_decl = m_manager->mk_func_decl(arity, domain, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_emp result: " << result_decl->get_name() << "family id: " << m_family_id << std::endl;
    #endif
    expr* const* result_expr = nullptr;
    this->global_emp = this->m_manager->mk_app(result_decl, result_expr);
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_const_nil(sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);
    if(this->global_nil != nullptr) {
        return this->global_nil->get_decl();
    }
    func_decl_info info(m_family_id, OP_NIL);
    func_decl* result_decl = m_manager->mk_func_decl(arity, domain, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_nil result: " << result_decl->get_name() << "family id: " << m_family_id << std::endl;
    #endif
    expr* const* result_expr = nullptr;
    this->global_nil = this->m_manager->mk_app(result_decl, result_expr);
    return result_decl;
}

func_decl * slhv_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range)  {
    switch (k)
    {
    case OP_HEAP_DISJUNION:
        /* code */
        #ifdef SLHV_DEBUG
        std::cout << "mk_func_decl in slhv plugin op_heap_disjunion" << std::endl;
        #endif
        return this->mk_uplus(arity, domain);
        break;
    case OP_POINTS_TO:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin op_points_to" << std::endl; 
    #endif 
        return this->mk_points_to(arity, domain);
    case OP_EMP:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin op_emp" << std::endl;
    #endif
        return this->mk_const_emp(range, arity, domain);
    case OP_NIL:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin op_nil" << std::endl;
    #endif
        return this->mk_const_nil(range, arity, domain);
    
    default:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin default!!" << std::endl; 
    #endif 
        return nullptr;
        break;
    }
}