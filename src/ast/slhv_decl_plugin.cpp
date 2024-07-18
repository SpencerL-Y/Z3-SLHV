#include <sstream>


#include "util/gparams.h"
#include "ast/slhv_decl_plugin.h"
#include "util/warning.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"

// for SLHV debug
#include "util/slhv_debug.h"

// SLHV
slhv_decl_plugin::slhv_decl_plugin() :
    m_disj_union_sym("uplus"),
    m_list_segment_sym("lseg"),
    m_points_to_sym("pt"),
    m_locadd_symbol("locadd"),
    m_subh_symbol("subh"),
    m_disjh_symbol("disjh"),
    m_readloc_symbol("readloc"),
    m_readdata_symbol("readdata"),
    m_writeloc_symbol("writeloc"),
    m_writedata_symbol("writedata"),
    m_loc2int_symbol("loc2int"),
    m_int2loc_symbol("int2loc"),
    m_locconst_symbol("Loc"),
    global_emp(nullptr),
    global_nil(nullptr),
    record_type_num(0),
    au_ptr(nullptr),
    dt_util_ptr(nullptr)
{
}


void slhv_decl_plugin::slhv_datatype_init() {

    ast_manager& m = *this->m_manager;
    family_id datatype_id = m.mk_family_id("datatype");
    datatype_decl_plugin* dt_plug = (datatype_decl_plugin*) m.get_plugin(datatype_id);
    this->dt_util_ptr = alloc(datatype_util, m);
    datatype_util& dtu = *this->dt_util_ptr;
    this->au_ptr = alloc(arith_util, m);
    arith_util& au = *this->au_ptr;
    if(this->pt_record_decls.find("Pt_R_0") == this->pt_record_decls.end()) {
        sort* intsort = this->mk_sort(INTLOC_SORT, 0, nullptr);
        sort_ref_vector srts0(m);
        accessor_decl* Pt_R_0_accs[1] = {
            mk_accessor_decl(m, symbol("data"), type_ref(intsort))
        };
        constructor_decl* cs0[1] = { mk_constructor_decl(symbol("Pt_R_0"), symbol("is-Pt_R_0"), 1, Pt_R_0_accs)};
        datatype_decl* dt0 = mk_datatype_decl(dtu, symbol("pt_record_0"), 0, nullptr, 1, cs0);
        VERIFY(dtu.plugin().mk_datatypes(1, &dt0, 0, nullptr, srts0))
        sort* record0_sort = srts0.get(0);
        ptr_vector<func_decl> const & decls0 = *dtu.get_datatype_constructors(record0_sort);
        func_decl* Pt_R_0_decl = decls0.get(0);
        
        this->add_pt_record("Pt_R_0", 1, 0);
        this->add_pt_r_decl("Pt_R_0", Pt_R_0_decl);
    }
    // if(this->pt_record_decls.find("Pt_R_1") == this->pt_record_decls.end()) {

    //     sort* intsort = au.mk_int();
    //     sort_ref_vector srts1(m);
    //     accessor_decl* Pt_R_1_accs[1] = {
    //         mk_accessor_decl(m, symbol("data"), type_ref(intsort))
    //     };
    //     constructor_decl* cs1[1] = { mk_constructor_decl(symbol("Pt_R_1"), symbol("is-Pt_R_1"), 1, Pt_R_1_accs)};
    //     datatype_decl* dt1 = mk_datatype_decl(dtu, symbol("pt_record_1"), 0, nullptr, 1, cs1);
    //     VERIFY(dtu.plugin().mk_datatypes(1, &dt1, 0, nullptr, srts1))
    //     sort* record1_sort = srts1.get(0);
    //     ptr_vector<func_decl> const & decls1 = *dtu.get_datatype_constructors(record1_sort);
    //     func_decl* Pt_R_1_decl = decls1.get(0);
        
    //     this->add_pt_record("Pt_R_1", 0, 1);
    //     this->add_pt_r_decl("Pt_R_1", Pt_R_1_decl);
    // } 
}




sort* slhv_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if(k == INTHEAP_SORT) {
        return m_manager->mk_sort(symbol(INTHEAP_SORT_STR), 
        sort_info(m_family_id, INTHEAP_SORT));
    } else if(k == INTLOC_SORT) {
        return m_manager->mk_sort(symbol(INTLOC_SORT_STR),
        sort_info(m_family_id, INTLOC_SORT));
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
    op_names.push_back(builtin_name("locadd", OP_LOCADD));
    op_names.push_back(builtin_name("subh", OP_SUBH));
    op_names.push_back(builtin_name("disjh", OP_DISJH));
    op_names.push_back(builtin_name("readloc", OP_READLOC));
    op_names.push_back(builtin_name("readdata", OP_READDATA));
    op_names.push_back(builtin_name("writeloc", OP_WRITELOC));
    op_names.push_back(builtin_name("writedata", OP_WRITEDATA));
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
    sort *domain2[arity];
    for(int i = 0; i < arity; i ++) {
        domain2[i] = domain[0];
    }
    func_decl* result_decl = m_manager->mk_func_decl(m_disj_union_sym, arity, domain2, domain[0], info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_uplus result: " << result_decl->get_name() << "  family id: " << m_family_id << std::endl;
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

func_decl* slhv_decl_plugin::mk_locadd(unsigned arity, sort* const* domain) {
    if(arity != 2) {
        m_manager->raise_exception("locadd takes exactly two arguments");
        return nullptr;
    }
    sort* addon_loc_sort = domain[0];
    sort* num_sort = domain[1];

    sort* final_sort = this->mk_sort(slhv_sort_kind::INTLOC_SORT, 0, nullptr);

    func_decl_info info(m_family_id, OP_LOCADD);
    func_decl* result_decl = m_manager->mk_func_decl(m_locadd_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_LOCADD));
    #ifdef SLHV_DEBUG
    std::cout << "mk_locadd result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl;
    #endif
    return result_decl;

}

func_decl* slhv_decl_plugin::mk_subh(unsigned arity, sort* const* domain) {
    if(arity != 2) {
        m_manager->raise_exception("subh takes exactly two arguments");
        return nullptr;
    }

    sort* first_ht_sort =  domain[0];
    sort* second_ht_sort = domain[1];

    sort* final_sort = m_manager->mk_bool_sort();
    func_decl_info info(m_family_id, OP_SUBH);
    func_decl* result_decl = m_manager->mk_func_decl(m_subh_symbol, arity, domain, final_sort, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_subh result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl; 
    #endif
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_disjh(unsigned arity, sort* const* domain) {

    if(arity != 2) {
        m_manager->raise_exception("disjh takes exactly two arguments");
        return nullptr;
    }

    sort* first_ht_sort =  domain[0];
    sort* second_ht_sort = domain[1];

    sort* final_sort = m_manager->mk_bool_sort();
    func_decl_info info(m_family_id, OP_DISJH);
    func_decl* result_decl = m_manager->mk_func_decl(m_disjh_symbol, arity, domain, final_sort, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_subh result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl; 
    #endif
    return result_decl;
}



func_decl* slhv_decl_plugin::mk_readloc(unsigned arity, sort*const* domain) {
    if(arity != 2) {
        m_manager->raise_exception("readloc takes exacly two arguments");
        return nullptr;
    }
    sort* read_heap_sort = domain[0];
    sort* read_addr_sort = domain[1];
    sort* final_sort = this->mk_sort(slhv_sort_kind::INTLOC_SORT, 0, nullptr);
    
    func_decl* result_decl = m_manager->mk_func_decl(m_readloc_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_READLOC));
    return result_decl;
}



func_decl* slhv_decl_plugin::mk_readdata(unsigned arity, sort*const* domain) {
    if(arity != 2) {
        m_manager->raise_exception("readdata takes exacly two arguments");
        return nullptr;
    }
    sort* read_heap_sort = domain[0];
    sort* read_addr_sort = domain[1];
    sort* final_sort = this->m_manager->mk_sort(arith_family_id, INT_SORT);
    
    func_decl* result_decl = m_manager->mk_func_decl(m_readdata_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_READDATA));
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_writeloc(unsigned arity, sort*const* domain) {
    if(arity != 3) {
        m_manager->raise_exception("writeloc takes exactly three arguments");
        return nullptr;
    }
    sort* written_heap_sort = domain[0];
    sort* written_addr_sort = domain[1];
    sort* written_lt_sort = domain[2];

    sort* final_sort = this->mk_sort(slhv_sort_kind::INTHEAP_SORT, 0, nullptr);

    

    func_decl* result_decl = m_manager->mk_func_decl(m_writeloc_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_WRITELOC));
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_writedata(unsigned arity, sort*const* domain) {
    if(arity != 3) {
        m_manager->raise_exception("writedata takes exactly three arguments");
        return nullptr;
    }
    sort* written_heap_sort = domain[0];
    sort* written_addr_sort = domain[1];
    sort* written_dt_sort = domain[2];


    sort* final_sort = this->mk_sort(slhv_sort_kind::INTHEAP_SORT, 0, nullptr);

    func_decl* result_decl = m_manager->mk_func_decl(m_writedata_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_WRITEDATA));
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_loc2int(unsigned arity, sort*const* domain) {
    if(arity != 1) {
        m_manager->raise_exception("loc2int takes exactly one arguments");
        return nullptr;
    }

    sort* orig_loc_sort = domain[0];

    sort* final_sort = this->m_manager->mk_sort(arith_family_id, INT_SORT);

    func_decl* result_decl = m_manager->mk_func_decl(m_loc2int_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_LOC2INT));
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_int2loc(unsigned arity, sort* const* domain) {
    if(arity != 1) {
        m_manager->raise_exception("int2loc takes exactly one arguments");
        return nullptr;
    }

    sort* orig_int_sort = domain[0];
    
    sort* final_sort = this->mk_sort(slhv_sort_kind::INTLOC_SORT, 0, nullptr);

    func_decl* result_decl = m_manager->mk_func_decl(m_int2loc_symbol, arity, domain, final_sort, func_decl_info(m_family_id, OP_INT2LOC));
    return result_decl;
}



func_decl* slhv_decl_plugin::mk_const_hvar(symbol name, sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);
    func_decl_info info(m_family_id, OP_HVAR_CONST);

    func_decl* result_decl = m_manager->mk_const_decl(name, range, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_const_hvar result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl;
    #endif
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_const_locvar(symbol name, sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);
    func_decl_info info(m_family_id, OP_LOCVAR_CONST);
    func_decl* result_decl = m_manager->mk_const_decl(name, range, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_const_locvar result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl;
    #endif
    return result_decl;

}
func_decl* slhv_decl_plugin::mk_const_emp(sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);

    if(this->global_emp != nullptr) {
        return this->global_emp->get_decl();
    }
    func_decl_info info(m_family_id, OP_EMP);

    func_decl* result_decl = m_manager->mk_const_decl(symbol("emp"), range, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_emp result: " << result_decl->get_name() << " family id: " << m_family_id << std::endl;
    #endif
    expr* const* result_expr = nullptr;
    this->global_emp = this->m_manager->mk_app(result_decl, result_expr);
    this->m_manager->inc_ref(this->global_emp);
    return result_decl;
}

func_decl* slhv_decl_plugin::mk_const_nil(sort* range, unsigned arity, sort* const* domain) {
    SASSERT(arity == 0);
    if(this->global_nil != nullptr) {
        return this->global_nil->get_decl();
    }
    func_decl_info info(m_family_id, OP_NIL);
    func_decl* result_decl = m_manager->mk_const_decl(symbol("nil"), range, info);
    #ifdef SLHV_DEBUG
    std::cout << "mk_nil result: " << result_decl->get_name() << "  family id: " << m_family_id << std::endl;
    #endif
    expr* const* result_expr = nullptr;
    this->global_nil = this->m_manager->mk_app(result_decl, result_expr);
    this->m_manager->inc_ref(this->global_nil);
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
    case OP_LOCADD:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin op_locadd" << std::endl; 
    #endif
        return this->mk_locadd(arity, domain);
    case OP_SUBH:
        return this->mk_subh(arity, domain);
    case OP_DISJH:
        return this->mk_disjh(arity, domain);
    case OP_READLOC:
        return this->mk_readloc(arity, domain);
    case OP_READDATA:
        return this->mk_readdata(arity, domain);
    case OP_WRITELOC:
        return this->mk_writeloc(arity, domain);
    case OP_WRITEDATA:
        return this->mk_writedata(arity, domain);
    case OP_LOC2INT:
        return this->mk_loc2int(arity, domain);
    case OP_INT2LOC:
        return this->mk_int2loc(arity, domain);
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
    case OP_LOCVAR_CONST:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin op_locvar_const" << std::endl;
    #endif
        return this->mk_const_locvar(this->curr_locvar_name, range, arity, domain);
    case OP_HVAR_CONST:

    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin op_hvar_const" << std::endl;
    #endif
        return this->mk_const_hvar(this->curr_hvar_name, range, arity, domain);
    default:
    #ifdef SLHV_DEBUG
    std::cout << "mk_func_decl in slhv plugin default!!" << std::endl; 
    #endif 
        return nullptr;
        break;
    }

}

app* slhv_decl_plugin::mk_locint(unsigned addr) {

    parameter param(addr);
    sort* loc_sort = this->mk_sort(INTLOC_SORT, 0, nullptr);
    func_decl* loc_const_f = m_manager->mk_const_decl(m_locconst_symbol, loc_sort, func_decl_info(m_family_id, OP_LOCVAR_CONST, 1, &param));
    return m_manager->mk_const(loc_const_f);
}


app* slhv_decl_plugin::mk_uplus_value(int num_arg, expr_ref_vector items) {
    sort* heap_sort = this->mk_sort(INTHEAP_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* uplus_decl = this->mk_uplus(num_arg, domain);
    app* result = m_manager->mk_app(uplus_decl, items.data());
    return result;
}


app* slhv_decl_plugin::mk_points_to_value(int num_arg, expr_ref_vector items) {
    sort* heap_sort = this->mk_sort(INTHEAP_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* pt_decl = this->mk_points_to(num_arg, domain);
    app* result = m_manager->mk_app(pt_decl, items.data());
    return result;
}


app* slhv_decl_plugin::mk_locadd_value(int num_arg, expr_ref_vector items) {
    #ifdef SLHV_DEBUG
    std::cout << "mk locadd value" << std::endl;
    #endif
    sort* loc_sort = this->mk_sort(INTLOC_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* locadd_decl = this->mk_locadd(num_arg, domain);
    app* result = m_manager->mk_app(locadd_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_subh_value(int num_arg, expr_ref_vector items) {
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* subh_decl = this->mk_subh(num_arg, domain);
    app* result = m_manager->mk_app(subh_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_disjh_value(int num_arg, expr_ref_vector items) {
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* subh_decl = this->mk_disjh(num_arg, domain);
    app* result = m_manager->mk_app(subh_decl, items.data());
    return result;
}




app* slhv_decl_plugin::mk_readloc_value(int num_arg, expr_ref_vector items) {
    sort* loc_sort = this->mk_sort(INTLOC_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* readloc_decl = this->mk_readloc(num_arg, domain);
    app* result = m_manager->mk_app(readloc_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_readdata_value(int num_arg, expr_ref_vector items) {
    sort* data_sort = this->m_manager->mk_sort(arith_family_id, INT_SORT);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* readdata_decl = this->mk_readdata(num_arg, domain);
    app* result = m_manager->mk_app(readdata_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_writeloc_value(int num_arg, expr_ref_vector items) {
    sort* heap_sort = this->mk_sort(slhv_sort_kind::INTHEAP_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* writeloc_decl = this->mk_writeloc(num_arg, domain);
    app* result = m_manager->mk_app(writeloc_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_writedata_value(int num_arg, expr_ref_vector items) {
    sort* heap_sort = this->mk_sort(slhv_sort_kind::INTHEAP_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* writedata_decl = this->mk_writedata(num_arg, domain);
    app* result = m_manager->mk_app(writedata_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_loc2int_value(int num_arg,expr_ref_vector items) {
    sort* data_sort = this->m_manager->mk_sort(arith_family_id, INT_SORT);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* loc2int_decl = this->mk_loc2int(num_arg, domain);
    app* result = m_manager->mk_app(loc2int_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_int2loc_value(int num_arg, expr_ref_vector items) {
    sort* loc_sort = this->mk_sort(INTLOC_SORT, 0, nullptr);
    sort* domain[num_arg];
    for(int i = 0; i < num_arg; i ++) {
        domain[i] = items.get(i)->get_sort();
    }
    func_decl* int2loc_decl = this->mk_int2loc(num_arg, domain);
    app* result = m_manager->mk_app(int2loc_decl, items.data());
    return result;
}

app* slhv_decl_plugin::mk_emp_value() {
    return this->global_emp;
}

bool slhv_decl_plugin::is_loc_value(app* e) {
    return is_app_of(e, m_family_id, OP_LOCVAR_CONST);
}


slhv_util::slhv_util(ast_manager& m) :
    slhv_recognizers(m.mk_family_id("slhv")),
    m_manager(m)
{
    // do the initialization in the 
    this->slhv_plug = (slhv_decl_plugin*) m.get_plugin(this->m_fid);
    this->slhv_plug->slhv_datatype_init();
}