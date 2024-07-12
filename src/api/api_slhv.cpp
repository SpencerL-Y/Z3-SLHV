#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/ast_pp.h"

extern "C" {

Z3_sort Z3_API  Z3_mk_intheap_sort(Z3_context c) {
    Z3_TRY;
    LOG_Z3_mk_intheap_sort(c);
    RESET_ERROR_CODE();
    Z3_sort r = of_sort(mk_c(c)->slhvutil().mk_intheap_sort());
    RETURN_Z3(r);
    Z3_CATCH_RETURN(nullptr);
}


Z3_sort Z3_API Z3_mk_intloc_sort(Z3_context c) {
    Z3_TRY;
    LOG_Z3_mk_intloc_sort(c);
    RESET_ERROR_CODE();
    Z3_sort r = of_sort(mk_c(c)->slhvutil().mk_intloc_sort());
    RETURN_Z3(r);
    Z3_CATCH_RETURN(nullptr);
}


Z3_ast Z3_API Z3_mk_emp(Z3_context c) {
    Z3_TRY;
    LOG_Z3_mk_emp(c);
    RESET_ERROR_CODE();
    Z3_ast emp = of_ast(mk_c(c)->slhvutil().mk_emp());
    RETURN_Z3(emp);
    Z3_CATCH_RETURN(nullptr);
}

Z3_ast Z3_API Z3_mk_nil(Z3_context c) {
    Z3_TRY;
    LOG_Z3_mk_nil(c);
    RESET_ERROR_CODE();
    Z3_ast nil = of_ast(mk_c(c)->slhvutil().mk_nil());
    RETURN_Z3(nil);
    Z3_CATCH_RETURN(nullptr);
}


Z3_ast Z3_API Z3_mk_pt(Z3_context c, Z3_ast from, Z3_ast to) {
    Z3_TRY;
    LOG_Z3_mk_pt(c, from, to);
    RESET_ERROR_CODE();
    CHECK_IS_EXPR(from, nullptr);
    CHECK_IS_EXPR(to, nullptr);
    expr* _addr = to_expr(from);
    expr* _content = to_expr(to);
    sort* addr_sort = _addr->get_sort();
    if(!mk_c(c)->slhvutil().is_intLoc(_addr)) {
        SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
        RETURN_Z3(nullptr);
    }
    if(mk_c(c)->slhvutil().is_intLoc(_content)) {
        Z3_ast result = of_ast(mk_c(c)->slhvutil().mk_points_to_loc(to_app(_addr), to_app(_content)));
        RETURN_Z3(result);
    } else if(mk_c(c)->autil().is_int(_content)) {
        Z3_ast result = of_ast(mk_c(c)->slhvutil().mk_points_to_data(to_app(_addr), to_app(_content)));
        RETURN_Z3(result);
    } else {
        SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
        RETURN_Z3(nullptr);
    }
    Z3_CATCH_RETURN(nullptr)
}



Z3_ast Z3_API Z3_mk_uplus(Z3_context c, unsigned num_args, Z3_ast const args[]) {
    Z3_TRY;
    LOG_Z3_mk_uplus(c, num_args, args);
    RESET_ERROR_CODE();
    std::vector<app*> args_vec;
    for(unsigned i = 0; i < num_args; i ++) {
        if(mk_c(c)->slhvutil().is_uplus(to_expr(args[i]))) {
            int inner_uplus_size = to_app(args[i])->get_num_args();
            for(int inner_i = 0; inner_i < inner_uplus_size; inner_i++) {
                args_vec.push_back(to_app(to_app(args[i])->get_arg(inner_i)));
            }
        } else {
            args_vec.push_back(to_app(args[i]));
        }
    }
    Z3_ast result = of_ast(mk_c(c)->slhvutil().mk_uplus(args_vec.size(), args_vec));
    RETURN_Z3(result);
    Z3_CATCH_RETURN(nullptr);
}


Z3_ast Z3_API Z3_mk_data_record(Z3_context c, Z3_ast data) {
    Z3_TRY;
    LOG_Z3_mk_data_record(c, data);
    RESET_ERROR_CODE();
    if(mk_c(c)->autil().is_int(to_expr(data))) {
        Z3_ast result = of_ast(mk_c(c)->slhvutil().mk_data_record(to_app(data)));
        RETURN_Z3(result);
    } else {
        SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
        RETURN_Z3(nullptr);
    }
    Z3_CATCH_RETURN(nullptr);
}

Z3_ast Z3_API Z3_mk_subh(Z3_context c, Z3_ast sub_h, Z3_ast large_h) {
    Z3_TRY;
    LOG_Z3_mk_subh(c, large_h, sub_h);
    RESET_ERROR_CODE();
    app* app_sub_h = to_app(sub_h);
    app* app_large_h = to_app(large_h);
    if(mk_c(c)->slhvutil().is_intHeap(app_large_h) && mk_c(c)->slhvutil().is_intHeap(app_sub_h)) {
        Z3_ast result = of_ast(mk_c(c)->slhvutil().mk_subh(to_app(sub_h), to_app(large_h)));
        RETURN_Z3(result);
    } else {
        SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
        RETURN_Z3(nullptr);
    }
    Z3_CATCH_RETURN(nullptr);
}

Z3_ast Z3_API Z3_mk_disjh(Z3_context c, Z3_ast first_h, Z3_ast second_h) {
    Z3_TRY;
    LOG_Z3_mk_disjh(c, first_h, second_h);
    RESET_ERROR_CODE();
    app* app_first_h = to_app(first_h);
    app* app_second_h = to_app(second_h);
    if(mk_c(c)->slhvutil().is_intHeap(app_first_h) && mk_c(c)->slhvutil().is_intHeap(app_second_h)) {
        Z3_ast result = of_ast(mk_c(c)->slhvutil().mk_disjh(to_app(first_h), to_app(second_h)));
        RETURN_Z3(result);
    } else {
        SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
        RETURN_Z3(nullptr);
    }
    Z3_CATCH_RETURN(nullptr);
}



bool Z3_API Z3_is_nil(Z3_context c, Z3_ast e) {
    Z3_TRY;
    LOG_Z3_is_nil(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_nil(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_emp(Z3_context c, Z3_ast e){
    Z3_TRY;
    LOG_Z3_is_emp(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_emp(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_intLoc(Z3_context c, Z3_ast e) {

    Z3_TRY;
    LOG_Z3_is_intLoc(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_intLoc(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_intHeap(Z3_context c, Z3_ast e){

    Z3_TRY;
    LOG_Z3_is_intHeap(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_intHeap(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_locvar(Z3_context c, Z3_ast e) {
    Z3_TRY;
    LOG_Z3_is_locvar(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_locvar(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_hvar(Z3_context c, Z3_ast e) {
    
    Z3_TRY;
    LOG_Z3_is_hvar(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_hvar(appe);
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_pt(Z3_context c, Z3_ast e){

    Z3_TRY;
    LOG_Z3_is_pt(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_pt(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}

bool Z3_API Z3_is_uplus(Z3_context c, Z3_ast e) {
    Z3_TRY;
    LOG_Z3_is_uplus(c, e);
    app* appe = to_app(e);
    bool result = mk_c(c)->slhvutil().is_uplus(appe);
    
    return result;
    Z3_CATCH_RETURN(false);
}


}