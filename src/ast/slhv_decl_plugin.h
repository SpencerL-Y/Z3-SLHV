
#pragma once
#include "ast/ast.h"
#include "cmd_context/cmd_context.h"

#include <map>

#define INTHEAP_SORT_STR "IntHeap"
#define INTLOC_SORT_STR "IntLoc"
// SLHV
enum slhv_sort_kind {
    INTHEAP_SORT,
    INTLOC_SORT
};

enum slhv_op_kind {
    OP_HEAP_DISJUNION,
    OP_POINTS_TO,
    OP_POINTS_TO_NEW,
    OP_LIST_SEGMENT,
    OP_HVAR_CONST,
    OP_LOCVAR_CONST,
    OP_EMP,
    OP_NIL
};

class pt_record {
    private:
        int loc_num;
        int data_num;
        std::string pt_record_name;
    public:
    pt_record(std::string name, int ln, int dn) : loc_num(ln), data_num(dn){
        this->pt_record_name = name;
    }

    std::string get_pt_record_name() {
        return this->pt_record_name;
    }

    int get_loc_num() {
        return this->loc_num;
    }

    int get_data_num() {
        return this->data_num;
    }

    int get_record_field_length() {
        return this->loc_num + this->data_num;
    }

    void print(std::ostream& os) {
        os << "( " << pt_record_name << " ( " << loc_num << ", " << data_num << "))" << std::endl;
    }
};

class slhv_decl_plugin : public decl_plugin {
    symbol m_disj_union_sym;
    symbol m_points_to_sym;
    symbol m_list_segment_sym;
    symbol curr_locvar_name;
    symbol curr_hvar_name;

    public:
    cmd_context* m_ctx;

    app* global_emp;
    app* global_nil;


    // this is the map that remembering the pt_records defined in smtlib2 file
    int record_type_num;
    
    std::map<std::string, pt_record*> pt_record_map;
    std::map<std::string, func_decl*> pt_record_decls;

    slhv_decl_plugin();

    void set_m_ctx(cmd_context* m) {
        this->m_ctx = m;
    }

    void add_pt_record(std::string record_name, int ln, int dn) {
        for(auto r : this->pt_record_map) {
            if(r.second->get_data_num() == dn && r.second->get_loc_num() == ln) {
                std::cout << "WARNING: pt record type (" << r.second->get_loc_num() << ", " << r.second->get_data_num() << ") already exists" << std::endl; 
                this->pt_record_map[record_name] = r.second;
                return;
            } 
        }
        pt_record* new_pt_r = alloc(pt_record, record_name, ln, dn);
        this->pt_record_map[record_name] = new_pt_r;
        this->record_type_num ++;
    }

    void add_pt_r_decl(std::string record_name, func_decl* pt_r) {
        if(this->pt_record_decls.find(record_name) != this->pt_record_decls.end()) {
            SASSERT(false);
        } else {
            this->pt_record_decls[record_name] = pt_r;
        }
    }

    int get_record_type_num() {
        return this->record_type_num;
    }

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

