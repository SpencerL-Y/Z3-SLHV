#pragma once

#include "smt/smt_theory.h"
#include "ast/slhv_decl_plugin.h"
#include "model/locvar_factory.h"
#include "model/numeral_factory.h"
#include "smt/smt_model_generator.h"
#include <set>
#include <stack>
#include <vector>
#include <map>
#include <iostream>
#include <bitset>
#include <tuple>

// debug macro
// #define SLHV_PRINT
// #define DED_INFO
// #define MODEL_GEN_INFO
// #define SLHV_UNSAT_CORE_DEBUG

// minimal for debug
// #define SOLVING_INFO

// for new encoding 
// #define DISJ_DEBUG

// for inf graph debug
// #define INF_GRAPH_DEBUG

// for readwrite support
// #define SLHV_RW_DEBUG


// frontend macro

namespace smt
{
    class heap_term;
    class slhv_fresh_var_maker;
    class slhv_syntax_maker;
    class atoms_subsumption;
    class ld_recov_node;
    class slhv_deducer;
    class formula_encoder;
    class inference_graph;
    class heap_value_proc;
    class mem_management;
    class memsafe_wrapper;
    class theory_slhv : public theory {

        public:
        enum slhv_check_status {
            slhv_unsat,
            slhv_sat,
            slhv_unknown
        };

        
        // ========== FINAL CHECK USING ENCODING OVER FOMRULA WITH DISJUNCTION
        // DISJ data structure
        std::vector<app*> outside_assertions_disj;
        std::vector<app*> refined_asssertions_disj;
        // std::vector<app*> outside_loc_cnstr_disj;
        std::set<app*> refined_heap_subassertions;
        std::set<app*> inf_graph_assertions_disj;
        std::set<app*> inf_graph_data_assertions;
        std::set<app*> inf_graph_loc_assertions;std::set<std::pair<heap_term*, heap_term*>> inf_graph_eq_pairs_hterms_disj;
        // std::vector<app*> outside_data_constr_disj;
        std::set<app*> locvars_disj;
        std::set<app*> hvars_disj;
        std::set<app*> datavars_disj;
        std::set<app*> disj_unions_disj;
        std::set<app*> pts_disj;
        std::vector<app*> atomic_hterms_disj;
        
        // DISJ functions
        void preprocessing_disj();
        void collect_and_analyze_assertions_disj(std::vector<app*> outside_assertions);
        bool hvars_contain_emp_disj();
        bool locvars_contain_nil_disj();
        // DISJ TODO
        void collect_heap_subassertions_disj(std::vector<app*> outside_assertions);
        void collect_loc_data_inf_graph_assertions_disj(std::set<app*> inf_assertions);
        expr* eliminate_uplus_in_uplus_for_assertion_disj(expr* assertion);
        expr* convert_to_nnf_recursive(expr* assertion);
        std::pair<std::set<heap_term*>, std::set<std::pair<heap_term*, heap_term*>>> extract_all_hterms_disj();
        
        // =========================================================


        // =================== FINAL CHECK UNDER FRAMEWORK OF CDCL 
        // configurations for a call of final_check
        slhv_check_status check_status;

        std::set<app *> curr_locvars;
        std::set<app *> curr_hvars;
        std::set<app *> curr_datavars;
        std::set<app *> curr_disj_unions;
        std::set<app *> curr_pts;
        std::vector<app*> curr_atomic_hterms;

        std::set<app *> curr_loc_cnstr;
        std::set<app *> curr_heap_cnstr;
        std::set<app* > curr_data_cnstr;

        std::vector<expr*> curr_outside_assignments;
        std::vector<expr*> curr_inside_assignments;


        // deduction unsat core generation
        inference_graph* infer_graph;
        std::map<expr*, std::set<heap_term*>> constraint2hts;
        std::set<ld_recov_node*> ld_recovery;

        // CDCL framework functions

        // obtain assigned literals from smt_context and analyze 
        // ast to obtain all location variables, heap variables for later use
        // analyze all terms to do preprocessing later
        void preprocessing(expr_ref_vector assigned_literals);

        bool curr_locvars_contain_nil();
        bool curr_hvars_contain_emp();

        // formula rewritting
        std::vector<expr*> eliminate_not_or_assignments(expr* expression);
        expr* eliminate_uplus_in_uplus_for_assignments(expr* expression);
        app* eliminate_uplus_uplus_hterm(app* hterm);

        std::vector<expr_ref_vector> eliminate_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals);
        std::vector<expr_ref_vector> remove_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals);
        std::vector<std::vector<expr*>> eliminate_heap_equality_negation(std::vector<std::vector<expr*>> elimnated_neg_vec, expr* curr_neg_lit);  
        // preprocessing functions
        void collect_and_analyze_assignments(expr_ref_vector assigned_literals);
        void collect_loc_heap_and_data_cnstr_in_assignments(expr_ref_vector assigned_literals);
        // heap term construction functions
        std::pair<std::set<std::pair<heap_term*, heap_term*>>, std::set<heap_term*>>  extract_all_hterms();
        void print_all_hterms(std::ostream& os);

        // =========================================================

        // ========== COMMON DATA STRUCTURE AND FUNCTIONS
        // to create formula while solving
        slhv_syntax_maker* syntax_maker;
        slhv_decl_plugin* slhv_plug;
        memsafe_wrapper* msw;
        // special constant
        app* global_emp;
        app* global_nil;
        
        // remember for each heap term which pt it subsumes
        std::set<atoms_subsumption*> model_subsume_info;
        std::map<std::string, int> model_loc_data_var_val_info;
        

        // model generation
        arith_factory* data_factory;
        std::map<app*, std::set<app*>> hvar2ptset;
        std::map<enode*, heap_value_proc*> enode2proc;
        // memory management
        mem_management* mem_mng;
        // preprocessing functions
        std::tuple<std::set<app* >, std::set<app *>, std::set<app *>> 
        collect_vars(app* expression);
        std::set<app*> collect_disj_unions(app* expression);
        std::set<app*> collect_points_tos(app* expression);

        // syntax checker
        bool contain_disjunction(app const * n);
        bool is_uplus(app const* n) const {
            return n->is_app_of(get_id(), OP_HEAP_DISJUNION);
        }
        bool is_points_to(app const* n) const {
            return n->is_app_of(get_id(), OP_POINTS_TO);
        }
        bool is_hvar(app const* n) const {
            return n->is_app_of(get_id(), OP_HVAR_CONST);
        } 
        bool is_locvar(app const* n) const {
            return n->is_app_of(get_id(), OP_LOCVAR_CONST);
        }
        bool is_atom_hterm(app const* n) const {
            return (is_points_to(n) || is_hvar(n) || is_emp(n));
        }
        bool is_locadd(app const* n) const {
            if(n->is_app_of(get_id(), OP_LOCADD)) {
                SASSERT(this->is_locvar(n) && this->is_dataterm(n));
                return true;
            }
            return false;
        }
        bool is_readloc(app const* n) const {
            if(n->is_app_of(get_id(), OP_READLOC)) {
                return true;
            }
            return false;
        }
        bool is_readdata(app const* n) const {
            if(n->is_app_of(get_id(), OP_READDATA)) {
                return true;
            }
            return false;
        }
        bool is_writeloc(app const* n) const {
            if(n->is_app_of(get_id(), OP_WRITELOC)) {
                return true;
            }
            return false;
        }
        bool is_writedata(app const* n) const {
            if(n->is_app_of(get_id(), OP_WRITEDATA)) {
                return true;
            }
            return false;
        }
        bool is_loc2int(app const* n) const {
            if(n->is_app_of(get_id(), OP_LOC2INT)) {
                return true;
            }
            return false;
        }
        bool is_int2loc(app const* n) const {
            if(n->is_app_of(get_id(), OP_INT2LOC)) {
                return true;
            }
            return false;
        }
        bool is_datavar(app const* n) const {
            // TODO: maybe buggy here
            if(n->get_num_args() == 0 && n->get_sort() == this->m.mk_sort(arith_family_id, INT_SORT)) {
                return true;
            } else {
                return false;
            }
        }
        bool is_emp(app const* n) const {
            return n->is_app_of(get_id(), OP_EMP);
        }
        bool is_nil(app const* n) const {
            return n->is_app_of(get_id(), OP_NIL);
        }
        bool is_heapterm(app const* n) const {
            return (n->get_sort()->get_name() == INTHEAP_SORT_STR);
        }
        bool is_locterm(app const* n) const {
            return (n->get_sort()->get_name() == INTLOC_SORT_STR);
        }
        bool is_dataterm(app const* n) const {
            return n->get_sort() == this->get_manager().mk_sort(arith_family_id, INT_SORT);
        }
        bool is_recordterm(app const* n) const {
            if(this->slhv_plug->pt_record_map.find(n->get_name().bare_str()) != this->slhv_plug->pt_record_map.end()) {
                return true;
            } else {
                return false;
            }
            return false;
        }

        bool is_arith_formula(app* l);
        bool is_not_heap_or_loc_formula(app* l);
        pt_record* analyze_pt_record_type(app* record_app);

        private:
        // final check interfaces:
        bool final_check();  
        bool final_check_using_CDCL();
        bool final_check_using_DISJ();

        bool internalize_term_core(app * term);
        void reset_inside_configs();
        void reset_outside_configs();

        // checking logic

        std::set<atoms_subsumption*> parse_and_collect_subsumption(formula_encoder* enc, std::set<std::string> true_bool_strs); 
        
        public:
        theory_slhv(context& ctx);
        

        ~theory_slhv() override {}
        
        void display(std::ostream & out) const override;
        // interface of class theory
        theory *mk_fresh(context * new_ctx) override;

        theory_var mk_var(enode* n);


        bool  internalize_atom(app * atom, bool gate_ctx) override;

        bool internalize_term(app * term) override;

        void new_eq_eh(theory_var v1, theory_var v2) override;

        void new_diseq_eh(theory_var v1, theory_var v2) override;

        char const * get_name() const override{ return "slhv"; }

        
       

        final_check_status final_check_eh() override {
            bool result = this->final_check();
            if(result) std::cout << "FINAL CHECK DONE" << std::endl;
            return result ? FC_DONE : FC_CONTINUE;
        }
        // model generation
        void init_model(model_generator & mg) override;
        /**
           \brief Return true if the theory has something to propagate
        */

        bool build_models() const override { 
            return true;
        }

        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        std::vector<int> generate_count_vector_by_app(app* hterm);

        bool can_propagate() override {
            return false;
        }        
        

        // statistics

        int calculate_atomic_proposition(app* encoded_form);


        
        
        /**
           \brief This method is invoked to give a theory a chance to perform
           theory propagation.
        */
        void propagate() override;

        std::set<expr*> extract_unsat_core_booleans(expr* e);
        std::set<expr*> recover_unsat_core(formula_encoder* fec, expr_ref_vector unsat_core);


        void set_conflict_slhv();

        // set UNSAT core for outside CDCL framework
        void set_conflict_slhv(std::vector<expr*> outside_unsat_core);

        void set_conflict_slhv(inference_graph* inf_graph);


        void set_conflict_slhv_empty();



        literal_vector compute_current_unsat_core(std::vector<expr*> outside_unsat_core);

        literal_vector compute_unsat_core_by_inference_graph(inference_graph* inf_graph);

        // set UNSAT core and equivalence realtion for inner branch cutting
        void set_conflict_inside();
        void set_conflict_inside(std::vector<expr*> inner_unsat_core);
        

        // void finalize_model(model_generator & m) override;



        // // virtual methods of class theory
        // public:
        // app * mk_eq_atom(expr * lhs, expr * rhs) override {
        //     #ifdef SLHV_DEBUG
        //     std::cout << "slhv theory: mk_eq_atom" << std::endl;
        //     #endif
        //     ast_manager& m = get_manager();
        //     if (lhs->get_id() > rhs->get_id())
        //         std::swap(lhs, rhs);
        //     if (m.are_distinct(lhs, rhs))                
        //         return m.mk_false();
        //     if (m.are_equal(lhs, rhs))
        //         return m.mk_true();
        //     return get_manager().mk_eq(lhs, rhs);
        // }
        // protected:
        // theory_var mk_var(enode * n) override{
        //     #ifdef SLHV_DEBUG
        //     std::cout << "slhv theory: mk_var" << std::endl;
        //     #endif
        //     SASSERT(!is_attached_to_var(n));
        //     theory_var v = m_var2enode.size();
        //     m_var2enode.push_back(n);
        //     return v;
        // }
        // /**
        //    \brief Return true if the theory uses default internalization:
        //    "the internalization of an application internalizes all arguments".
        //    Theories like arithmetic do not use default internalization.
        //    For example, in the application (+ a (+ b c)), no enode is created
        //    for (+ b c).
        // */        
        // bool default_internalizer() const override{
        //     return true;
        // }
        // /**
        //    \brief Apply (interpreted) sort constraints on the given enode.
        // */
        // virtual void apply_sort_cnstr(enode * n, sort * s) {
        // }
        // /**
        //    \brief This method is invoked when a truth value is 
        //    assigned to the given boolean variable.
        // */
        // virtual void assign_eh(bool_var v, bool is_true) {
        // }
        // /**
        //    \brief use the theory to determine phase of the variable.
        // */
        // virtual lbool get_phase(bool_var v) {
        //     return l_undef;
        // }

        // /**
        //    \brief Return true if the theory does something with the
        //    disequalities implied by the core.
        // */
        // virtual bool use_diseqs() const { 
        //     return true; 
        // }

        // /**
        //    \brief This method is invoked when the theory application n
        //    is marked as relevant.
        //  */
        // virtual void relevant_eh(app * n) {
        // }
        //  /**
        //    \brief This method is invoked when a new backtracking point
        //    is created.
        // */
        // virtual void push_scope_eh();

        // /**
        //    \brief This method is invoked during backtracking.
        // */
        // virtual void pop_scope_eh(unsigned num_scopes);

        // /**
        //    \brief This method is invoked when the logical context is being
        //    restarted.
        // */
        // virtual void restart_eh() {
        // }

        // /**
        //    \brief This method is called by smt_context before the search starts
        //    to get any extra assumptions the theory wants to use.
        //    (See theory_str for an example)
        // */
        // virtual void add_theory_assumptions(expr_ref_vector & assumptions) {
        // }

        // /**
        //    \brief This method is called from the smt_context when an unsat core is generated.
        //    The theory may change the answer to UNKNOWN by returning l_undef from this method.
        // */
        // virtual lbool validate_unsat_core(expr_ref_vector & unsat_core) {
        //     return l_false;
        // }

        // /**
        //    \brief This method is called from the smt_context when an unsat core is generated.
        //    The theory may tell the solver to perform iterative deepening by invalidating
        //    this unsat core and increasing some resource constraints.
        // */
        // virtual bool should_research(expr_ref_vector & unsat_core) {
        //     return false;
        // }

        // /**
        //    \brief This method is invoked before the search starts.
        // */
        // virtual void init_search_eh() {
        // }

        // /**
        //    \brief This method is invoked when the logical context assigned
        //    a truth value to all boolean variables and no inconsistency was 
        //    detected.
        // */
        // virtual final_check_status final_check_eh() {
        //     return FC_DONE;
        // }

        // /**
        //    \brief Parametric theories (e.g. Arrays) should implement this method.
        //    See example in context::is_shared
        // */
        // virtual bool is_shared(theory_var v) const {
        //     return false;
        // }

        // /**
        //    \brief Determine if node \c n under parent \c p is in a beta redex position.
        // */
        // virtual bool is_beta_redex(enode* p, enode* n) const {
        //     return false;
        // }
    

        
        // /**
        //    \brief This method allows a theory to contribute to
        //    disequality propagation.
        // */
        // virtual justification * why_is_diseq(theory_var v1, theory_var v2) {
        //     return nullptr;
        // }

        // /**
        //    \brief Just releases memory.
        // */
        // virtual void flush_eh() {
        // }

        // /**
        //    \brief This method is invoked when the logical context is being reset.
        // */
        // virtual void reset_eh();

        // // ----------------------------------------------------
        // //
        // // Model validation 
        // //
        // // ----------------------------------------------------

        // virtual void validate_model(model& mdl) {}

        // public:
        // /**
        //    \brief This method is invoked when a theory atom is used
        //    during conflict resolution. This allows the theory to bump
        //    the activity of the enodes contained in the given atom.
        // */
        // virtual void conflict_resolution_eh(app * atom, bool_var v) {
        // }

        // virtual void setup() {}

        // virtual void init() {}

        // virtual bool is_safe_to_copy(bool_var v) const { return true; }

        // virtual void display(std::ostream & out) const = 0;

        // virtual void display_var2enode(std::ostream & out) const;
        
        // virtual void collect_statistics(::statistics & st) const {
        // }

        // // -----------------------------------
        // //
        // // Model generation
        // //
        // // -----------------------------------

        // /**
        //    \brief Return true if theory support model construction
        // */


        // virtual void init_model(model_generator & m) {
        // }

        // virtual void finalize_model(model_generator & m) {
        // }
        
        // /**
        //    \brief Return a functor that can build the value (interpretation) for n.
        // */
        

        // virtual bool include_func_interp(func_decl* f) {
        //     return false;
        // }

        // // -----------------------------------
        // //
        // // Model checker
        // //
        // // -----------------------------------

        // virtual bool get_value(enode * n, expr_ref & r) {
        //     return false;
        // }

        // virtual char const * get_name() const { return "unknown"; }

        // /**
        //  * \brief theory plugin for fixed values.
        //  */
        // virtual bool is_fixed_propagated(theory_var v, expr_ref& val, literal_vector & explain) { return false; }
    };


// heap term class

    class heap_term {
        private:
            theory_slhv* th;
            std::vector<app*> atomic_hterms_vec;
            std::vector<int> atomic_hterms_count;
        public:
            heap_term(theory_slhv* th, std::vector<app*> atomics, std::vector<app*> atoms);
            heap_term(theory_slhv* th, std::vector<app*> atomics, std::vector<int> atoms_count): th(th), atomic_hterms_vec(atomics), atomic_hterms_count(atoms_count) {
            }

            bool is_subhterm_of(heap_term* ht);
            bool is_suphterm_of(heap_term* ht);
            heap_term* intersect_with(heap_term* ht);
            heap_term* disj_union_with(heap_term* ht);

            std::vector<app*> get_atoms();

            std::vector<app*> get_atomic_hterm_vec() const{
                return this->atomic_hterms_vec;
            }
            std::vector<int> get_atomic_count() const{
                return this->atomic_hterms_count;
            }
            int get_vec_size() {
                return this->atomic_hterms_vec.size();
            }
            int get_pos(int pos) const{
                return this->atomic_hterms_count[pos];
            }

            bool is_emp();

            bool is_atom_pt();

            bool is_atom_hvar();

            bool is_uplus_hterm();

            int get_pt_num();

            int get_hvar_num();

            int get_emp_num();

            std::set<heap_term*>  get_subhterms();
            std::set<std::vector<int>> get_atomic_subhterms_counts();
            void print(std::ostream& os);

            std::set<std::pair<std::vector<int>, std::vector<int>>> get_splitted_subpairs();

            std::set<std::pair<std::vector<int>, std::vector<int>>> get_all_distinct_atomic_pairs();

            void print_ht();
            void print_ht2file(std::ofstream& f);
    };



    // encoder from slhv to lia
    class formula_encoder {
        private:
        std::map<std::pair<int, int>, app*> djrel_var_map;
        std::map<std::pair<int, int>, app*> shrel_var_map;
        std::map<app*, std::pair<int, int>> djrel_var2pair;
        std::map<app*, std::pair<int, int>> shrel_var2pair;
        std::map<heap_term*, int> ht2index_map;
        std::vector<heap_term*> index2ht;

        std::map<app*, app*> locvar2intvar_map;

        bool unsat_found = false;


        std::set<heap_term*> hts;
        std::set<std::pair<heap_term*, heap_term*>> eq_ht_pairs;
        std::set<heap_term*> atom_hts;
        std::set<heap_term*> pt_hts;
        std::set<heap_term*> hvar_hts;
        std::map<heap_term*, heap_term*> ht2root;
        std::set<heap_term*> repre_hts;
        std::set<heap_term*> repre_pts;
        std::set<heap_term*> repre_hvars;
        std::set<heap_term*> repre_atoms;
        heap_term* emp_ht;

        theory_slhv* th;
        slhv_deducer* ded;
        slhv_syntax_maker* syntax_maker;

        void construct_ht2root_from_deducer();
        void construct_ht2root_from_nothing();
        void construct_ht2root_from_deducer_disj();

        std::set<heap_term*> get_sub_atom_hts(heap_term* orig_ht);

        expr* translate_locdata_formula(expr* formula);
        app* translate_locterm_to_liaterm(app* locterm);
        public:
        
        // formula encoder for CDCL
        formula_encoder(theory_slhv* th, std::set<heap_term*> all_hterms, std::set<std::pair<heap_term*, heap_term*>> eq_hterm_pairs);


        // formula encoder for disj enc
        formula_encoder(theory_slhv* th, std::set<heap_term*> all_hterms);
        
        app* get_shrel_boolvar(heap_term* subht, heap_term* supht);
        app* get_djrel_boolvar(heap_term* firstht, heap_term* secondht);
        std::pair<std::pair<int, int>, bool> get_boolvar_id_type(app* boolvar);
        heap_term* get_ht_by_id(int id) {
            return this->index2ht[id];
        }
        app* locvar2intvar(app* locvar);

        std::set<expr*> generate_deduced_assumptions();
        std::pair<std::set<expr*>, std::set<ld_recov_node*>> generate_ld_assumptions();
        std::set<expr*> generate_init_assumptions();
        std::set<expr*> generate_pto_assumptions();
        std::set<expr*> generate_iso_assumptions();
        std::set<expr*> generate_idj_assumptions();
        std::set<expr*> generate_final_assumptions();


        expr* generate_deduced_premises();
        expr* generate_ld_formula();
        expr* generate_init_formula();
        expr* generate_pto_formula();
        expr* generate_iso_formula();
        expr* generate_idj_formula();
        expr* generate_final_formula();

        // hard encoded formula
        expr* generate_loc_var_constraints();

        //  ======================== for disj
        std::set<expr*> generate_init_ld_locvar_constraint_for_all_assertions();
        std::set<expr*> generate_deduced_assumptions_disj();
        std::set<expr*> generate_pto_assumptions_disj();
        std::set<expr*> generate_iso_assumptions_disj();
        std::set<expr*> generate_idj_assumptions_disj();
        std::set<expr*> generate_final_assumptions_disj();


        // disj auxillary formulas
        expr* generate_init_ld_locvar_constraint_recursive(app* assertion);
        expr* generate_init_ld_locvar_constraint_for_generate_ap(app* ap);
        expr* generate_init_ld_locvar_constraint_for_hteq(app* heq);
        heap_term* find_heap_term_for_ht_disj(app* orig_ht);

        std::set<app*> collect_locvars_recursive(app* term);
        std::set<app*> collect_hteq_all_pts(app* hteq);

        //  ======================== 

        expr* generate_nil_constraint();

        // ========== encoding interfaces ============
        std::pair<expr*, expr_ref_vector> encode();

        std::pair<expr*, expr_ref_vector> encode_with_ass();

        std::set<expr*> encode_for_disj();



        std::pair<heap_term*, heap_term*> get_ht_pair_by_vec_pair(std::pair<std::vector<int>, std::vector<int>> vec_pair);

        std::map<heap_term*, int> get_ht2index_map() {
            return this->ht2index_map;
        }
        std::vector<heap_term*> get_index2ht() {
            return this->index2ht;
        }
        std::set<heap_term*> get_all_hterms() {
            return this->hts;
        }
        std::set<std::pair<heap_term*, heap_term*>> get_eq_ht_pairs() {
            return this->eq_ht_pairs;
        }
        heap_term* get_emp_ht() {
            return this->emp_ht;
        }
        theory_slhv* get_th() {
            return this->th;
        }
        bool get_unsat_found() {
            return this->unsat_found;
        }
        void print_statistics() {
            std::cout << "Number of heap terms: " << this->hts.size() << std::endl;
            std::cout << "Number of aht: " << this->atom_hts.size() << std::endl;
            std::cout << "Number of locvars: " << this->locvar2intvar_map.size() << std::endl;
        }
    };

    // deducer is used to simplify the formula. It is used to deduce subheap and disjoint relation before encoding and find trivial unsat situations.

    class slhv_deducer {
        private:
            theory_slhv* th;
            formula_encoder* fec;
            std::vector<heap_term*> index2ht;
            std::map<heap_term*, int> ht2index;

            bool unsat_found;

            // data structure used for deduction
            std::set<std::pair<int, int>> shpair_set;
            std::set<std::pair<int, int>> djpair_set;

            std::map<int, std::set<std::pair<int, int>>> sh_pair_1st_elem_map;
            std::map<int, std::set<std::pair<int, int>>> sh_pair_2nd_elem_map;
            std::map<int, std::set<std::pair<int, int>>> dj_pair_1st_elem_map;
            std::map<int, std::set<std::pair<int, int>>> dj_pair_2nd_elem_map;

            bool insert_sh_pair(std::pair<int, int> sh_pair, std::set<std::pair<int, int>>& nxt_sh_pair_set, std::map<int, std::set<std::pair<int, int>>>& nxt_sh_1nd_elem_map, std::map<int, std::set<std::pair<int, int>>>& nxt_sh_2nd_elem_map);
            bool insert_dj_pair(std::pair<int, int> dj_pair, std::set<std::pair<int, int>>& nxt_dj_pair_set, std::map<int, std::set<std::pair<int, int>>>& nxt_dj_1nd_elem_map, std::map<int, std::set<std::pair<int, int>>>& nxt_dj_2nd_elem_map);  
            bool insert_sh_pair(std::pair<int, int> sh_pair);
            bool insert_dj_pair(std::pair<int, int> dj_pair);  

            std::map<app*, app*> ldvar2eqroot;
            std::map<app*, std::set<app*>> ldvar2neqvars;

            void initialize_shdj();
            void initialize_ldeqneq();

            void initialize_shdj_disj();
            void initialize_ldeqneq_disj();
            
            // -----Check inconsistency-------
            void check_ldvars_consistency();
            void check_sh_of_emp();
            void check_pt_addr_nil();
            // -----Theory propagation----
            bool propagate_eq_neq();
            bool propagate_shdj_by_eq_neq();
            bool propagate_transitive_sh();
            bool propagate_transitive_dj();

            bool add_ld_eq_vars(app* v1, app* v2);
            bool add_ld_neq_vars(app* v1, app* v2);

            bool is_pt(int index);
            bool is_emp(int index);
            bool is_hvar(int index);

            bool has_dj_pair(std::pair<int, int> dj_p);
            bool has_sh_pair(std::pair<int, int> sh_p);
        public: 
            slhv_deducer(theory_slhv* th, formula_encoder* fec, bool is_disj);

            void print_current(std::ostream& os);
            bool deduce();
            bool get_is_unsat() {
                return this->unsat_found;
            }
            std::set<std::pair<int, int>> get_sh_pair_set() {
                return  this->shpair_set;
            }
            std::set<std::pair<int, int>> get_dj_pair_set() {
                return this->djpair_set;
            }

            std::map<app*, app*> get_ldvar2eqroot() {
                return this->ldvar2eqroot;
            }

            std::map<app*, std::set<app*>> get_ldvar2neqvars() {
                return this->ldvar2neqvars;
            }

            bool has_shrel(int ht1, int ht2) {
                if(this->shpair_set.find({ht1, ht2}) != this->shpair_set.end()) {
                    return true;
                }
                return false;
            }

            bool has_djrel(int ht1, int ht2) {
                if(this->djpair_set.find({ht1, ht2}) != this->djpair_set.end() ||
                   this->djpair_set.find({ht2, ht1}) != this->djpair_set.end()) {
                        return true;
                   }
                return false;
            }
    };

    class ld_recov_node {
        public:
            expr* original_formula;
            expr* translated_formula;

            ld_recov_node(expr* orig, expr* trans) {
                this->original_formula = orig;
                this->translated_formula = trans;
            }
    };




// heap term atoms contained
    class atoms_subsumption {
        private: 
            heap_term* main_heap_term;
            std::set<heap_term*> pt_atoms;
        public:
            atoms_subsumption(heap_term* m, std::set<heap_term*> pts) : main_heap_term(m), pt_atoms(pts) {
                
            }
            heap_term* get_main_heap_term() {
                return this->main_heap_term;
            }
            std::set<heap_term*> get_pt_atoms() {
                return this->pt_atoms;
            }
    };
// unsat core finder, used to record the inference path

    class inf_node {
        private:
            bool is_outside_assignment;
            expr* outside_assignment;

            bool is_refined_assignment;
            expr* refined_assignment;

            bool is_compound_heap_term;
            heap_term* compound_ht;

            bool is_ht_eq_pair;
            std::pair<heap_term*, heap_term*> ht_eq_pair;

            bool is_dj_rel;
            std::pair<int, int> dj_pair;
            
            bool is_sh_rel;
            std::pair<int, int> sh_pair;

            bool is_eq_class;
            
            std::set<inf_node*> premises;
            bool is_conflict_node;
        public:
            inf_node(expr* outside);
            inf_node(expr* refined_assignment, std::set<inf_node*> premises);
            inf_node(std::pair<heap_term*, heap_term*> ht_eq_pair, std::set<inf_node*> premises);
            inf_node(heap_term* com_ht, std::set<inf_node*> premises);
            inf_node(std::pair<int, int> pair, bool is_dj, bool is_sh, std::set<inf_node*> premises);
            inf_node(std::set<inf_node*> premises);

            std::set<inf_node*> get_premises() {
                return this->premises;
            }
            bool get_is_outside_assignment() {
                return this->is_outside_assignment;
            }
            bool get_is_refined_assignment() {
                return this->is_refined_assignment;
            }
            bool get_is_compound_heap_term() {
                return this->is_compound_heap_term;
            }
            bool get_is_ht_eq_pair() {
                return this->is_ht_eq_pair;
            }
            bool get_is_dj_rel() {
                return this->is_dj_rel;
            }
            bool get_is_sh_rel() {
                return this->is_sh_rel;
            }
            bool get_is_eq_class() {
                return this->is_eq_class;
            }
            bool get_is_conflict_node() {
                return this->is_conflict_node;
            }

            expr* get_outside_assignment() {
                return this->outside_assignment;
            }

            expr* get_refined_assignment() {
                return this->refined_assignment;
            }

            heap_term* get_compound_ht() {
                return this->compound_ht;
            }

            std::pair<heap_term*, heap_term*> get_ht_eq_pair() {
                return this->ht_eq_pair;
            }

            std::pair<int, int>  get_dj_pair() {
                return this->dj_pair;
            }
            
            std::pair<int, int>  get_sh_pair() {
                return this->sh_pair;
            }

            // TODO: compute the minimal conflict sources
            std::set<inf_node*> get_conflict_sources();

            void reset_configs();
            void set_conflict() {
                this->is_conflict_node = true;
            }


    };

    class inference_graph {
        public:
            theory_slhv* th;
            std::set<inf_node*> nodes;
            std::set<inf_node*> outside_nodes;
            std::set<inf_node*> refine_nodes;
            std::set<inf_node*> compound_nodes;
            std::set<inf_node*> ht_eq_pair_nodes;
            std::set<inf_node*> disj_rel_nodes;
            std::set<inf_node*> sh_rel_nodes;
            inf_node* newest_loc_eq_node;
            inf_node* newest_loc_neq_node;
            inf_node* newest_data_eq_node;
            inf_node* newest_data_neq_node;

            std::set<inf_node*> conflict_nodes;

            std::set<expr*> unsat_core;

            inference_graph(theory_slhv* th, std::set<expr*> initial_assignments);

            inf_node* get_outside_assignment_premise(expr* out_assignment);
            inf_node* get_refine_assignment_premise(expr* refine_assignment);
            inf_node* get_compound_ht_premise(heap_term* com_ht);
            inf_node* get_ht_eq_pair_premise(std::pair<heap_term*, heap_term*> ht_p);
            inf_node* get_disj_rel_premise(std::pair<int, int> disj_p);
            inf_node* get_sh_rel_premise(std::pair<int, int> sh_p);

            bool contain_dj_node(std::pair<int, int> dj_p);
            bool contain_sh_node(std::pair<int, int> sh_p);

            bool contain_comht_node(heap_term* com_ht);

            void create_init_assignment_node(expr* init_ass);
            void add_refined_assignment_node(expr* new_assignment, expr* old_assignment);
            void add_compound_ht_node(heap_term* com_ht, expr* refined_assignment);
            void add_ht_eq_pair_node(std::pair<heap_term*, heap_term*> ht_eq_p, expr* refined_assignment);
            void add_loc_eqclass_node(std::set<app*> loc_eq_constr);
            void add_data_eqclass_node(std::set<app*> data_eq_constr);
            void add_loc_neqclass_node(std::set<app*> loc_neq_constr);
            void add_data_neqclass_node(std::set<app*> data_neq_constr);
            
            void add_data_neqclass_node(std::pair<int, int> dj_pair);
            void add_loc_neqclass_node(std::pair<int, int> dj_pair);
            void add_data_eqclass_node(std::pair<int, int> sh_pair);
            void add_loc_eqclass_node(std::pair<int, int> sh_pair);


            void add_disj_rel_pair(std::pair<int, int> dj_p, heap_term* com_ht);
            void add_disj_rel_pair_locdata_neqclass(std::pair<int, int> dj_p, std::pair<int, int> pt1InHt, std::pair<int, int> pt2InHt);
            void add_disj_rel_pair(std::pair<int, int> dj_p, std::pair<int, int> ht1InHt3, std::pair<int, int> ht2InHt4, std::pair<int, int> ht3DjHt4);



            void add_sh_rel_pair(std::pair<int, int> sh_p, heap_term* com_ht);
            void add_sh_rel_pair(std::pair<int, int> sh_p, std::pair<heap_term*, heap_term*> ht_eq_p);
            void add_sh_rel_pair_locdata_eqclass(std::pair<int, int> sh_p, std::pair<int, int> pt1InHt, std::pair<int, int> pt2InHt);
            void add_isolated_sh_rel_pair(std::pair<int, int> sh_p);

            void add_sh_rel_pair(std::pair<int, int> sh_p, std::pair<int, int> ht1InHt2, std::pair<int, int> ht2InHt3);

            void set_curr_loc_eqneq_unsat_node();
            void set_curr_data_eqneq_unsat_node();
            void set_sh_emp_unsat_node(std::pair<int, int> sh_emp_p);

            void set_dj_unsat_node(std::pair<int, int> dj_pair);
            void set_sh_unsat_node(std::pair<int, int> sh_pair);


            std::set<expr*> compute_unsat_core_expressions();
    };

// util class
    class slhv_util {
        public:
        template<typename T>
        static std::set<T> setUnion(std::set<T> s1, std::set<T> s2) {
            std::set<T> result;
            for(T e : s1) {
                result.insert(e);
            }
            for(T e : s2) {
                result.insert(e);
            }
            return result;
        }

        template<typename T>
        static bool setEqual(std::set<T> s1, std::set<T> s2) {
            for(T t1 : s1) {
                if(s2.find(t1) == s2.end()) {
                    return false;
                }
            }
            for(T t2 : s2) {
                if(s1.find(t2) == s1.end()) {
                    return false;
                }
            }
            return true;
        }

        template<typename T>
        static bool setIsSubset(std::set<T> larger, std::set<T> smaller) {
            for(T t : smaller) {
                if(larger.find(t) == larger.end()) {
                    return false;
                }
            }
            return true;
        }

        template<typename T>
        static std::set<T> setSubstract(std::set<T> substracted, std::set<T> substractor) {
            std::set<T> result;
            for(T t : substracted) {
                if(substractor.find(t) == substractor.end()) {
                    result.insert(t);
                }
            }
            return result;
        }

        template<typename T>
        static bool pairSetHasElement(std::set<std::pair<T, T>> pairset, std::pair<T, T> elem) {
            for(std::pair<T, T> p : pairset) {
                if(p.first == elem.first && p.second == elem.second) {
                    return true;
                }
            }
            return false;
        }

        template<typename T>
        static std::vector<T> vecConcat(std::vector<T> v1, std::vector<T> v2) {
            std::vector<T> result;
            for(T t1 : v1) {
                result.push_back(t1);
            }
            for(T t2 : v2) {
                result.push_back(t2);
            }
            return result;
        }

        template<typename T>
        static std::vector<T> vecIncluded(std::vector<T> larger, std::vector<T> smaller) {
            std::map<T, int> larger_map;
            std::map<T, int> smaller_map;
            for(T t : larger) {
                if(larger_map.find(t) != larger_map.end()) {
                    larger_map[t] += 1;
                } else {
                    larger_map[t] = 1;
                }
            }
            for(T t : smaller) {
                if(smaller_map.find(t) != smaller_map.end()) {
                    smaller_map[t] += 1;
                } else {
                    smaller_map[t] = 1;
                }
            }
            for(auto pair : smaller_map) {
                if(larger_map.find(pair.first) == larger_map.end()) {
                    return false;
                } else {
                    if(larger_map[pair.first] < pair.second) {
                        return false;
                    }
                }
            }
            return true;
        }

        template<typename T>
        static std::vector<T> vecEqual(std::vector<T> first, std::vector<T> second) {
            std::map<T, int> first_map;
            std::map<T, int> second_map;
            for(T t : first) {
                if(first_map.find(t) != first_map.end()) {
                    first_map[t] += 1;
                } else {
                    first_map[t] = 1;
                }
            }
            for(T t : second) {
                if(second_map.find(t) != second_map.end()) {
                    second_map[t] += 1;
                } else {
                    second_map[t] = 1;
                }
            }
            for(auto pair : second_map) {
                if(first_map.find(pair.first) == first_map.end()) {
                    return false;
                } else {
                    if(first_map[pair.first] != pair.second) {
                        return false;
                    }
                }
            }
            return true;
        }

        template<typename T>
        static std::set<T> setIntersect(std::set<T> set1, std::set<T> set2) {
            std::set<T> result;
            for(T t1 : set1) {
                if(set2.find(t1) != set2.end()) {
                    result.insert(t1);
                }
            }
            return result;
        }

        static std::vector<std::string> str_split(std::string str, std::string pattern) {
            std::string::size_type pos;
            std::vector<std::string> result;
            str += pattern;
            int size = str.size();
            for (int i = 0; i < size; i ++) {
                pos = str.find(pattern, i);
                if(pos == std::string::npos) {
                    std::cout << "problematic str: " << str << std::endl;
                }
                if(pos < size) {
                    std::string s = str.substr(i, pos-i);
                    result.push_back(s);
                    i = pos + pattern.size() - 1;
                }
            }
            return result;
        }
    };

// fresh_var_maker
    class slhv_fresh_var_maker {
    private:
        theory_slhv* th;
        int curr_locvar_id;
        int curr_hvar_id;
        int curr_datavar_id;
        int curr_boolvar_id;
        std::map<int, app*> locvar_map;
        std::map<int, app*> hvar_map;
        std::map<int, app*> datavar_map;
        std::map<int, app*> boolvar_map;
        slhv_decl_plugin* fe_plug;
    public:
        slhv_fresh_var_maker(theory_slhv* t);

        app* mk_fresh_locvar();
        app* mk_fresh_hvar();
        app* mk_fresh_datavar();
        app* mk_fresh_boolvar();

        void reset();
    };
// syntax maker
    class slhv_syntax_maker {
        private:
        theory_slhv* th;
        slhv_decl_plugin* slhv_decl_plug;
        slhv_fresh_var_maker* fv_maker;
        memsafe_wrapper* msw;
        arith_util* a;

        public: 
        // var maker
        void reset_fv_maker();
        slhv_syntax_maker(theory_slhv* t, memsafe_wrapper* msw);
        app* mk_fresh_locvar();
        app* mk_fresh_hvar();
        app* mk_fresh_boolvar();
        // operation maker
        app* mk_and(expr* lhs, expr* rhs);
        app* mk_implies(expr* lhs, expr* rhs);
        app* mk_not(expr* inner);
        app* mk_and(expr* arg1, expr* arg2, expr* arg3);
        app* mk_and(int num_args, expr* const* args);
        app* mk_simplify_and(expr* f1, expr* f2);
        app* mk_or(expr* lhs, expr* rhs);
        app* mk_or(expr* arg1, expr* arg2, expr* arg3);
        app* mk_or(int num_args, expr* const* args);
        app* mk_eq(expr* lhs, expr* rhs);
        app* mk_distinct(expr* lhs, expr* rhs);

        // syntax sugar maker
        app* mk_read_formula(app* from_hvar, app* read_addr, app* read_data);
        app* mk_write_formula(app* orig_hvar, app* writed_hvar, app* write_addr, app* write_data);
        app* mk_addr_in_hterm(app* hterm, app* addr);
        app* mk_addr_notin_hterm(app* hterm, app* addr);
        std::vector<std::vector<app*>> mk_hterm_disequality(app* lhs, app* rhs);

        app* mk_uplus_app(int num_arg, std::vector<app*> hterm_args);
        app* mk_points_to(app* addr_loc, app* data_loc);

        // logic with record:

        app* mk_points_to_new(app* addr_loc, app* record_loc); 

        app* mk_fresh_datavar(); 
        app* mk_lia_intvar(std::string name);
        app* mk_lia_intconst(int constval);
        app* mk_boolvar(std::string name);
        std::vector<std::vector<app*>> mk_hterm_disequality_new(app* lhs, app* rhs); 
        app* mk_addr_in_hterm_new(app* hterm, app* addr); 
        app* mk_addr_notin_hterm_new(app *hterm, app* addr);
        app* mk_read_formula_new(app* from_hvar, app* read_addr, int read_field, app* read_item); 
        app* mk_write_formula_new(app* orig_hvar, app* writed_hvar, app* write_addr, int write_field, app* write_item); 

        // logic with multi-records:
        app* mk_points_to_multi(app* addr_loc, app* record_term);// DONE
        // TODOs:
        app* mk_record(pt_record* r, std::vector<app*> locvars, std::vector<app*> datavars);// DONE

        std::vector<std::vector<app*>> mk_hterm_disequality_multi(app* lhs, app* rhs); // DONE

        std::vector<app*> mk_addr_in_hterm_multi(app* hterm, app* addr); // DONE
        app* mk_addr_notin_hterm_multi(app* hterm, app* addr); // DONE

        // TODO: these two can be postponed
        app* mk_read_formula_multi(app* from_hvar, app* read_addr, pt_record* record_type, int read_field, app* read_item);
        app* mk_write_formula_multi(app* orig_hvar, app* writed_hvar, app* write_addr, pt_record* record_type, int write_field, app* write_item);

        

         
    };

 
    class heap_value_proc : public model_value_proc {
        family_id m_fid;
        sort*     m_sort;
        unsigned m_num_entries;
        svector<model_value_dependency> m_dependencies;

        public:
        heap_value_proc(family_id id, sort* s) {
            this->m_fid = id;
            this->m_sort = s;
            this->m_num_entries = 0;
        }

        void add_dependency(model_value_dependency d) {
            this->m_num_entries ++;
            this->m_dependencies.push_back(d);
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            result.append(this->m_dependencies.size(), m_dependencies.data());
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values)  {
            ast_manager& m = mg.get_manager();
            slhv_decl_plugin* plug = (slhv_decl_plugin*) m.get_plugin(m.mk_family_id("slhv"));
            if(this->m_sort->get_name() == INTHEAP_SORT_STR) {
                if(values.size() > 1) {
                    if(values.get(0)->get_sort()->get_name() == INTHEAP_SORT_STR) {
                        // the value is a uplus term
                        return plug->mk_uplus_value(values.size(), values);
                    } else {
                        SASSERT(values.size() == 2 && values.get(0)->get_sort()->get_name() == INTLOC_SORT_STR);
                        // must be a points to
                        return plug->mk_points_to_value(2, values);
                    }
                } else if(values.size() == 1){
                    return to_app(values.get(0));
                } else {
                    return plug->mk_emp_value();
                }
            } else if(this->m_sort->get_name() == INTLOC_SORT_STR) {
                ast_manager& m = mg.get_manager();
                SASSERT(values.size() == 2);
                return plug->mk_locadd_value(2, values);
            } else {
                return nullptr;
            }
        }

        bool is_fresh() const override {
            return false;
        }

    };

    class mem_management {
        public:
        theory_slhv* th;
        std::set<heap_term*> ht_ptrs;
        std::set<atoms_subsumption*> at_ptrs;
        std::set<formula_encoder*> fec_ptrs;
        std::set<slhv_syntax_maker*> syntax_makers;
        std::set<ld_recov_node*> ld_recov_nodes;
        inference_graph* inf_graph;
        

        mem_management(theory_slhv* t) {
            this->th = t;
        }

        void push_ht_ptr(heap_term* ht) {
            ht_ptrs.insert(ht);
        }
        
        void push_at_ptr(atoms_subsumption* at) {
            at_ptrs.insert(at);
        }

        void push_fec_ptr(formula_encoder* fec) {
            fec_ptrs.insert(fec);
        }

        void push_syntax_mker(slhv_syntax_maker* syn_mker) {
            this->syntax_makers.insert(syn_mker);
        }

        void push_recov_node_ptr(ld_recov_node* recov_node) {
            this->ld_recov_nodes.insert(recov_node);
        }


        void set_inf_graph(inference_graph* inf_g) {
            this->inf_graph = inf_g;
        }

        void dealloc_all() {
            for(auto i : ht_ptrs) {
                dealloc(i);
            }
            for(auto i : at_ptrs) {
                dealloc(i);
            }
            for(auto i : fec_ptrs) {
                dealloc(i);
            }
            for(auto i : syntax_makers) {
                dealloc(i);
            }
            for(auto i : ld_recov_nodes) {
                dealloc(i);
            }
            this->ht_ptrs.clear();
            this->at_ptrs.clear();
            this->fec_ptrs.clear();
            this->syntax_makers.clear();
            this->ld_recov_nodes.clear();
            for(inf_node* n : this->inf_graph->nodes) {
                dealloc(n);
            }
            dealloc(this->inf_graph);
        }
        
    };

    class memsafe_wrapper {
        private:
        theory_slhv* th;

        std::set<expr*> dangling_nodes;

        public:
        memsafe_wrapper(theory_slhv* t) : th(t) {}

        app* use_mk_and(expr* lhs, expr* rhs);
        app* use_mk_and(expr* arg1, expr* arg2, expr* arg3);
        app* use_mk_and(unsigned num_args, expr * const * args);

        app* use_mk_or(expr* lhs, expr* rhs);
        app* use_mk_or(expr* arg1, expr* arg2, expr* arg3);
        app* use_mk_or(unsigned num_args, expr * const * args);

        app* use_mk_implies(expr* premise, expr* conclusion);
        app* use_mk_not(expr* inner);
        app* use_mk_eq(expr* lhs, expr* rhs);
        app* use_mk_distinct(expr* lhs, expr* rhs);

        
        void add_dangling(expr* node) {
            this->dangling_nodes.insert(node);
        }
    };

} // namespace smt
