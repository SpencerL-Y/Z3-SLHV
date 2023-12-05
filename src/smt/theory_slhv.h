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
namespace smt
{
    class heap_term;
    class slhv_fresh_var_maker;
    class slhv_syntax_maker;
    class atoms_subsumption;
    class formula_encoder;
    class theory_slhv : public theory {

        public:
        enum slhv_check_status {
            slhv_unsat,
            slhv_sat,
            slhv_unknown
        };

        
        // configurations for a call of final_check
        slhv_check_status check_status;
        edge_labelled_dgraph* model_graph {nullptr};

        std::set<app *> curr_locvars;
        std::set<app *> curr_hvars;
        std::set<app *> curr_datavars;
        std::set<app *> curr_disj_unions;
        std::set<app *> curr_pts;
        std::vector<app*> curr_atomic_hterms;

        std::set<app *> curr_loc_cnstr;
        std::set<app *> curr_heap_cnstr;
        std::set<app* > curr_data_cnstr;

        std::set<enode*> curr_notnil_locterms_enodes;

        slhv_syntax_maker* syntax_maker;

        std::vector<expr*> curr_outside_assignments;
        std::vector<expr*> curr_inside_assignments;

        std::set<atoms_subsumption*> model_subsume_info;
        std::map<std::string, int> model_locvar_val_info;


        slhv_decl_plugin* slhv_plug;

        app* global_emp;
        app* global_nil;

        // model generation

        arith_factory* data_factory;
        locvar_factory* loc_factory;



        // check_context for a construction based on locvar_eq and negation choice

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
            return (is_points_to(n) || is_hvar(n));
        }
        bool is_locadd(app const* n) const {
            if(n->is_app_of(get_id(), OP_LOCADD)) {
                SASSERT(this->is_locvar(n) && this->is_dataterm(n));
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

        pt_record* analyze_pt_record_type(app* record_app);

        private:
        bool final_check();
        

        bool enode_contains_points_to(enode* node);

        bool curr_locvars_contain_nil();

        bool curr_hvars_contain_emp();

        bool internalize_term_core(app * term);


        // obtain assigned literals from smt_context and analyze 
        // ast to obtain all location variables, heap variables for later use
        // analyze all terms to do preprocessing later
        void preprocessing(expr_ref_vector assigned_literals);


        std::vector<expr_ref_vector> eliminate_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals);

        std::vector<std::vector<expr*>> eliminate_heap_equality_negation(std::vector<std::vector<expr*>> elimnated_neg_vec, expr* curr_neg_lit);  

        void collect_and_analyze_assignments(expr_ref_vector assigned_literals);
        void collect_loc_heap_and_data_cnstr_in_assignments(expr_ref_vector assigned_literals);

        

        std::tuple<std::set<app* >, std::set<app *>, std::set<app *>> 
        collect_vars(app* expression);

        std::set<app*> collect_disj_unions(app* expression);

        std::set<app*> collect_points_tos(app* expression);

        
        void reset_configs();
        // checking logic

        std::pair<std::set<std::pair<heap_term*, heap_term*>>, std::set<heap_term*>>  extract_all_hterms();

        void print_all_hterms(std::ostream& os);

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
            return final_check()? FC_DONE : FC_CONTINUE;
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

        bool can_propagate() override {
            return false;
        }        
        
        
        
        /**
           \brief This method is invoked to give a theory a chance to perform
           theory propagation.
        */
        void propagate() override;

        void set_conflict_or_lemma(literal_vector const& core, bool is_out_layer_conflict);

        void set_conflict_slhv(bool is_outside);
        void set_conflict_slhv(bool is_outside, std::vector<expr*> unsat_core);

        // set UNSAT core for outside CDCL framework
        void set_conflict_outside();
        void set_conflict_outside(std::vector<expr*> outside_unsat_core);

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

            void print_ht();
    };
// encoder from slhv to lia
    class formula_encoder {
        private:
        std::map<std::pair<int, int>, app*> djrel_var_map;
        std::map<std::pair<int, int>, app*> shrel_var_map;
        std::map<heap_term*, int> ht2index_map;
        std::vector<heap_term*> index2ht;

        std::map<app*, app*> locvar2intvar_map;

        std::set<heap_term*> hts;
        std::set<std::pair<heap_term*, heap_term*>> eq_ht_pairs;
        std::set<heap_term*> atom_hts;
        std::set<heap_term*> pt_hts;
        std::set<heap_term*> hvar_hts;
        heap_term* emp_ht;

        theory_slhv* th;
        slhv_syntax_maker* syntax_maker;
        
        std::set<heap_term*> get_sub_atom_hts(heap_term* orig_ht);

        expr* translate_locdata_formula(expr* formula);
        app* translate_locterm_to_liaterm(app* locterm);

        public:
        
        formula_encoder(theory_slhv* th, std::set<heap_term*> all_hterms, std::set<std::pair<heap_term*, heap_term*>> eq_hterm_pairs);
        
        app* get_shrel_boolvar(heap_term* subht, heap_term* supht);
        app* get_djrel_boolvar(heap_term* firstht, heap_term* secondht);
        heap_term* get_ht_by_id(int id) {
            return this->index2ht[id];
        }
        app* locvar2intvar(app* locvar);

        expr* generate_ld_formula();
        expr* generate_init_formula();
        expr* generate_pto_formula();
        expr* generate_iso_formula();
        expr* generate_idj_formula();
        expr* generate_final_formula();
        expr* generate_loc_var_constraints();

        expr* encode();


        std::pair<heap_term*, heap_term*> get_ht_pair_by_vec_pair(std::pair<std::vector<int>, std::vector<int>> vec_pair);

        std::set<std::pair<heap_term*, heap_term*>> parse_model_shrel(model_core& mdc);
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
        std::map<int, app*> locvar_map;
        std::map<int, app*> hvar_map;
        std::map<int, app*> datavar_map;
        slhv_decl_plugin* fe_plug;
    public:
        slhv_fresh_var_maker(theory_slhv* t);

        app* mk_fresh_locvar();
        app* mk_fresh_hvar();
        app* mk_fresh_datavar();

        void reset();
    };
// syntax maker
    class slhv_syntax_maker {
        private:
        theory_slhv* th;
        slhv_decl_plugin* slhv_decl_plug;
        slhv_fresh_var_maker* fv_maker;
        arith_util* a;

        public: 
        void reset_fv_maker();
        slhv_syntax_maker(theory_slhv* t);
        app* mk_fresh_locvar();
        app* mk_fresh_hvar();
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

        void get_dependencies(buffer<model_value_dependency>& result) override{
            result.append(this->m_dependencies.size(), m_dependencies.data());
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values)  {
            ast_manager& m = mg.get_manager();
            slhv_decl_plugin* plug = (slhv_decl_plugin*) m.get_plugin(m.mk_family_id("slhv"));
            if(values.size() > 1) {
                return plug->mk_uplus_value(values.size(), values);
            } else if(values.size() == 1){
                return to_app(values.get(0));
            } else {
                return nullptr;
            }
        }

        bool is_fresh() const override {
            return false;
        }


    };


    
} // namespace smt
