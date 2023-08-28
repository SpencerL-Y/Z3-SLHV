#pragma once

#include "smt/smt_theory.h"
#include "ast/slhv_decl_plugin.h"
#include "model/value_factory.h"
#include <set>
#include <stack>
#include <vector>
#include <map>
#include <iostream>
#include <bitset>
namespace smt
{
    class slhv_fresh_var_maker;
    class slhv_syntax_maker;
    class dgraph_node;
    class hvar_dgraph_node;
    class pt_dgraph_node;
    class dgraph_edge;
    class hterm;
    class edge_labelled_dgraph;
    class edge_labelled_subgraph;
    class subheap_relation;
    class locvar_eq;
    class coarse_hvar_eq;
    class theory_slhv : public theory {

        public:
        enum slhv_check_status {
            slhv_unsat,
            slhv_sat,
            slhv_unknown
        };

        
        // configurations for a call of final_check
        slhv_check_status check_status;

        std::set<app *> curr_locvars;
        std::set<app *> curr_hvars;
        std::set<app *> curr_disj_unions;
        std::set<app *> curr_pts;

        std::set<app *> curr_loc_cnstr;
        std::set<app *> curr_heap_cnstr;

        std::set<enode_pair> curr_distinct_locterm_pairs;
        std::set<enode*> curr_emp_hterm_enodes;
        std::set<enode*> curr_notnil_locterms_enodes;
        std::set<enode_pair> curr_distinct_hterm_pairs;

        slhv_syntax_maker* syntax_maker;

        std::vector<expr*> curr_outside_assignments;
        std::vector<expr*> curr_inside_assignments;

        std::vector<bool> temp_loceq_bits;
        bool temp_zero_enumerated;
        std::map<int, enode_pair> indexed_assignable_pairs;

        app* global_emp;
        app* global_nil;

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
        void collect_loc_and_heap_cnstr_in_assignments(expr_ref_vector assigned_literals);

        

        std::pair<std::set<app* >, std::set<app *>> 
        collect_vars(app* expression);

        std::set<app*> collect_disj_unions(app* expression);

        std::set<app*> collect_points_tos(app* expression);
        

        void record_distinct_locterms_in_assignments(expr_ref_vector assigned_literals);
        
        void record_distinct_locterms(app* atom);

        void reset_configs();
        // checking logic

        std::map<enode*, std::set<app*>> get_coarse_locvar_eq();

        std::vector<enode_pair> get_unassigned_locvar_pairs();

        std::map<enode*, std::set<app*>> get_fine_locvar_eq(std::set<enode_pair>& assigned_pairs, std::map<enode*, std::set<app*>>& existing_data);

        std::vector<std::map<enode*, std::set<app*>>>  get_feasible_locvars_eq(); 

        void init_locvars_eq_boolvec();

        std::pair<bool, std::map<enode*, std::set<app*>>> get_locvars_eq_next();



        bool check_hterm_distinct_hvar_eq_consistency(coarse_hvar_eq* hvar_eq);

        void infer_emp_hterms();

        void infer_distinct_locterms_in_assignments(expr_ref_vector assigned_literals);

        void infer_distinct_locterms(app* expr);

        void infer_notnil_locterms_in_assignments(expr_ref_vector assigned_literals);

        void infer_notnil_locterms(app* expr);


        void infer_distinct_heapterms_in_assignments(expr_ref_vector assigned_hcnstrs);

        void infer_distinct_heapterms(app* atom);

        bool check_locvar_eq_feasibility_in_assignments(locvar_eq* loc_eq);

        std::set<hterm*> construct_hterms_subgraphs(std::vector<edge_labelled_subgraph*> all_subgraphs);

        std::pair<std::map<dgraph_node*, subheap_relation*>, bool> check_and_deduce_subheap_relation(edge_labelled_dgraph* orig_graph, std::map<dgraph_node*, std::vector<edge_labelled_subgraph*>>& all_subgraphs);

        std::pair<subheap_relation*, bool> check_and_deduce_subheap_relation_for_node(dgraph_node* node, std::map<dgraph_node*, subheap_relation*>& root2relation, std::set<edge_labelled_subgraph*> rooted_node_subgraphs);

        // RULE3 RULE4
        std::set<std::pair<hterm*, hterm*>> deduce_replaced_equivalent_pairs(std::set<hterm*>& existing_hterms, std::set<std::pair<hterm*, hterm*>> curr_eqs, std::set<std::pair<hterm*, hterm*>> child_eqs);

        std::pair<hterm*, hterm*> replace_and_find(std::set<hterm*>& existing_hterms, hterm* unchanged_orig, hterm* changed_orig, hterm* changed_frag, hterm* replacer);

        std::pair<hterm*, hterm*> substract_and_find(std::set<hterm*>& existing_hterms, hterm* large1, hterm* large2, hterm* small1, hterm* small2);

        bool check_new_subheap_pair(hterm* smaller, hterm* larger);

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

        void init_model(model_generator & mg) override;
        /**
           \brief Return true if the theory has something to propagate
        */

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

        // set UNSAT core for outside CDCL framework
        void set_conflict_outside();

        // set UNSAT core and equivalence realtion for inner branch cutting
        void set_conflict_inside();
        

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
        // virtual bool build_models() const { 
        //     return true;
        // }

        // virtual void init_model(model_generator & m) {
        // }

        // virtual void finalize_model(model_generator & m) {
        // }
        
        // /**
        //    \brief Return a functor that can build the value (interpretation) for n.
        // */
        // virtual model_value_proc * mk_value(enode * n, model_generator & mg) {
        //     return nullptr;
        // }

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


// variable equivalence class
    class locvar_eq {
        private:
            theory_slhv* th;
            std::map<enode*, std::vector<app*>> fine_data;
        public: 
            locvar_eq(theory_slhv* t, std::map<enode*, std::set<app*>>& fine_data);
            bool is_in_same_class(app* loc1, app* loc2);
            app* get_leader_locvar(app* loc);
            bool is_nil(app* loc);

            std::vector<app*> get_leader_locvars();
            theory_slhv* get_th() {
                return this->th;
            }

    };

    class coarse_hvar_eq {
        private:
            theory_slhv* th;
            std::map<enode*, std::vector<app*>> coarse_data;
            void merge_enodes(std::set<enode*> nodes);
        public:
        // construct coarse hvar eq from th curr_hvars
        coarse_hvar_eq(theory_slhv* th);
        coarse_hvar_eq* merge_hvar_nodes(std::vector<std::set<enode*>> enode_sets);
        // return 1 for yes, 0 for no and -1 for not sure
        int is_in_same_class(app* hvar1, app* hvar2);
        app* get_leader_hvar(app* hvar);
        // return 1 for yes, 0 for no and -1 for unknown
        int is_emp_hvar(app* hvar);
        app* get_emp() {
            return this->th->global_emp;
        }

        std::vector<app*> get_leader_hvars();
        std::map<enode*, std::vector<app*>> get_coarse_data() {
            return this->coarse_data;
        }
        theory_slhv* get_th() {
            return this->th;
        }
    };

// edge-labelled directed graph
    class edge_labelled_dgraph {
        //TODO: add labeling function for list segment later
        private:
            theory_slhv* th;
            locvar_eq* loc_eq;
            coarse_hvar_eq* hvar_eq;
            std::vector<dgraph_node*>  nodes;
            std::vector<dgraph_edge*>  edges;
            bool simplified;
            void construct_graph_from_theory();
            void tarjanSCC(std::set<dgraph_node*> sources);
            dgraph_node* get_unvisited();
            bool check_established_reachable(std::set<int> nontrivial_ids);
            coarse_hvar_eq* check_and_merge_scc_hvars(std::set<int> nontrivial_ids);
            std::set<dgraph_node*> get_simplified_nodes(std::set<int> nontrivial_ids);
        public:
            edge_labelled_dgraph(theory_slhv* t, locvar_eq* l, coarse_hvar_eq* h);
            edge_labelled_dgraph(theory_slhv* t, locvar_eq* l, coarse_hvar_eq* h, std::vector<dgraph_node*> ns, std::vector<dgraph_edge*> es, bool simplified);

            hvar_dgraph_node* get_hvar_node(app* orig_hvar);
            pt_dgraph_node* get_pt_node(app* orig_pt);

            std::set<dgraph_node*> get_sources();
            bool has_edge(dgraph_edge* edge);
            bool has_edge_to(dgraph_node* node);
            bool has_edge_from(dgraph_node* node);
            std::vector<dgraph_edge*> get_edges_from_node(dgraph_node* n);
            bool is_scc_computed();
            virtual bool is_subgraph() {
                return false;
            }
            edge_labelled_dgraph* check_and_simplify();
            void set_simplified() {
                this->simplified = true;
            }
            void add_node(dgraph_node* n);
            void add_edge(dgraph_edge* e);
            dgraph_node* get_node_by_low(int low_idx);
            std::vector<edge_labelled_subgraph*> extract_all_rooted_disjoint_labelcomplete_subgraphs(dgraph_node* root, std::map<dgraph_node*, std::vector<edge_labelled_subgraph*>>& node2subgraph);
            std::vector<edge_labelled_subgraph*> subgraphs_union(std::vector<edge_labelled_subgraph*> graphs1, std::vector<edge_labelled_subgraph*> graphs2);
            
            bool is_rooted() {
                return this->get_sources().size() == 1;
            }
            dgraph_node* get_root_node();
            std::set<dgraph_node*> get_dest_nodes();

            locvar_eq* get_locvar_eq() {
                return this->loc_eq;
            }
            coarse_hvar_eq* get_hvar_eq() {
                return this->hvar_eq;
            }
            theory_slhv* get_th() {
                return this->th;
            }
            bool get_simplified() {
                return this->simplified;
            }
            std::vector<dgraph_node*> get_nodes() {
                return this->nodes;
            }
            std::vector<dgraph_edge*> get_edges() {
                return this->edges;
            }
            void print(std::ostream& out);
    };

    class edge_labelled_subgraph : public  edge_labelled_dgraph {
        private:
            edge_labelled_dgraph* parent;
        public:
        edge_labelled_subgraph(edge_labelled_dgraph* p, std::vector<dgraph_node*> ns, std::vector<dgraph_edge*> es);
        bool is_subgraph() override {
            return true;
        }
        edge_labelled_dgraph* get_parent() {
            return this->parent;
        }
        hterm* obtain_graph_hterm();
        bool is_rooted_disjoint_labelcomplete();
    };

    class dgraph_node {
        private:
            edge_labelled_dgraph* dgraph;
            // -1 for not visited
            // other means visited
            int dfs_index;
            int low_index;
        public: 
            dgraph_node(edge_labelled_dgraph* g);
            int tarjanSCC(int& dfs_num);
            bool is_tarjan_visited() {
                return !(dfs_index == -1);
            }
            int get_low_index() {
                return this->low_index;
            }
            int get_dfs_index() {
                return dfs_index;
            }
            edge_labelled_dgraph* get_dgraph() {
                return this->dgraph;
            }
            virtual bool is_hvar() {
                return false;
            }
            virtual bool is_points_to() {
                return false;
            }
            virtual bool is_established() {
                return false;
            }
            void set_graph(edge_labelled_dgraph* g) {
                this->dgraph = g;
            }
            void set_low_index(int idx) {
                this->low_index = idx;
            }
            void set_dfs_index(int idx) {
                this->dfs_index = idx;
            }
            virtual void print(std::ostream& out) {
                out << "node print node implemented" << std::endl;
            }
    };

    class hvar_dgraph_node : public dgraph_node {
        private: 
            app* leader_hvar;
        public:
            hvar_dgraph_node(edge_labelled_dgraph* g, app* hvar);
            app* get_hvar_label() {
                return this->leader_hvar;
            }
            bool is_hvar() override {
                return true;
            }
            bool is_points_to() override {
                return false;
            }
            bool is_established() override {
                return false;
            }
            void print(std::ostream& out) override;
    };

    class pt_dgraph_node : public dgraph_node {
        private:
            app* pt_addr_leader;
            app* pt_data_leader;
        public:
            pt_dgraph_node(edge_labelled_dgraph* g, app* pt_addr, app* pt_data);

            std::pair<app*, app*> get_pt_pair_label() {
                return {pt_addr_leader, pt_data_leader};
            }

            bool is_hvar() override {
                return false;
            }
            
            bool is_points_to() override {
                return true;
            }
            bool is_established() override {
                return true;
            }
            void print(std::ostream& out) override;
    };

    class dgraph_edge {
        private:
            edge_labelled_dgraph* dgraph;
            dgraph_node* from;
            dgraph_node* to;
            app* hterm_label;
        public:
            dgraph_edge(edge_labelled_dgraph* graph, dgraph_node* f, dgraph_node* t, app* hterm_label);
            dgraph_node* get_from() {
                return from;
            }
            dgraph_node* get_to() {
                return to;
            }
            app* get_label() {
                return hterm_label;
            }
            edge_labelled_dgraph* get_dgraph() {
                return dgraph;
            }
            void print(std::ostream& out);
    };
// hterm class
    class hterm {
        private:
            std::set<std::pair<app*,app*>> h_atoms;
            coarse_hvar_eq* h_eq;
            locvar_eq* loc_eq;

            std::set<hterm*> concat_subhterms(std::set<hterm*> hterm_set, std::pair<app*, app*> curr_atom);

            void print_app_pair(std::pair<app*, app*> p, std::ostream& os);
        public:
            hterm(std::set<std::pair<app*, app*>> hts, coarse_hvar_eq* hvar_eq, locvar_eq* loc_eq) : h_atoms(hts), h_eq(hvar_eq), loc_eq(loc_eq) {
                if(h_atoms.size() == 0) {
                    h_atoms.insert({this->h_eq->get_emp(), nullptr});
                }
            }
            bool is_sub_hterm_of(hterm* ht);
            bool is_super_hterm_of(hterm* ht);
            bool is_established();
            bool is_emp();
            std::set<std::pair<app*, app*>> get_h_atoms() {
                return h_atoms;
            }
            hterm* substract_hterm(hterm* substracted);
            coarse_hvar_eq* get_h_eq() {
                return this->h_eq;
            }
            locvar_eq* get_loc_eq() {
                return this->loc_eq;
            }
            std::set<hterm*> get_all_atom_hterms();
            std::set<hterm*> generate_all_subhterms();

            bool operator==(const hterm& other) {
                if(this->h_eq == other.h_eq &&
                   this->loc_eq == other.loc_eq &&
                   this->h_atoms == other.h_atoms) {
                    return true;
                   } else {
                    return false;
                   }
            }

            void print(std::ostream& os);

    };

// hterm inclusion relation
    class subheap_relation {
        private:
            std::set<hterm*> hterm_set;
            std::set<std::pair<hterm*, hterm*>> subheap_pairs;
            // first <= second
        public:
            subheap_relation(std::set<hterm*> hts, std::set<std::pair<hterm*, hterm*>> pairs) : hterm_set(hts), subheap_pairs(pairs) {}
            subheap_relation() {}
            void add_hterm(hterm* ht) {
                this->hterm_set.insert(ht);
            }
            void add_pair(hterm* ht_smaller, hterm* ht_larger);
            void add_equal(hterm* first, hterm* second);
            bool contain_hterm(hterm* ht);
            bool is_subheap(hterm* smaller, hterm* larger);
            bool is_equal_heap(hterm* first, hterm* second);
            std::set<hterm*> get_all_smaller_hterms(hterm* larger);
            std::set<hterm*> get_hterm_set() {
                return this->hterm_set;
            }
            std::set<std::pair<hterm*, hterm*>> get_subheap_pairs() {
                return this->subheap_pairs;
            }
            std::set<std::pair<hterm*, hterm*>> extract_equivalent_hterms();
            void print(std::ostream& os);
    };

    class eqheap_relation {
        private:
            std::set<hterm*> hterm_set;
            std::set<std::pair<hterm*, hterm*>> eqheap_pairs;
        public:
            eqheap_relation(std::set<hterm*> hts, std::set<std::pair<hterm*, hterm*>> pairs) : hterm_set(hts), eqheap_pairs(pairs) {
                for(hterm* h : hterm_set) {
                    eqheap_pairs.insert({h, h});
                }
            }

            bool is_equal_heap(hterm* first, hterm* second);
            std::set<std::pair<hterm*, hterm*>> get_eqheap_pairs();

            void print(std::ostream& os);
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
    };

// fresh_var_maker
    class slhv_fresh_var_maker {
    private:
        theory_slhv* th;
        int curr_locvar_id;
        int curr_hvar_id;
        std::map<int, app*> locvar_map;
        std::map<int, app*> hvar_map;
        slhv_decl_plugin* fe_plug;
    public:
        slhv_fresh_var_maker(theory_slhv* t);

        app* mk_fresh_locvar();
        app* mk_fresh_hvar();

        void reset();
    };
// syntax maker
    class slhv_syntax_maker {
        private:
        theory_slhv* th;
        slhv_decl_plugin* slhv_decl_plug;
        slhv_fresh_var_maker* fv_maker;

        public: 
        void reset_fv_maker();
        slhv_syntax_maker(theory_slhv* t);
        app* mk_fresh_locvar();
        app* mk_fresh_hvar();
        app* mk_read_formula(app* from_hvar, app* read_addr, app* read_data);
        app* mk_write_formula(app* orig_hvar, app* writed_hvar, app* write_addr, app* write_data);
        app* mk_addr_in_hterm(app* hterm, app* addr);
        app* mk_addr_notin_hterm(app* hterm, app* addr);
        std::vector<app*> mk_hterm_disequality(app* lhs, app* rhs);

        app* mk_uplus(int num_arg, std::vector<app*> hterm_args);
        app* mk_points_to(app* addr_loc, app* data_loc);
         
    };


    
} // namespace smt
