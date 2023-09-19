#include "ast/ast_ll_pp.h"
#include "ast/slhv_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "smt/smt_context.h"
#include "smt/theory_slhv.h"
#include "smt/smt_solver.h"
#include "util/params.h"
#include <bitset>
namespace smt {

    // theory-slhv --------------------------------
    theory_slhv::theory_slhv(context& ctx) : theory(ctx, ctx.get_manager().mk_family_id("slhv")) {
        #ifdef SLHV_DEBUG
        std::cout << "SLHV theory plugin created" << std::endl;
        #endif
        this->syntax_maker = new slhv_syntax_maker(this);
        this->global_emp = nullptr;
        this->global_nil = nullptr;
        this->reset_configs();
    }


    bool theory_slhv::enode_contains_points_to(enode* node) {
        enode* curr_node = node;
        app* node_app = curr_node->get_expr();
        if(is_points_to(node_app)) {
            return true;
        }
        curr_node = node->get_next();
        while(curr_node != node) {
            node_app = curr_node->get_expr();
            if(is_points_to(node_app)) {
                return true;
            }
        }
        return false;
    }


    bool theory_slhv::curr_locvars_contain_nil() {
        for(app* locvar : this->curr_locvars) {
            if(this->is_nil(locvar)) {
                return true;
            }
        }
        return false;
    }

    bool theory_slhv::curr_hvars_contain_emp() {
        for(app* hvar : this->curr_hvars) {
            if(this->is_emp(hvar)) {
                return true;
            }
        }
        return false;
    }

    
    theory *theory_slhv::mk_fresh(context * new_ctx)  {
        #ifdef SLHV_DEBUG
            std::cout << "slhv mk_fresh" << std::endl;
        #endif
        return alloc(theory_slhv, *new_ctx);
    }

    bool theory_slhv::internalize_atom(app * atom, bool gate_ctx)  {
        #ifdef SLHV_DEBUG
            std::cout << "slhv internalize atom" << std::endl;
        #endif
        return true;
    }

    bool theory_slhv::internalize_term(app * term)  {
        #ifdef SLHV_DEBUG
            std::cout << "slhv internalize term" << std::endl;
        #endif
        if(!is_uplus(term) && !is_points_to(term) && !is_locvar(term) && !is_hvar(term) && !is_nil(term) && !is_emp(term)) {
            std::cout << "unsupported term op: " << term->get_name() << std::endl;
            return false;
        }
        if(!internalize_term_core(term) ) {
            return true;
        }

        if(is_points_to(term)) {
            SASSERT(term->get_num_args() == 2);
            enode* arg0_node = ctx.get_enode(term->get_arg(0));
            enode* arg1_node = ctx.get_enode(term->get_arg(1));
            SASSERT(arg1_node != nullptr);

            theory_var arg0_var = arg0_node->get_th_var(get_id());
            SASSERT(arg0_var != -1 );
            SASSERT(get_th_var(term) != -1);
            #ifdef SLHV_DEBUG
            std::cout << "term name: " << term->get_name() << " is_points_to: " << is_points_to(term) << " num args: " << term->get_num_args() << std::endl;
            #endif
        } else if(is_uplus(term)) {
            SASSERT(term->get_num_args() >= 2);
            SASSERT(get_th_var(term) != -1);
            #ifdef SLHV_DEBUG
            std::cout << "term name: " << term->get_name() << " is_uplus: " << is_uplus(term) << " num args: " << term->get_num_args() << std::endl;
            #endif
        }
        else {
            SASSERT(term->get_num_args() == 0);
        }
        
        return true;
    }

    bool theory_slhv::internalize_term_core(app * term) {
        for(expr* arg : *term) {
            ctx.internalize(arg, false);
        }
        for (expr* arg : *term) {
            if(m.is_bool(arg)) {
                ctx.internalize(arg, false);
            }
        }
        if(ctx.e_internalized(term)) {
            return false;
        }
        enode* e = ctx.mk_enode(term, false, false, true);
        if(!is_attached_to_var(e)) {
            #ifdef SLHV_DEBUG
            std::cout << "mk_theory_var for " << mk_ismt2_pp(term, m) << std::endl;
            #endif
            mk_var(e);
            std::cout << "theory var made: " << get_th_var(e) << std::endl;
        }
        if(m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        return true;
    }

    void theory_slhv::new_eq_eh(theory_var v1, theory_var v2)  {
        #ifdef SLHV_DEBUG
            std::cout << "slhv new eq eh" << std::endl;
        #endif
    }

    void theory_slhv::new_diseq_eh(theory_var v1, theory_var v2)  {
        #ifdef SLHV_DEBUG
            std::cout << "slhv internalize term" << std::endl;
        #endif

    }

    void theory_slhv::display(std::ostream & out) const {

    }

    void theory_slhv::propagate() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv propagate" << std::endl;
        #endif
    }

    void theory_slhv::set_conflict_or_lemma(literal_vector const& core, bool is_outer_layer_conflict) {

    }

    void theory_slhv::set_conflict_outside() {
        literal_vector unsat_core;
        for(expr* e : this->curr_outside_assignments) {
            literal expr_lit = this->ctx.get_literal(e);
            unsat_core.push_back(expr_lit);
        }
        #ifdef SLHV_DEBUG
        std::cout << "conflict unsat core literals ====== " << std::endl;
        for(literal l : unsat_core) {
            std::cout  << l << std::endl;
        }
        std::cout << "conflict unsat core exprs ====== " << std::endl;
        for(expr* e : this->curr_outside_assignments) {
            std::cout << mk_pp(e, this->m) << std::endl;
        }
        #endif
        ctx.set_conflict(
            ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx, unsat_core.size(), unsat_core.data(), 0, nullptr, 0, nullptr
            ))
        );
    }


    void theory_slhv::set_conflict_outside(std::vector<expr*> outside_unsat_core) {
        literal_vector unsat_core;
        for(expr* e : outside_unsat_core) {
            literal expr_lit = this->ctx.get_literal(e);
            unsat_core.push_back(expr_lit);
        }
        #ifdef SLHV_DEBUG
        std::cout << "conflict unsat core literals ====== " << std::endl;
        for(literal l : unsat_core) {
            std::cout  << l << std::endl;
        }
        std::cout << "conflict unsat core exprs ====== " << std::endl;
        for(expr* e : this->curr_outside_assignments) {
            std::cout << mk_pp(e, this->m) << std::endl;
        }
        #endif
        ctx.set_conflict(
            ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx, unsat_core.size(), unsat_core.data(), 0, nullptr, 0, nullptr
            ))
        );
    }

    void theory_slhv::set_conflict_inside() {
        #ifdef SLHV_DEBUG
        std::cout << "TODOTODOTODOTODOTODOTODOTODO: set conflict inside" << std::endl;
        #endif
        // TODO use eliminated assignment to set conflict unsat core
    }

    void theory_slhv::set_conflict_inside(std::vector<expr*> inside_unsat_core) {
        
        #ifdef SLHV_DEBUG
        std::cout << "TODOTODOTODOTODOTODOTODOTODO: set conflict inside" << std::endl;
        #endif
    }


    void theory_slhv::set_conflict_slhv(bool is_outside) {
        if(is_outside) {
            this->set_conflict_outside();
        } else {
            this->set_conflict_inside();
        }
    }


    void theory_slhv::set_conflict_slhv(bool is_outside, std::vector<expr*> unsat_core) {

    }


    bool theory_slhv::is_arith_formula(app* l) {
        if(l->get_family_id() == arith_family_id) {
            return true;
        }
        if(l->get_num_args() > 0) {
            bool result = false;
            for(int i = 0; i < l->get_num_args(); i ++) {
                bool curr_result = this->is_arith_formula(to_app(l->get_arg(i)));
                result = result || curr_result;
                if(result) {
                    return true;
                }
            }
        }
        return false;
    }


    bool theory_slhv::final_check() {
        // reset all theory attribute for new final check
        #ifdef SLHV_DEBUG
        std::cout << "XXXXXXXXXXXXXXXXXXXX slhv final_check() XXXXXXXXXXXXXXXXXXXX" << std::endl;
        std::cout << "================= current assignment ==============" << std::endl;
        #endif
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        // reset collected hvars, locvars and 
        #ifdef SLHV_DEBUG
        for(expr* e : assignments) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
        }
        std::cout << "===================== current assignment end ==================" << std::endl;  
        #endif
        std::vector<expr*> heap_cnstr_core;
        for(expr* e : assignments) {
            if(!this->is_arith_formula(to_app(e))) {
                heap_cnstr_core.push_back(e);
            }
        }

        // use the datatype to initialize pt field info
        this->slhv_plug = (slhv_decl_plugin*) this->get_manager().get_plugin(this->get_id());
        SASSERT(this->slhv_plug->pt_record_initialized);
        this->pt_datafield_num = this->slhv_plug->pt_datanum;
        this->pt_locfield_num = this->slhv_plug->pt_locnum;
        #ifdef SLHV_DEBUG
        std::cout << "final check pt datafield num: " << this->pt_datafield_num << std::endl;
        std::cout << "final check pt locfield num: " << this->pt_locfield_num << std::endl;
        #endif
        
        // TODO: change all encoding based on pt record info 
        //  enumerate all possible situations for negation imposed on hterm equalities
        std::vector<expr_ref_vector> elim_enums = this->eliminate_heap_equality_negation_in_assignments(assignments);
        #ifdef SLHV_DEBUG
        std::cout << "number of assignments after negations elimination: " << elim_enums.size() << std::endl;
        #endif

        
        // TODO implement inner CDCL framework here
        for(expr_ref_vector curr_assignments : elim_enums) {
            expr_ref_vector heap_cnstr_assignments(m);
            expr_ref_vector numeral_cnstr_assignments(m);
            for(expr* e : curr_assignments) {
                if(this->is_arith_formula(to_app(e))) {
                    numeral_cnstr_assignments.push_back(e);
                } else {
                    heap_cnstr_assignments.push_back(e);
                }
            }
            #ifdef SLHV_DEBUG
            std::cout << "--------------------- CURR ELIM ASS -------------" << std::endl;
            std::cout << "heap constraints ========== " << std::endl;
            for(expr* e : heap_cnstr_assignments) {
                std::cout << mk_ismt2_pp(e, this->m) << std::endl;
            } 
            std::cout << "numeral constraints ========== " << std::endl;
            for(expr* e : numeral_cnstr_assignments) {
                std::cout << mk_ismt2_pp(e, this->m) << std::endl;
            } 
            std::cout << "--------------------- CURR ELIM ASS -------------" << std::endl;
            #endif
            // reset info from previous curr_assignments
            this->reset_configs();
            // record current outside assignments and inside assignments
            for(expr* e : assignments) {
                this->curr_outside_assignments.push_back(e);
            }
            for(expr* e : curr_assignments) {
                this->curr_inside_assignments.push_back(e);
            }
            // TODO elaborate the unsat core for CDCL outside
            // ---------------------------------- NUMERAL CONSTRAINT SOLVING ------------
            solver* numeral_solver = mk_smt_solver(this->m, params_ref(), symbol("QF_LIA"));
            for(expr* e: numeral_cnstr_assignments) {
                numeral_solver->assert_expr(e);
            }
            lbool result =  numeral_solver->check_sat();
            #ifdef SLHV_DEBUG
            std::cout << "XXXXXXXXXXXXXXXXX coarse numeral constraint result XXXXXXXXXXXXXXXXXXX " << std::endl;
            if(result == l_true) {
                std::cout << "SAT" << std::endl;
            } else if(result == l_false) {
                std::cout << "UNSAT" << std::endl;
            } else {
                std::cout << "UNDEF" << std::endl;
            }
            std::cout << "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" << std::endl;
            #endif
            std::vector<expr*> numeral_cnstr_core;
            for(expr* e : numeral_cnstr_assignments) {
                numeral_cnstr_core.push_back(e);
            }
            if(result == l_false) {
                // this->set_conflict_slhv(true, numeral_cnstr_core);
                this->check_status = slhv_unsat;
                this->set_conflict_slhv(true);
                return false;
            } else if(result == l_true){
                
            } else {
                #ifdef SLHV_DEBUG
                std::cout << "ERROR: this should not happen" << std::endl;
                #endif
                SASSERT(false);
            }

            // ---------------------------------- HEAP CONSTRAINT SOLVING ------------
            // preprocessing
            this->preprocessing(heap_cnstr_assignments);
            if(this->check_status == slhv_unsat) {
                this->check_status = slhv_unknown;
                continue;
            }
 
            // [[ OLD LOGIC ********************************* 
            // enumerate all possible loc eqs
            // std::vector<std::map<enode*, std::set<app*>>> loc_eqs_raw = this->get_feasible_locvars_eq();
            // #ifdef  SLHV_DEBUG
            // std::cout << "feasible locvars eq num: " << loc_eqs_raw.size() << std::endl;
            // #endif
            //   ********************************* OLD LOGIC ]]

            // establish coarse hvar eq 
            coarse_hvar_eq* curr_hvar_eq = alloc(coarse_hvar_eq, this);
            if(!this->check_hterm_distinct_hvar_eq_consistency(curr_hvar_eq)) {
                continue;
            }
            // initialize locvar eq searching
            this->init_locvars_eq_boolvec();
            
            bool still_has_eq = true;
            while(still_has_eq) {
                auto search_res = this->get_locvars_eq_next();
                still_has_eq = search_res.first;
                std::map<enode*, std::set<app*>> loc_eq_data = search_res.second;
                if(!still_has_eq) {
                    break;
                }

                locvar_eq* curr_loc_eq = alloc(locvar_eq, this, loc_eq_data);

                // TODO: add data constraint enumeration  here

                std::vector<app*> data_constraints =  extract_influential_data_constraints(curr_loc_eq loc_eq);
                // TODO: implement CDCL framework here
                if(!this->check_locvar_eq_feasibility_in_assignments(curr_loc_eq)) {
                    continue;
                }
                #ifdef SLHV_DEBUG
                std::cout << "---------------" << std::endl;
                std::cout << "current loc_eq_data: " << std::endl;
                int i = 0;
                for(auto p : loc_eq_data) {
                    std::cout << "loc partition " << i << ":" << std::endl;
                    for(app* e : p.second) {
                        std::cout << mk_ismt2_pp(e, this->m) << ", ";
                    }
                    std::cout << std::endl;
                    i += 1;
                }
                i = 0;
                std::cout << "---------------" << std::endl;
                auto coarse_hvar_eq_data = curr_hvar_eq->get_coarse_data();
                for(auto p : coarse_hvar_eq_data) {
                    std::cout << "hvar partition " << i << ":" << std::endl;
                    for(app* e : p.second) {
                        std::cout << mk_ismt2_pp(e, this->m) << ", ";
                    }
                    std::cout << std::endl;
                    i += 1;
                }
                std::cout << "---------------" << std::endl;
                #endif
                edge_labelled_dgraph* orig_graph = alloc(edge_labelled_dgraph, this, curr_loc_eq, curr_hvar_eq);

                #ifdef SLHV_DEBUG   
                    std::cout << "original graph: " << std::endl;
                    orig_graph->print(std::cout);
                #endif
                edge_labelled_dgraph* simplified_graph = orig_graph->check_and_simplify();
                #ifdef SLHV_DEBUG   
                    std::cout << "simplified graph: " << std::endl;
                    simplified_graph->print(std::cout);
                #endif
                // infer hterm inclusion
                // first compute the node2subgraphs mapping
                std::set<dgraph_node*> roots = simplified_graph->get_sources();
                std::map<dgraph_node*, std::vector<edge_labelled_subgraph*>> node2subgraphs;
                for(dgraph_node* n : roots) {
                    simplified_graph->extract_all_rooted_disjoint_labelcomplete_subgraphs(n, node2subgraphs);
                }
                #ifdef SLHV_DEBUG
                std::cout << "subgraphs extracted" << std::endl;
                #endif
                // deduce subheap relation for each node
                std::pair<std::map<dgraph_node*, subheap_relation*>, bool> curr_result = this->check_and_deduce_subheap_relation(simplified_graph, node2subgraphs);
                // the subheap deduction find a feasible subheap relation for satisfiability
                if(curr_result.second && this->check_status != slhv_unsat) {
                            #ifdef SLHV_DEBUG
                            std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET SAT XXXXXXXXXXXXXXXXXXXX" << std::endl;
                            #endif
                    this->check_status = slhv_sat;
                    return true;
                }
            }
        }

        #ifdef SLHV_DEBUG
        std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET UNSAT XXXXXXXXXXXXXXXXXXXX" << std::endl;
        #endif
        this->check_status = slhv_unsat;
        // this->set_conflict_slhv(true, heap_cnstr_core);
        this->set_conflict_slhv(true);
        return false;
    }

    void theory_slhv::preprocessing(expr_ref_vector assigned_literals) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv preprocessing" << std::endl;
        #endif
        this->collect_and_analyze_assignments(assigned_literals);
        this->record_distinct_locterms_in_assignments(assigned_literals);
        // collect heap constraints in the assigned literals
        expr_ref_vector heap_cnstr(m);
        for(expr* e : assigned_literals) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(to_app(e)->get_arg(0));
                if(this->is_heapterm(to_app(inner->get_arg(0)))) {
                    heap_cnstr.push_back(e);
                }
            } else {
                if(this->is_heapterm(to_app(to_app(e)->get_arg(0)))) {
                    heap_cnstr.push_back(e);
                }
            }
        }
        this->collect_loc_heap_and_data_cnstr_in_assignments(assigned_literals);
        this->infer_distinct_locterms_in_assignments(heap_cnstr);
        this->infer_distinct_heapterms_in_assignments(heap_cnstr);
        this->infer_emp_hterms();
        // TODO: add the equivalence checking of nil
        #ifdef SLHV_DEBUG
        std::cout << "slhv preprocessing end" << std::endl;
        #endif
    }

    std::vector<expr_ref_vector> theory_slhv::eliminate_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals) {
        std::vector<std::vector<expr*>> last_result;
        for(auto e : assigned_literals) {
            std::vector<std::vector<expr*>> temp_result;
            if(this->is_arith_formula(to_app(e))) {
                if(last_result.size() > 0) {
                    for(std::vector<expr*> r : last_result) {
                        std::vector<expr*> nr = r;
                        nr.push_back(e);
                        temp_result.push_back(nr);
                    }
                } else {
                    std::vector<expr*> nr;
                    nr.push_back(e);
                    temp_result.push_back(nr);
                }
                last_result = temp_result;
            } else {
                #ifdef SLHV_DEBUG
                std::cout << " eliminate heap negation for " << mk_ismt2_pp(e, this->get_manager()) << std::endl;
                #endif
                temp_result = this->eliminate_heap_equality_negation(last_result, e);
                last_result = temp_result;
                #ifdef SLHV_DEBUG
                std::cout << " eliminated " << mk_ismt2_pp(e, this->get_manager()) << std::endl;
                #endif
            }
        }
        std::vector<expr_ref_vector> final_result;
        for(std::vector<expr*> ev : last_result) {
            expr_ref_vector ref_v(m);
            for(auto e : ev) {
                ref_v.push_back(e);
            }
            final_result.push_back(ref_v);
        }
        return final_result;
    }

    std::vector<std::vector<expr*>> theory_slhv::eliminate_heap_equality_negation(std::vector<std::vector<expr*>> eliminated_neg_vec, expr* curr_neg_lit) {
        app* curr_lit = to_app(curr_neg_lit);
        std::vector<std::vector<expr*>> final_result;
        if(is_app_of(curr_lit, basic_family_id, OP_NOT) || is_app_of(curr_lit, basic_family_id, OP_DISTINCT)) {
            if(curr_lit->is_app_of(basic_family_id, OP_NOT)) {
                app* equality = to_app(curr_lit->get_arg(0));
                SASSERT(equality->is_app_of(basic_family_id, OP_EQ));
                app* left_expr = to_app(equality->get_arg(0));
                app* right_expr = to_app(equality->get_arg(1));
                if(this->is_heapterm(left_expr) && this->is_heapterm(right_expr)) {
                    SASSERT(this->is_hvar(left_expr));
                    // std::vector<std::vector<app*>> disjuncts_after_elim = this->syntax_maker->mk_hterm_disequality(left_expr, right_expr);
                    std::vector<std::vector<app*>> disjuncts_after_elim = this->syntax_maker->mk_hterm_disequality_new(left_expr, right_expr);
                    if(eliminated_neg_vec.size() != 0) {
                        for(std::vector<expr*> ev : eliminated_neg_vec) {
                            for(std::vector<app*> disj : disjuncts_after_elim) {
                                std::vector<expr*> result = ev;
                                for(app* l : disj) {
                                    result.push_back(to_expr(l));
                                }
                                final_result.push_back(result);
                            }
                        }
                    } else {
                        for(std::vector<app*> disj : disjuncts_after_elim) {
                            std::vector<expr*> result;
                            for(app* l : disj) {
                                result.push_back(to_expr(l));
                            }
                            final_result.push_back(result);
                        }
                    }
                    return final_result;
                } else {
                    if(eliminated_neg_vec.size() != 0) {
                        for(std::vector<expr*> v : eliminated_neg_vec) {
                            std::vector<expr*> result = v;
                            result.push_back(curr_neg_lit);
                            final_result.push_back(result);
                        }
                        return final_result;
                    } else {
                        std::vector<expr*> result;
                        result.push_back(curr_neg_lit);
                        final_result.push_back(result);
                        return final_result;
                    }
                }
            } else {
                std::cout << "eliminate heap equality negation: this should not happen" << std::endl;
                SASSERT(false);
                return final_result;
            }
        } else {
            if(eliminated_neg_vec.size() != 0) {
                for(std::vector<expr*> v : eliminated_neg_vec) {
                    std::vector<expr*> result = v;
                    result.push_back(curr_neg_lit);
                    final_result.push_back(result);
                }
            } else {
                std::vector<expr*> result;
                result.push_back(curr_neg_lit);
                final_result.push_back(result);
            }
            return final_result;
        }
    }

    void theory_slhv::collect_and_analyze_assignments(expr_ref_vector assigned_literals) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv collect and analyze assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            #ifdef SLHV_DEBUG
            std::cout << "collect expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            app* app_e = to_app(e);
            #ifdef SLHV_DEBUG
            std::cout << "collect vars in literal" << std::endl;
            #endif
            auto collected_vars = this->collect_vars(app_e);
            this->curr_locvars = slhv_util::setUnion(this->curr_locvars, std::get<0>(collected_vars));
            this->curr_hvars = slhv_util::setUnion(this->curr_hvars, std::get<1>(collected_vars));
            this->curr_datavars = slhv_util::setUnion(this->curr_datavars, std::get<2>(collected_vars));
            #ifdef SLHV_DEBUG
            std::cout << "collect disj unions in literal" << std::endl;
            #endif
            this->curr_disj_unions = slhv_util::setUnion(this->curr_disj_unions, this->collect_disj_unions(app_e));

            #ifdef SLHV_DEBUG
            std::cout << "collect pts in literal" << std::endl;
            #endif
            this->curr_pts = slhv_util::setUnion(this->curr_pts,  this->collect_points_tos(app_e));
        }
        // if "emp" or "nil" does not appear in the literals, add and internalize them manually:
        decl_plugin* plug = this->m.get_plugin(get_id());
        SASSERT(plug->get_family_id() == this->get_manager().mk_family_id("slhv"));
        SASSERT(plug != nullptr);
        slhv_decl_plugin* slhv_plugin = (slhv_decl_plugin*) plug;
        if(this->global_emp == nullptr) {
            #ifdef SLHV_DEBUG
            std::cout << "begin construct emp" << std::endl;
            #endif
            if(!this->curr_hvars_contain_emp()) {
                SASSERT(slhv_plugin->global_emp != nullptr);
                app* ge = slhv_plugin->global_emp;
                this->get_context().internalize(ge, false);
                std::cout << "internalize " << mk_pp(ge, this->m) << std::endl;
                this->curr_hvars.insert(ge);
                this->global_emp = ge;
            } else {
                SASSERT(this->global_emp == to_app(slhv_plugin->global_emp));
                this->get_context().internalize(to_app(slhv_plugin->global_emp), false);
            }
        } else {
            this->get_context().internalize(this->global_emp, false);
        }
        if(this->global_nil == nullptr) {
            #ifdef SLHV_DEBUG
            std::cout << "begin construct nil" << std::endl;
            #endif
            if(!this->curr_locvars_contain_nil()) {
                app* gn = slhv_plugin->global_nil;
                this->get_context().internalize(gn, false);
                std::cout << "internalize " << mk_pp(gn, this->m) << std::endl;
                this->curr_locvars.insert(gn);
                this->global_nil = slhv_plugin->global_nil;
            } else {
                SASSERT(this->global_nil == to_app(slhv_plugin->global_nil));
                this->get_context().internalize(to_app(slhv_plugin->global_nil), false);
            }
        } else {
            this->get_context().internalize(this->global_nil, false);
        }
        #ifdef SLHV_DEBUG
        std::cout << "collect and analyze assignments end" << std::endl;
        #endif
    }

    std::tuple<std::set<app* >, std::set<app *>, std::set<app *>>
    theory_slhv::collect_vars(app* expression) {
        // collect all locvars and hvars appeared recursively.
        std::set<app*> collected_locvars;
        std::set<app*> collected_hvars;
        std::set<app*> collected_datavars;
        
        if(is_hvar(expression) ) {
            collected_hvars.insert(expression);
            return make_tuple(collected_locvars, collected_hvars, collected_datavars);
        } else if (is_emp(expression)){
            collected_hvars.insert(expression);
            this->global_emp = expression;
            return make_tuple(collected_locvars, collected_hvars, collected_datavars);
        } else if(is_locvar(expression)) {
            collected_locvars.insert(expression);
            return make_tuple(collected_locvars, collected_hvars, collected_datavars);
        } else if(is_nil(expression)) {
            collected_locvars.insert(expression);
            this->global_nil = expression;
            return make_tuple(collected_locvars, collected_hvars, collected_datavars);
        } else if(is_datavar(expression)) {

            #ifdef SLHV_DEBUG
            std::cout << "collect data var: " << mk_ismt2_pp(expression, this->m) << std::endl;
            #endif
            collected_datavars.insert(expression);
            return make_tuple(collected_locvars, collected_hvars, collected_datavars);
        } 
        else {
            for(int i = 0; i < expression->get_num_args(); i ++) {
                auto temp_result_pair = this->collect_vars(to_app(expression->get_arg(i)));
                collected_locvars = slhv_util::setUnion(collected_locvars, std::get<0>(temp_result_pair));
                collected_hvars = slhv_util::setUnion(collected_hvars, std::get<1>(temp_result_pair));
                collected_datavars = slhv_util::setUnion(collected_datavars, std::get<2>(temp_result_pair));
            }
            return make_tuple(collected_locvars, collected_hvars, collected_datavars);
        }
    }

    
    std::set<app*> theory_slhv::collect_disj_unions(app* expression) {
        // collect all app that is disjoint union of heap terms recursively.
        std::set<app*> collected_disj_unions;
        if(is_uplus(expression)) {
            collected_disj_unions.insert(expression);
        } 
        for(int i = 0; i < expression->get_num_args(); i ++) {
            collected_disj_unions = slhv_util::setUnion(collected_disj_unions, this->collect_disj_unions(to_app(expression->get_arg(i))));
        }
        return collected_disj_unions;
    }

    std::set<app*> theory_slhv::collect_points_tos(app* expression) {
        std::set<app*> collected_points_tos;
        if(is_points_to(expression)) {
            collected_points_tos.insert(expression);
        }
        for(int i = 0; i < expression->get_num_args(); i ++) {
            collected_points_tos = slhv_util::setUnion(collected_points_tos, this->collect_points_tos(to_app(expression->get_arg(i))));
        }
        return collected_points_tos;
    }

    void theory_slhv::analyze_pt_record_field(app* pt) {
        SASSERT(this->is_points_to(pt));
        app* record = to_app(pt->get_arg(1));
        SASSERT(record->get_name() == "Pt_R");
        app* pt_r = to_app(record->get_arg(1));
        int field_num = pt_r->get_num_args();
        int loc_num = 0, data_num = 0;
        for(int i = 0; i < field_num; i ++) {
            app* curr_arg = to_app(pt_r->get_arg(i));
            if(this->is_locterm(curr_arg)) {
                loc_num += 1;
            } else if(this->is_dataterm(curr_arg)) {
                data_num += 1;
            } else {
                SASSERT(false);
            }
        }
        this->pt_locfield_num = loc_num;
        this->pt_datafield_num = data_num;
    }

    void theory_slhv::record_distinct_locterms_in_assignments(expr_ref_vector assigned_literals) {
        // refcord in literals all distinct locterms where constraints are explicitly given
        #ifdef SLHV_DEBUG
        std::cout << "record distinct locterms in assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            this->record_distinct_locterms(to_app(e));
        }
        #ifdef SLHV_DEBUG
        std::cout << "record distinc locterms in assignments end" << std::endl;
        #endif
    }

    void theory_slhv::record_distinct_locterms(app* atom) {
        // record all locterm enode that are explicitly distinct
        #ifdef SLHV_DEBUG
        std::cout << "record distinct locvars: "<< mk_ismt2_pp(atom, m) << std::endl; 
        #endif
        if(atom->is_app_of(basic_family_id, OP_DISTINCT)) {
            expr* lhs_expr = atom->get_arg(0);
            expr* rhs_expr = atom->get_arg(1);
            SASSERT(lhs_expr->get_sort()->get_name() == rhs_expr->get_sort()->get_name());
            if(this->is_locterm(to_app(lhs_expr))) {
                enode* lhs_node = this->ctx.get_enode(lhs_expr);
                enode* rhs_node = this->ctx.get_enode(rhs_expr);
                this->curr_distinct_locterm_pairs.insert({lhs_node->get_root(), rhs_node->get_root()});

                #ifdef SLHV_DEBUG
                std::cout << "record distinct locvars: " << mk_ismt2_pp(lhs_expr, m) << ", " <<  mk_ismt2_pp(rhs_expr, m)  << std::endl;
                #endif
            }
            
        } else if(atom->is_app_of(basic_family_id, OP_NOT)) {
            expr* negated = atom->get_arg(0);
            SASSERT(to_app(negated)->is_app_of(basic_family_id, OP_EQ));
            expr* lhs_expr = to_app(negated)->get_arg(0);
            expr* rhs_expr = to_app(negated)->get_arg(1);
            SASSERT(lhs_expr->get_sort()->get_name() == rhs_expr->get_sort()->get_name());
            if(this->is_locterm(to_app(lhs_expr))) {
                enode* lhs_node = this->ctx.get_enode(lhs_expr);
                enode* rhs_node = this->ctx.get_enode(rhs_expr);
                this->curr_distinct_locterm_pairs.insert({lhs_node->get_root(), rhs_node->get_root()});

                #ifdef SLHV_DEBUG
                std::cout << "record distinct locvars: " << mk_ismt2_pp(lhs_expr, m) << ", " <<  mk_ismt2_pp(rhs_expr, m)  << std::endl;
                #endif
            }
        } else {
            //PASS
        }
    }

    
    void theory_slhv::collect_loc_heap_and_data_cnstr_in_assignments(expr_ref_vector assigned_literals){
        // collect all constrainst imposed on heap and loc
        for(auto e : assigned_literals) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                expr* negated = to_app(e)->get_arg(0);
                expr* negated_arg0 = to_app(negated)->get_arg(0);
                if(is_heapterm(to_app(negated_arg0))) {
                    this->curr_heap_cnstr.insert(to_app(e));
                } else if(is_locterm(to_app(negated_arg0))) {
                    this->curr_loc_cnstr.insert(to_app(e));
                } else {
                    #ifdef SLHV_DEBUG
                    std::cout << "collect data cnstr: " << mk_ismt2_pp(e, this->m) << std::endl;
                    #endif
                    this->curr_data_cnstr.insert(to_app(e));
                    // this should not happen
                }
            } else {
                if(to_app(e)->is_app_of(basic_family_id, OP_DISTINCT) || 
                   to_app(e)->is_app_of(basic_family_id, OP_EQ) ){
                    expr* arg = to_app(e)->get_arg(0);
                    if(is_heapterm(to_app(arg))) {
                        this->curr_heap_cnstr.insert(to_app(e));
                    } else if(is_locterm(to_app(arg))) {
                        this->curr_loc_cnstr.insert(to_app(e));
                    } else {

                    #ifdef SLHV_DEBUG
                    std::cout << "collect data cnstr: " << mk_ismt2_pp(e, this->m) << std::endl;
                    #endif
                        this->curr_data_cnstr.insert(to_app(e));
                    }
                }
            }
        }
    }


    void theory_slhv::reset_configs() {
        std::cout << "reset configs for slhv theory" << std::endl;
        this->curr_pts.clear();
        this->curr_disj_unions.clear();
        this->curr_hvars.clear();
        this->curr_locvars.clear();

        this->curr_distinct_locterm_pairs.clear();
        this->curr_loc_cnstr.clear();
        this->curr_heap_cnstr.clear();
        this->curr_data_cnstr.clear();

        this->curr_distinct_locterm_pairs.clear();
        this->curr_emp_hterm_enodes.clear();
        this->curr_notnil_locterms_enodes.clear();
        this->check_status = slhv_unknown;
        
        this->curr_outside_assignments.clear();
        this->curr_inside_assignments.clear();
    }

    // check_logic

    std::map<enode*, std::set<app*>> theory_slhv::get_coarse_locvar_eq() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv get_coarse_locvar_eq" << std::endl;
        #endif
        std::map<enode*, std::set<app*>> unique_node_map;
        for(app* locvar : this->curr_locvars) {
            enode* lnode =  this->ctx.get_enode(locvar)->get_root();
            if(unique_node_map.find(lnode) != unique_node_map.end()) {
                unique_node_map[lnode].insert(locvar);
            } else {
                std::set<app*> newSet;
                newSet.insert(locvar);
                unique_node_map[lnode] = newSet;
            }
        }
        return unique_node_map;
    }

    std::vector<enode_pair> theory_slhv::get_unassigned_locvar_pairs(){
        #ifdef SLHV_DEBUG
        std::cout << "slhv get_unassigned_locvar_pairs" << std::endl;
        #endif
        std::map<enode*, std::set<app*>> unique_node_map = this->get_coarse_locvar_eq();
        std::vector<enode*> nodes;
        for(auto record : unique_node_map) {
            nodes.push_back(record.first);
        }

        std::vector<enode_pair> result;
        for(int i = 0; i < nodes.size(); i ++ ) {
            for(int j = i + 1; j < nodes.size(); j ++) {
                if(this->curr_distinct_locterm_pairs.find({nodes[i], nodes[j]}) == this->curr_distinct_locterm_pairs.end() && 
                   this->curr_distinct_locterm_pairs.find({nodes[j], nodes[i]}) == this->curr_distinct_locterm_pairs.end() ) {
                        result.push_back({nodes[i], nodes[j]});
                }
            }
        }
        return result;
    }


    std::map<enode*, std::set<app*>> theory_slhv::get_fine_locvar_eq(std::set<enode_pair> &assigned_pairs, std::map<enode*, std::set<app*>>& existing_data){
        auto unique_node_map = existing_data;
        std::map<enode*, std::set<app*>> result = unique_node_map;
        std::set<std::set<enode*>> enodes_partition;
        for(auto p : existing_data) {
            std::set<enode*> singleton;
            singleton.insert(p.first);
            enodes_partition.insert(singleton);
        }
        for(enode_pair p : assigned_pairs) {
            SASSERT(p.first != nullptr && p.second != nullptr);
            std::set<enode*> first_set, second_set;
            bool first_found = false, second_found = false;
            for(auto s : enodes_partition) {
                if(s.find(p.first) != s.end() && s.find(p.second) != s.end()) {
                    first_found = true; second_found = true;
                    first_set = s;
                    second_set = s;
                    break;
                }
                if(s.find(p.first) != s.end() && !first_found) {
                    first_found = true;
                    first_set = s;
                }
                if(s.find(p.second) != s.end() && !second_found) {
                    second_found = true;
                    second_set = s;
                }
                if(first_found && second_found) {
                    break;
                }
            }
            SASSERT(first_found && second_found);
            if(slhv_util::setEqual(first_set, second_set)) { 
                continue;
            } else {
                enodes_partition.erase(first_set);
                enodes_partition.erase(second_set);
                std::set<enode*> merged_set = slhv_util::setUnion(first_set, second_set);
                enodes_partition.insert(merged_set);
            }
        }

        #ifdef SLHV_DEBUG
        #endif
        for(std::set<enode*> s : enodes_partition) {
            std::set<app*> merged_app_set;
            for(enode* e : s) {
                merged_app_set = slhv_util::setUnion(merged_app_set, existing_data[e]);
            }
            for(enode* e : s) {
                result[e] = merged_app_set;
            }
        }
        return result;
    }

    std::vector<std::map<enode*, std::set<app*>>> theory_slhv::get_feasible_locvars_eq() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv get_feasible_locvars_eq" << std::endl;
        #endif
        // enumerate all feasible assignment to assignable locvar enode pairs
        // the result is a vector of map, where each map represents a way to do the partition of locvar eq
        std::vector<enode_pair> unassigned_pairs = this->get_unassigned_locvar_pairs();
        #ifdef SLHV_DEBUG
        std::cout << "unassigned pairs: " << std::endl;
        for(enode_pair p : unassigned_pairs) {
            std::cout << mk_ismt2_pp(p.first->get_expr(), this->m) << ", " << mk_ismt2_pp(p.second->get_expr(), this->m) << std::endl;
        }
        std::cout << "distinct pairs: " << std::endl;
        for(enode_pair p : this->curr_distinct_locterm_pairs) {
            std::cout << mk_ismt2_pp(p.first->get_expr(), this->m) << ", " << mk_ismt2_pp(p.second->get_expr(), this->m) << std::endl;
        }
        #endif
        std::vector<enode_pair> assignable_pairs;
        for(auto p : unassigned_pairs) {
            for(auto conflict : this->curr_distinct_locterm_pairs) {
                if(conflict.first == p.first && conflict.second == p.second ||
                   conflict.first == p.second && conflict.second == p.first) {
                    break;
                } 
            }
            assignable_pairs.push_back(p);
        }
        std::vector<std::set<enode_pair>> all_assigned_situations;
        std::vector<std::vector<bool>> assigned_bits_situations;
        for(int i = 0; i < assignable_pairs.size(); i ++) {
            if(i == 0) {
                std::vector<bool> firstAssigned; firstAssigned.push_back(true);
                std::vector<bool> firstNotAssigned; firstNotAssigned.push_back(false);
                assigned_bits_situations.push_back(firstAssigned);
                assigned_bits_situations.push_back(firstNotAssigned);
            } else {
                std::vector<std::vector<bool>> result;
                for(std::vector<bool> curr : assigned_bits_situations) {
                    std::vector<bool> currAssigned = curr;
                    std::vector<bool> currNotAssigned = curr;
                    currAssigned.push_back(true);
                    currNotAssigned.push_back(false);
                    result.push_back(currAssigned);
                    result.push_back(currNotAssigned);
                }
                assigned_bits_situations = std::move(result);
            }
        }
        for(std::vector<bool> & bits : assigned_bits_situations) {
            std::set<enode_pair> assigned_pairs;
            for(int i = 0; i < assignable_pairs.size(); i ++) {
                if(bits[i]) {
                    assigned_pairs.insert(assignable_pairs[i]);
                }
            }
            all_assigned_situations.push_back(assigned_pairs);
        }

        std::vector<std::map<enode*, std::set<app*>>> result_maps;
        std::map<enode*, std::set<app*>> existing_loc_eq_data = std::move(this->get_coarse_locvar_eq());
        #ifdef SLHV_DEBUG
        for(auto p : existing_loc_eq_data) {
            std::cout << "coarse partition x: " << std::endl;
            for(app* e : p.second) {
                std::cout << mk_ismt2_pp(e, this->get_manager()) << ", ";
            }
            std::cout << std::endl;
        }
        #endif
        for(auto e : all_assigned_situations) {
            result_maps.push_back(this->get_fine_locvar_eq(e, existing_loc_eq_data));
        }
        return result_maps;
    }


    void theory_slhv::init_locvars_eq_boolvec(){
        this->temp_zero_enumerated = false;
        this->temp_loceq_bits.clear();
        this->indexed_assignable_pairs.clear();
        #ifdef SLHV_DEBUG
        std::cout << "init locvars eq boolvec" << std::endl;
        #endif
        // enumerate all feasible assignment to assignable locvar enode pairs  
        // the result is a vector of map, where each map represents a way to do the partition of locvar eq
        std::vector<enode_pair> unassigned_pairs = this->get_unassigned_locvar_pairs();
        #ifdef SLHV_DEBUG
        std::cout << "unassigned pairs: " << std::endl;
        for(enode_pair p : unassigned_pairs) {
            std::cout << mk_ismt2_pp(p.first->get_expr(), this->m) << ", " << mk_ismt2_pp(p.second->get_expr(), this->m) << std::endl;
        }
        std::cout << "distinct pairs: " << std::endl;
        for(enode_pair p : this->curr_distinct_locterm_pairs) {
            std::cout << mk_ismt2_pp(p.first->get_expr(), this->m) << ", " << mk_ismt2_pp(p.second->get_expr(), this->m) << std::endl;
        }
        #endif
        std::vector<enode_pair> assignable_pairs;
        for(auto p : unassigned_pairs) {
            for(auto conflict : this->curr_distinct_locterm_pairs) {
                if(conflict.first == p.first && conflict.second == p.second ||
                   conflict.first == p.second && conflict.second == p.first) {
                    break;
                } 
            }
            assignable_pairs.push_back(p);
        }
        #ifdef SLHV_DEBUG
        std::cout << "assignable pairs: " << std::endl;
        for(enode_pair p : assignable_pairs) {
            std::cout << mk_ismt2_pp(p.first->get_expr(), this->m) << ", " << mk_ismt2_pp(p.second->get_expr(), this->m) << std::endl;
        }
        #endif
        for(int i = 0; i < assignable_pairs.size(); i ++) {
            this->temp_loceq_bits.push_back(false);
            this->indexed_assignable_pairs[i] = assignable_pairs[i];
        }
        #ifdef SLHV_DEBUG
        std::cout << "init locvars eq boolvec over" << std::endl;
        #endif
    }

    void simulation_add(std::vector<bool>& bits) {
        if(bits.size() == 0) {
            return;
        }
        bool adding_comsumed = false;
        int curr_idx = 0;
        while(!adding_comsumed) {
            if(bits[curr_idx]) {
                curr_idx ++;
                bits[curr_idx] = false;
            } else {
                adding_comsumed = true;
                bits[curr_idx] = true;
            }
        }
    }

    std::pair<bool, std::map<enode*, std::set<app*>>> theory_slhv::get_locvars_eq_next() {
        #ifdef SLHV_DEBUG
        std::cout << "get locvars eq next" << std::endl;
        std::cout << "current bits: ";
        for(int idx; idx < this->temp_loceq_bits.size(); idx ++) {
            std::cout << this->temp_loceq_bits[idx];
        }
        std::cout << std::endl;
        #endif
        std::set<enode_pair> assigned_pairs;
        if(this->temp_loceq_bits.size() > 0) {
            if(this->temp_zero_enumerated) {
                bool true_found = false;
                for(int idx = 0; idx < this->temp_loceq_bits.size(); idx ++) {
                    if(this->temp_loceq_bits[idx]) {
                        true_found = true;
                        break;
                    }
                }
                if(!true_found) {
                    std::map<enode*, std::set<app*>> empty_result;
                    return {false, empty_result};
                }
                for(int idx = 0; idx < this->temp_loceq_bits.size(); idx ++) {
                    if(this->temp_loceq_bits[idx]) {
                        assigned_pairs.insert(this->indexed_assignable_pairs[idx]);
                    }
                }
            } else {
                for(int idx = 0; idx < this->temp_loceq_bits.size(); idx ++) {
                    if(this->temp_loceq_bits[idx]) {
                        assigned_pairs.insert(this->indexed_assignable_pairs[idx]);
                    }
                }
                simulation_add(this->temp_loceq_bits);
                this->temp_zero_enumerated = true;
            } 
        }
        #ifdef SLHV_DEBUG
        std::cout << "current assigned pairs: " << std::endl;
        for(enode_pair p : assigned_pairs) {
            std::cout << mk_ismt2_pp(p.first->get_expr(), this->m) << ", " << mk_ismt2_pp(p.second->get_expr(), this->m) << std::endl;
        }
        #endif
        std::map<enode*, std::set<app*>> existing_loc_eq_data = std::move(this->get_coarse_locvar_eq());
        #ifdef SLHV_DEBUG
        for(auto p : existing_loc_eq_data) {
            std::cout << "coarse partition x: " << std::endl;
            for(app* e : p.second) {
                std::cout << mk_ismt2_pp(e, this->get_manager()) << ", ";
            }
            std::cout << std::endl;
        }
        #endif
        return {true, this->get_fine_locvar_eq(assigned_pairs, existing_loc_eq_data)};
    }


    std::vector<app*> theory_slhv::extract_influential_data_constraints(locvar_eq* loc_eq) {
        std::vector<app*> final_result;
        if(this->pt_datafield_num == 0) {
            // points-to does not contain any data field
            return final_result;
        }

        std::map<app*, std::vector<app*>> addr2pts;
        std::set<app*> addr_appeared;
        for(app* pt : this->curr_pts) {
            SASSERT(this->is_points_to(pt));
            app* addr = pt->get_arg(0);
            SASSERT(this->is_locvar(addr));
            app* addr_leader_var = loc_eq->get_leader_locvar(addr);
            addr_appeared.insert(addr_leader_var);
            if(addr2pts.find(addr_leader_var) != addr2pts.end()) {
                addr2pts[addr_leader_var].push_back(pt);
            } else {
                std::vector<app*> new_pt_vec;
                new_pt_vec.push_back(pt);
                addr2pts[addr_leader_var] = new_pt_vec;
            }
        }

        for(app* leader_var : addr_appeared) {
            std::vector<app*> addr_pts = addr2pts[leader_var];
        }
    }


    bool theory_slhv::is_points_to_loc_inequal(app* pt, locvar_eq* loc_eq) {

    }



    bool theory_slhv::check_hterm_distinct_hvar_eq_consistency(coarse_hvar_eq* hvar_eq) {
        for(auto p : this->curr_distinct_hterm_pairs) {
            if(p.first == p.second) {
                return false;
            }
        }
        return true;
    }


    void theory_slhv::infer_emp_hterms() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv inter emp hterms" << std::endl;
        #endif
        enode* emp_root = this->ctx.get_enode(this->global_emp);
        this->curr_emp_hterm_enodes.insert(emp_root);
        for(app* disju : this->curr_disj_unions) {
            SASSERT(this->is_uplus(disju));
            for(int i = 0; i < disju->get_num_args(); i ++) {
                for(int j = i + 1; j < disju->get_num_args(); j ++) {
                    enode* node_i = ctx.get_enode(disju->get_arg(i));
                    enode* node_j = ctx.get_enode(disju->get_arg(j));
                    if(node_i->get_root() == node_j->get_root()) {
                        this->curr_emp_hterm_enodes.insert(node_j->get_root());
                        if(this->enode_contains_points_to(node_j->get_root())){
                            // UNSAT
                            // reason: infered emp hterm is a points-to
                            this->check_status = slhv_unsat;
                            this->set_conflict_slhv(false);
                        }
                    }
                }
            }
        }
    }

    void theory_slhv::infer_distinct_locterms_in_assignments(expr_ref_vector assigned_literals) {

        #ifdef SLHV_DEBUG
        std::cout << "slhv infer distinct locterms in assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                // PASS because the heap term can be \bot
            } else {
                this->infer_distinct_locterms(to_app(e));
            }
        }
    }

    void theory_slhv::infer_distinct_locterms(app* e) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv infer_distinct_locterms: " << mk_ismt2_pp(e, m) << std::endl;
        #endif
        SASSERT(!e->is_app_of(basic_family_id, OP_NOT));
        if(is_uplus(e)) {
            std::vector<app*> disj_pts;
            for(int i = 0; i < e->get_num_args(); i ++) {
                if(is_points_to(to_app(e->get_arg(i)))) {
                    disj_pts.push_back(to_app(e->get_arg(i)));
                }
            }
            for(int i = 0; i < disj_pts.size(); i ++) {
                for(int j = i + 1; j < disj_pts.size(); j ++) {
                    #ifdef SLHV_DEBUG
                    std::cout << "pts: " << mk_pp(disj_pts[i], this->m) << " " << mk_pp(disj_pts[j], this->m) << std::endl;
                    #endif
                    expr* addr_i = disj_pts[i]->get_arg(0);
                    expr* addr_j = disj_pts[j]->get_arg(0);
                    enode* node_addr_i = ctx.get_enode(addr_i);
                    enode* node_addr_j = ctx.get_enode(addr_j);
                    enode* nil_root = this->ctx.get_enode(this->global_nil)->get_root();
                    #ifdef SLHV_DEBUG
                    std::cout << "get nil root node" << std::endl;
                    #endif
                    if(node_addr_i->get_root() == node_addr_j->get_root() ||
                       node_addr_i->get_root() == nil_root || 
                       node_addr_j->get_root() == nil_root) {
                        // UNSAT
                        // reason: two identical addr in one disj_union term
                        // or one of them is equal to nil
                        this->check_status = slhv_unsat;
                        this->set_conflict_slhv(false);
                    } else {
                        this->curr_distinct_locterm_pairs.insert({node_addr_i->get_root(), node_addr_j->get_root()});
                        this->curr_distinct_locterm_pairs.insert({node_addr_i->get_root(), nil_root});
                        this->curr_distinct_locterm_pairs.insert({node_addr_j->get_root(), nil_root});
                    }
                }
            }
        } else {
            for(int i = 0; i < e->get_num_args(); i ++ ) {
                this->infer_distinct_locterms(to_app(e->get_arg(i)));
            }
        }
    }

    void theory_slhv::infer_notnil_locterms_in_assignments(expr_ref_vector assigned_literals) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv infer notnil locterms in assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                // PASS because the heap term can be \bot
            } else {
                this->infer_notnil_locterms(to_app(e));
            }
        }
    }


    void theory_slhv::infer_notnil_locterms(app* expr) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv infer_notnil_locterms: " << mk_ismt2_pp(expr, m) << std::endl;
        #endif
        SASSERT(!expr->is_app_of(basic_family_id, OP_NOT));
        if(is_points_to(expr)) {
            this->curr_notnil_locterms_enodes.insert(ctx.get_enode(expr)->get_root());
        } else {
            for(int i = 0; i < expr->get_num_args(); i ++) {
                this->infer_notnil_locterms(to_app(expr->get_arg(i)));
            }
        }
    }

    void theory_slhv::infer_distinct_heapterms_in_assignments(expr_ref_vector assigned_hcnstrs) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv infer distinct heap terms in assignments" << std::endl;
        #endif
        for(expr * atom : assigned_hcnstrs) {
            app* possibly_neg = to_app(atom);
            if(!possibly_neg->is_app_of(basic_family_id, OP_NOT)) {
                #ifdef SLHV_DEBUG
                std::cout << "infer distinct heapterm of eq: " << mk_ismt2_pp(possibly_neg, this->m) << std::endl;
                #endif
                this->infer_distinct_heapterms(to_app(possibly_neg));
            }
        }
    };

    void theory_slhv::infer_distinct_heapterms(app* atom){

        #ifdef SLHV_DEBUG
        std::cout << "slhv infer distinct heap terms" << mk_ismt2_pp(atom, m) << std::endl;
        #endif
        SASSERT(atom->is_app_of(basic_family_id, OP_EQ));
        app* left_var = to_app(atom->get_arg(0));
        SASSERT(this->is_hvar(left_var) || this->is_emp(left_var));
        app* right_expr = to_app(atom->get_arg(1));
        if(this->is_uplus(right_expr)) {
            enode* emp_root = this->ctx.get_enode(this->global_emp)->get_root();
            enode* left_var_root_node = this->ctx.get_enode(left_var)->get_root();
            bool contain_points_to = false;
            for(int i = 0; i < right_expr->get_num_args(); i ++) {
                app* arg = to_app(right_expr->get_arg(i));
                if(this->is_points_to(arg)) {
                    contain_points_to = true;
                    break;
                }
            }
            if(contain_points_to) {
                this->curr_distinct_hterm_pairs.insert({emp_root, left_var_root_node});
                for(int i = 0; i < right_expr->get_num_args(); i ++) {
                    app* arg = to_app(right_expr->get_arg(i));
                    if(this->is_hvar(arg)) {
                        enode* rhs_var_root_node = this->ctx.get_enode(arg)->get_root();
                        this->curr_distinct_hterm_pairs.insert({left_var_root_node, rhs_var_root_node});
                    }
                }
            }
        } else if(this->is_points_to(right_expr)) {
            // left var is distinct with emp
            enode* emp_root = this->ctx.get_enode(this->global_emp)->get_root();
            enode* left_var_root = this->ctx.get_enode(left_var)->get_root();
            this->curr_distinct_hterm_pairs.insert({emp_root, left_var_root});
        } else if(this->is_emp(right_expr)) {
            // PASS
        } else if(this->is_hvar(right_expr)) {
            // PASS
        } else {
            SASSERT(false);
            // this should not happen
        }
    }

    bool theory_slhv::check_locvar_eq_feasibility_in_assignments(locvar_eq* loc_eq) {
        for(app* pt : this->curr_pts) {
            SASSERT(this->is_points_to(pt));
            app* addr = to_app(pt->get_arg(0));
            if(loc_eq->get_leader_locvar(addr) == this->global_nil) {
                return false;
            } 
        }
        return true;
    }

    std::set<hterm*> theory_slhv::construct_hterms_subgraphs(std::vector<edge_labelled_subgraph*> all_subgraphs) {
        // collect hterm from subgraphs:
        std::set<hterm*> result;
        coarse_hvar_eq* curr_eq = nullptr;
        for(edge_labelled_subgraph* sb : all_subgraphs) {
            if(curr_eq != nullptr) {
                if(curr_eq != sb->get_hvar_eq()) {
                    SASSERT(false);
                }
            } else {
                curr_eq = sb->get_hvar_eq();
            }
            result.insert(sb->obtain_graph_hterm());
        }
        return result;
    }


    std::pair<equiheap_relation*, bool> theory_slhv::check_and_deduce_equiheap_relation(edge_labelled_dgraph* orig_graph, std::map<dgraph_node*, std::vector<edge_labelled_subgraph*>>& all_subgraphs) {
        // RULE1: graph hterm self equal
        std::set<hterm*> all_hterms;
        std::set<hterm*> graph_hterms;
        std::set<std::pair<hterm*, hterm*>> hterm_pairs;
        for(std::pair<dgraph_node*, std::vector<edge_labelled_subgraph*>> ngs : all_subgraphs) {
            for(edge_labelled_subgraph* g : ngs.second) {
                hterm* ght = g->obtain_graph_hterm();
                graph_hterms.insert(ght);
                hterm_pairs.insert({ght, ght});
            }
        }
        // RULE2: equal hterms between graphs
        for(dgraph_node* n : orig_graph->get_nodes()) {
            std::vector<edge_labelled_subgraph*> node_subgraphs = all_subgraphs[n];
            edge_labelled_subgraph* first_subgraph = node_subgraphs[0];
            hterm* first_subgraph_hterm = first_subgraph->obtain_graph_hterm();
            for(int i = 1; i < node_subgraphs.size(); i ++) {
                hterm_pairs.insert({first_subgraph_hterm, node_subgraphs[i]->obtain_graph_hterm()});
            } 
        }

        equiheap_relation* rel = alloc(equiheap_relation, graph_hterms, hterm_pairs);
        if(!rel->get_is_feasible()) {
            return {rel, false};
        }

        // TODO: extend the pairs here
        std::set<std::pair<hterm*, hterm*>> all_pairs;
        std::set<std::set<hterm*>> distinct_equiv_set;
        for(auto record : rel->get_equiv_class()) {
            if(distinct_equiv_set.find(record.second) == distinct_equiv_set.end()) {
                distinct_equiv_set.insert(record.second);
            }
        }
        for(std::set<hterm*> s : distinct_equiv_set) {
            for(hterm* ht1 : s) {
                for(hterm* ht2 : s) {
                    all_pairs.insert({ht1, ht2});
                }
            }
        }
        all_hterms = graph_hterms;
        // RULE 3 and RULE 4
        std::set<std::pair<hterm*, hterm*>> new_deduced_hterm_pairs;
        do {    
            //RULE 3
            new_deduced_hterm_pairs.clear();
            std::set<std::pair<hterm*, hterm*>> temp_new_pairs;
            for(std::pair<hterm*, hterm*> p1 : all_pairs) {
                for(std::pair<hterm*, hterm*> p2 : all_pairs) {
                    if(p1 != p2) {
                        if(p2.first->is_sub_hterm_of(p1.second)) {
                            hterm* first = p1.first;
                            hterm* second = p1.second->replace_subhterm(p2.first, p2.second);
                            all_hterms.insert(second);
                            temp_new_pairs.insert({first, second});
                        } 
                        if(p2.second->is_sub_hterm_of(p1.second)) {
                            hterm* first = p1.first;
                            hterm* second = p1.second->replace_subhterm(p2.second, p2.first);
                            all_hterms.insert(second);
                            temp_new_pairs.insert({first, second});
                        }
                        if(p2.first->is_sub_hterm_of(p1.first)) {
                            hterm* first = p1.second;
                            hterm* second = p1.first->replace_subhterm(p2.first, p2.second);
                            all_hterms.insert(second);
                            temp_new_pairs.insert({first, second});
                        }
                        if(p2.second->is_sub_hterm_of(p1.first)) {
                            hterm* first = p1.second;
                            hterm* second = p1.first->replace_subhterm(p2.second, p2.first);
                            all_hterms.insert(second);
                            temp_new_pairs.insert({first, second});
                        }
                    }
                }
            }
            for(auto temp_p : temp_new_pairs) {
                bool found = false;
                for(auto ep : all_pairs) {
                    if(*temp_p.first == *ep.first && *temp_p.second == *ep.second) {
                        found = true;
                        break;
                    }
                }
                if(!found) {
                    new_deduced_hterm_pairs.insert(temp_p);
                }
            }
            temp_new_pairs.clear();

            // RULE4
            for(std::pair<hterm*, hterm*> p1 : all_pairs) {
                for(std::pair<hterm*, hterm*> p2 : all_pairs) {
                    if(p1 != p2) {
                        if(p2.first->is_sub_hterm_of(p1.first) && p2.second->is_sub_hterm_of(p1.second)) {
                            hterm* left = p1.first->substract_hterm(p2.first);
                            hterm* right = p1.second->substract_hterm(p2.second);
                            all_hterms.insert(left);
                            all_hterms.insert(right);
                            temp_new_pairs.insert({left, right});
                        }
                        if(p2.second->is_sub_hterm_of(p1.first) && p2.first->is_sub_hterm_of(p1.second)) {
                            hterm* left = p1.first->substract_hterm(p2.second);
                            hterm* right = p1.second->substract_hterm(p2.first);
                            all_hterms.insert(left);
                            all_hterms.insert(right);
                            temp_new_pairs.insert({left, right});
                        }
                    }
                }
            }

            
            for(auto temp_p : temp_new_pairs) {
                bool found = false;
                for(auto ep : all_pairs) {
                    if(*temp_p.first == *ep.first && *temp_p.second == *ep.second) {
                        found = true;
                        break;
                    }
                }
                for(auto ep : new_deduced_hterm_pairs) {
                    if(found) {
                        break;
                    }
                    if(*temp_p.first == *ep.first && *temp_p.second == *ep.second) {
                        found = true;
                        break;
                    }
                }
                if(!found) {
                    new_deduced_hterm_pairs.insert(temp_p);
                }
            }
            temp_new_pairs.clear();
            all_pairs = slhv_util::setUnion(all_pairs, new_deduced_hterm_pairs);
        } while(new_deduced_hterm_pairs.size() > 0);
        
        return {rel, rel->get_is_feasible()};
    }

    std::pair<std::map<dgraph_node*, subheap_relation*>, bool>  theory_slhv::check_and_deduce_subheap_relation(edge_labelled_dgraph* orig_graph, std::map<dgraph_node*, std::vector<edge_labelled_subgraph*>>& all_subgraphs){
        #ifdef SLHV_DEBUG
        std::cout << "check and deduce subheap relation" << std::endl;
        #endif
        std::map<dgraph_node*, subheap_relation*> root2relation;
        SASSERT(orig_graph->get_simplified());
        std::set<dgraph_node*> visited;
        // first construct subheap relation for leaf nodes
        for(dgraph_node* leaf : orig_graph->get_dest_nodes() ) {
            for(edge_labelled_subgraph* sb : all_subgraphs[leaf]) {
                SASSERT(sb->get_root_node() == leaf);
                hterm* leaf_term = sb->obtain_graph_hterm();
                subheap_relation* rel = alloc(subheap_relation);
                rel->add_hterm(leaf_term);
                rel->add_equal(leaf_term, leaf_term);
                root2relation[leaf] = rel;
                visited.insert(leaf);
                break;
            }
        }

        #ifdef SLHV_DEBUG
        std::cout << "relation for leaf node computed" << std::endl;
        #endif
        
        std::set<dgraph_node*> frontier_nodes;
        std::set<dgraph_node*> next_frontier_nodes;
        for(dgraph_node* n : orig_graph->get_nodes()) {
            bool abandoned = false;
            if(visited.find(n) != visited.end()) {
                abandoned = true;
            }
            for(dgraph_edge* e : orig_graph->get_edges()) {
                if(abandoned) break;
                if(e->get_from() == n && visited.find(e->get_to()) == visited.end()) {
                    abandoned = true;
                    break;
                }
            }
            if(!abandoned) {
                frontier_nodes.insert(n);
            }
        }
        while(frontier_nodes.size() > 0) {
            #ifdef SLHV_DEBUG
            std::cout << "curr visited: " << std::endl;
            for(dgraph_node* n : visited) {
                n->print(std::cout);
                std::cout << std::endl;
            }
            std::cout << "curr frontiers" << std::endl;
            for(dgraph_node* n : frontier_nodes) {
                n->print(std::cout);
                std::cout << std::endl;
            }
            #endif
            // check and deduce subheap relation for each frontier node
            for(dgraph_node* n : frontier_nodes) {
                std::set<edge_labelled_subgraph*> root_n_subgraphs;
                for(edge_labelled_subgraph* g : all_subgraphs[n]) {
                    root_n_subgraphs.insert(g);
                } 
                // check and deduce subheap relation for node
                std::pair<subheap_relation*, bool> n_relation = this->check_and_deduce_subheap_relation_for_node(n, root2relation, root_n_subgraphs);
                if(!n_relation.second) {
                    return {root2relation, false};
                }
                root2relation[n] = n_relation.first;
                visited.insert(n);
                // frontier_nodes.erase(n);
            }
            #ifdef SLHV_DEBUG
            std::cout << "compute new frontier nodes" << std::endl;
            #endif
            // compute new frontier nodes
            for(dgraph_node* n : orig_graph->get_nodes()) {
                bool abandoned = false;
                if(visited.find(n) != visited.end()) {
                    abandoned = true;
                }
                for(dgraph_edge* e : orig_graph->get_edges()) {
                    if(abandoned) break;
                    if(e->get_from() == n && visited.find(e->get_to()) == visited.end()) {
                        abandoned = true;
                        break;
                    }
                }
                if(!abandoned) {
                    next_frontier_nodes.insert(n);
                }
            }
            frontier_nodes = next_frontier_nodes;
        }
        #ifdef SLHV_DEBUG
        std::cout << "check and deduce subheap relation end" << std::endl;
        #endif
        return {root2relation, true};
    }


    std::pair<subheap_relation*, bool>  theory_slhv::check_and_deduce_subheap_relation_for_node(dgraph_node* node, std::map<dgraph_node*, subheap_relation*>& root2relation, std::set<edge_labelled_subgraph*> rooted_node_subgraphs) {
        //TODO: relation_hterm may repeat
        // merge all hterms rooted node
        #ifdef SLHV_DEBUG
        std::cout << "check and deduce subheap relation for node " ; 
        node->print(std::cout);
        std::cout << std::endl;
        std::cout << "rooted node subgraphs: " << std::endl;
        for(auto g : rooted_node_subgraphs) {
            g->print(std::cout);
            std::cout << std::endl;
            std::cout << "--------" << std::endl;
        }
        #endif
        std::set<hterm*> relation_hterms;
        std::set<std::pair<hterm*, hterm*>> new_subheap_pairs;
        std::set<std::pair<hterm*, hterm*>> equivalent_pairs;
        
        // gathering existing hterms
        for(edge_labelled_dgraph* sb : rooted_node_subgraphs) {
            for(dgraph_edge* e : sb->get_edges_from_node(node)) {
                subheap_relation* to_relation = root2relation[e->get_to()];
                for(hterm* ht : to_relation->get_hterm_set()) {
                    relation_hterms.insert(ht);
                }
            }
        }
        
        // generate remaining hterms
        for(edge_labelled_subgraph* sb : rooted_node_subgraphs) {
            hterm* total_hterm = sb->obtain_graph_hterm();
            std::set<hterm*> total_hterm_subterms = total_hterm->generate_all_subhterms();
            for(hterm* ht : total_hterm_subterms) {
                bool found = false;
                for(hterm* eht : relation_hterms) {
                    if(*ht == *eht) {
                        found = true;
                        break;
                    }
                }
                if(!found) {relation_hterms.insert(ht);};
            }
        }
        #ifdef SLHV_DEBUG
        std::cout << "gathering existing hterms and remaining hterms: " << std::endl;
        for(hterm* ht : relation_hterms) {
            ht->print(std::cout);
            std::cout << std::endl;
        }
        std::cout << "---- subheap pairs before rules: " << std::endl;
        for(auto p : new_subheap_pairs) {
            p.first->print(std::cout);
            std::cout << " <= " ;
            p.second->print(std::cout);
            std::cout << std::endl;
        }
        #endif
        // RULE1
        std::set<hterm*> graph_hterms;
        for(edge_labelled_subgraph* sb : rooted_node_subgraphs) {
            hterm* graph_hterm = sb->obtain_graph_hterm();
            bool found = false;
            for(hterm* ht : relation_hterms) {
                if(*graph_hterm == *ht) {
                    graph_hterm = ht;
                    found = true;
                    break;
                }
            }
            if(!found) {
                relation_hterms.insert(graph_hterm);
            }
            graph_hterms.insert(graph_hterm);
            new_subheap_pairs.insert({graph_hterm, graph_hterm});
            if(!this->check_new_subheap_pair(graph_hterm, graph_hterm)) {
                return {nullptr, false};
            }
            equivalent_pairs.insert({graph_hterm, graph_hterm});
        }

        #ifdef SLHV_DEBUG
        std::cout << "---- RULE 1 applied subheap pairs: " << std::endl;
        for(auto p : new_subheap_pairs) {
            p.first->print(std::cout);
            std::cout << " <= " ;
            p.second->print(std::cout);
            std::cout << std::endl;
        }
        #endif

        // RULE2
        for(edge_labelled_subgraph* sb1 : rooted_node_subgraphs) {
            for(edge_labelled_subgraph* sb2 : rooted_node_subgraphs) {
                if(sb1 != sb2) {
                    hterm* ht1 = sb1->obtain_graph_hterm();
                    hterm* ht2 = sb2->obtain_graph_hterm();
                    bool found1 = false, found2 = false;
                    for(hterm* ht : relation_hterms) {
                        if(found1 && found2) {
                            break;
                        }
                        if(*ht == *ht1 && !found1) {
                            ht1 = ht;
                            found1 = true;
                        }
                        if(*ht == *ht2 && !found2) {
                            ht2 = ht;
                            found2 = true;
                        }
                    }
                    if(!found1) {
                        relation_hterms.insert(ht1);
                    }
                    if(!found2) {
                        relation_hterms.insert(ht2);
                    }

                    new_subheap_pairs.insert({ht1, ht2});
                    new_subheap_pairs.insert({ht2, ht1});

                    if(!this->check_new_subheap_pair(ht1, ht2) || !this->check_new_subheap_pair(ht2, ht1)) {
                        return {nullptr, false};
                    }
                    equivalent_pairs.insert({ht1, ht2});
                }
            }
        }


        #ifdef SLHV_DEBUG
        std::cout << "---- RULE 2 applied subheap pairs: " << std::endl;
        for(auto p : new_subheap_pairs) {
            p.first->print(std::cout);
            std::cout << " <= " ;
            p.second->print(std::cout);
            std::cout << std::endl;
        }
        #endif

        for(edge_labelled_subgraph* sb : rooted_node_subgraphs) {
            for(dgraph_edge* e : sb->get_edges_from_node(sb->get_root_node())) {
                dgraph_node* child_node = e->get_to();
                subheap_relation* child_relation = root2relation[child_node];
                    // merge the hterms
                relation_hterms = slhv_util::setUnion(relation_hterms, child_relation->get_hterm_set());
                    // merge subheap pairs
                new_subheap_pairs = slhv_util::setUnion(new_subheap_pairs, child_relation->get_subheap_pairs());
            }
        }
        std::set<std::pair<hterm*, hterm*>> curr_iter_new_pairs;
        do {
            curr_iter_new_pairs.clear();
            // RULE 5: deduce ht1 < ht2 and ht2 < ht3 -> ht1 < ht3 and collect more equivalent pairs
            for(auto p1 : new_subheap_pairs) {
                for(auto p2 : new_subheap_pairs) {
                    if(p1 != p2 && p1.second == p2.first) {
                        std::pair<hterm*, hterm*> new_pair = {p1.first, p2.second};
                        if(!slhv_util::pairSetHasElement(new_subheap_pairs, new_pair)) {
                            curr_iter_new_pairs.insert(new_pair);
                        }
                    }
                }
            }
            new_subheap_pairs = slhv_util::setUnion(new_subheap_pairs, curr_iter_new_pairs);

            for(auto p1 : new_subheap_pairs) {
                for(auto p2 : new_subheap_pairs) {
                    if(p1.first == p2.second && p2.second == p1.first) {
                        std::pair<hterm*, hterm*> new_pair = {p1.first, p2.second};
                        bool equi_pair_found = false;
                        for(auto p : equivalent_pairs) {
                            if(p.first == new_pair.first && p.second == new_pair.second || 
                            p.first == new_pair.second && p.second == new_pair.first) {
                                equi_pair_found = true;
                                break;
                            }
                        }
                        if(!equi_pair_found) {
                            equivalent_pairs.insert(new_pair);
                        }
                    }
                }
            }

            // RULE 3&4 DO equivalence replacement when simply merging the existing subheap relation for child node
            for(edge_labelled_subgraph*  sb : rooted_node_subgraphs) {
                for(dgraph_edge* e : sb->get_edges_from_node(sb->get_root_node())) {
                    dgraph_node* child_node = e->get_to();
                    subheap_relation* child_relation = root2relation[child_node];

                    std::set<std::pair<hterm*, hterm*>> child_eq_pairs = child_relation->extract_equivalent_hterms();
                    if(equivalent_pairs.size() == 0) {
                        equivalent_pairs = child_eq_pairs;
                    } else {
                        std::set<std::pair<hterm*, hterm*>> new_eq_pairs = this->deduce_replaced_equivalent_pairs(relation_hterms, equivalent_pairs, child_eq_pairs);
                        for(std::pair<hterm*, hterm*> p : new_eq_pairs) {
                            if(!slhv_util::pairSetHasElement(new_subheap_pairs, p)) {
                                curr_iter_new_pairs.insert(p);
                            }
                            if(!slhv_util::pairSetHasElement(new_subheap_pairs, {p.second, p.first})) {
                                curr_iter_new_pairs.insert({p.second, p.first});
                            }
                            new_subheap_pairs.insert(p);
                            new_subheap_pairs.insert({p.second, p.first});
                            if(!this->check_new_subheap_pair(p.first, p.second) || !this->check_new_subheap_pair(p.second, p.first)) {
                                return {nullptr, false};
                            }
                        }
                        equivalent_pairs = slhv_util::setUnion(equivalent_pairs, new_eq_pairs);
                        equivalent_pairs = slhv_util::setUnion(equivalent_pairs, child_eq_pairs);
                    }
                }
            }
            new_subheap_pairs = slhv_util::setUnion(new_subheap_pairs, curr_iter_new_pairs);
            #ifdef SLHV_DEBUG
            std::cout << "curr iteration new pairs: " << std::endl;
            for(auto p : curr_iter_new_pairs) {
                std::cout << "(";
                p.first->print(std::cout);
                std::cout << ", ";
                p.second->print(std::cout);
                std::cout << ")";
            }
            #endif
        } while (curr_iter_new_pairs.size() > 0);
        #ifdef SLHV_DEBUG
        std::cout << "---- RULE 3&4&5 applied subheap pairs: " << std::endl;
        for(auto p : new_subheap_pairs) {
            p.first->print(std::cout);
            std::cout << " <= " ;
            p.second->print(std::cout);
            std::cout << std::endl;
        }
        #endif
        subheap_relation* result_relation = alloc(subheap_relation, relation_hterms, new_subheap_pairs);
        #ifdef SLHV_DEBUG
        std::cout << "----- result relation generated" << std::endl;
        result_relation->print(std::cout);
        #endif
        return {result_relation, true};
    }

    // RULE3 RULE4
    std::set<std::pair<hterm*, hterm*>> theory_slhv::deduce_replaced_equivalent_pairs(std::set<hterm*>& existing_hterms, std::set<std::pair<hterm*, hterm*>> curr_eqs, std::set<std::pair<hterm*, hterm*>> child_eqs) {
        std::set<std::pair<hterm*, hterm*>> result;
        std::set<std::pair<hterm*, hterm*>> curr_new;
        for(auto cp : child_eqs) {
            for(auto p : curr_eqs) {
                hterm* ht1 = cp.first; hterm* ht2 = cp.second;
                hterm* ht1_p = p.first; hterm* ht2_p = p.second;
                if(*ht1 == *ht1_p && *ht2 == *ht2_p) {
                    continue;
                }
                //RULE3
                if(ht2->is_super_hterm_of(ht1_p) && !ht1->is_super_hterm_of(ht1_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht1, ht2, ht1_p, ht2_p);
                    curr_new.insert(result_pair);
                } else if(ht1->is_super_hterm_of(ht1_p) && !ht2->is_super_hterm_of(ht1_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht2, ht1, ht1_p, ht2_p);
                    curr_new.insert(result_pair);
                } else if(ht1->is_sub_hterm_of(ht1_p) && !ht1->is_sub_hterm_of(ht2_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht2_p, ht1_p, ht1, ht2);
                    curr_new.insert(result_pair);
                } else if(ht1->is_sub_hterm_of(ht2_p) && !ht1->is_sub_hterm_of(ht1_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht1_p, ht2_p, ht1, ht2);
                    curr_new.insert(result_pair);
                } else if(ht2->is_super_hterm_of(ht2_p) && !ht1->is_super_hterm_of(ht2_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht1, ht2, ht2_p, ht1_p);
                    curr_new.insert(result_pair);
                } else if(ht1->is_super_hterm_of(ht2_p) && !ht2->is_super_hterm_of(ht2_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht2, ht1, ht2_p, ht1_p);
                    curr_new.insert(result_pair);
                } else if(ht2->is_sub_hterm_of(ht1_p) && !ht2->is_sub_hterm_of(ht2_p)) {    
                    auto result_pair = this->replace_and_find(existing_hterms, ht2_p, ht1_p, ht2, ht1);
                    curr_new.insert(result_pair);
                } else if(ht2->is_sub_hterm_of(ht2_p) && !ht2->is_sub_hterm_of(ht1_p)) {
                    auto result_pair = this->replace_and_find(existing_hterms, ht1_p, ht2_p, ht2, ht1);
                    curr_new.insert(result_pair);
                } else {
                    //RULE3 not applied
                }

                //RULE4
                if(ht1->is_super_hterm_of(ht1_p) && ht2->is_super_hterm_of(ht2_p)) {
                    auto result_pair = this->substract_and_find(existing_hterms, ht1, ht2, ht1_p, ht2_p);
                    curr_new.insert(result_pair);
                } else if(ht1->is_super_hterm_of(ht2_p) && ht2->is_super_hterm_of(ht1_p) ) {
                    auto result_pair = this->substract_and_find(existing_hterms, ht1, ht2, ht2_p, ht1_p);
                    curr_new.insert(result_pair);
                } else if(ht1->is_sub_hterm_of(ht1_p) && ht2->is_sub_hterm_of(ht2_p)) {
                    auto result_pair = this->substract_and_find(existing_hterms, ht1_p, ht2_p, ht1, ht2);
                    curr_new.insert(result_pair);
                } else if(ht1->is_sub_hterm_of(ht2_p) && ht2->is_sub_hterm_of(ht1_p)) {
                    auto result_pair = this->substract_and_find(existing_hterms, ht1_p, ht2_p, ht2, ht1);
                    curr_new.insert(result_pair);
                } else {
                    // RULE4 not applied
                }
            }
        }
        //TODO: recursion maybe needed
        return curr_new;
    }


    std::pair<hterm*, hterm*> theory_slhv::replace_and_find(std::set<hterm*>& existing_hterms, hterm* unchanged_orig, hterm* changed_orig, hterm* changed_frag, hterm* replacer) {
        std::set<std::pair<app*, app*>> changed_atoms = changed_orig->get_h_atoms();
        std::set<std::pair<app*, app*>> replaced_atoms = changed_frag->get_h_atoms();
        std::set<std::pair<app*, app*>> replacer_atoms = replacer->get_h_atoms();

        std::set<std::pair<app*, app*>> new_atoms = slhv_util::setUnion(
            slhv_util::setSubstract(changed_atoms, replaced_atoms),
            replacer_atoms
        );
        for(hterm* existing : existing_hterms) {
            if(existing->get_h_atoms() == new_atoms) {
                return {unchanged_orig, existing};
            }
        }
        hterm* new_hterm = alloc(hterm, new_atoms, unchanged_orig->get_h_eq(), unchanged_orig->get_loc_eq());
        return {unchanged_orig, new_hterm};
    }


    std::pair<hterm*, hterm*> theory_slhv::substract_and_find(std::set<hterm*>& existing_hterms, hterm* large1, hterm* large2, hterm* small1, hterm* small2) {
        // eq_pair1 is the larger pair
        std::set<std::pair<app*, app*>> large1_atoms = large1->get_h_atoms();
        std::set<std::pair<app*, app*>> large2_atoms = large2->get_h_atoms();
        std::set<std::pair<app*, app*>> small1_atoms = small1->get_h_atoms();
        std::set<std::pair<app*, app*>> small2_atoms = small2->get_h_atoms();
        std::set<std::pair<app*, app*>> substract1_atoms = slhv_util::setSubstract(large1_atoms, small1_atoms);
        std::set<std::pair<app*, app*>> substract2_atoms = slhv_util::setSubstract(large2_atoms, small2_atoms);
        hterm* result_first = nullptr;
        hterm* result_second = nullptr;
        bool result1_found = false, result2_found = false;
        for(hterm* existing : existing_hterms) {
            if(!result1_found && existing->get_h_atoms() == substract1_atoms) {
                result_first = existing;
                result1_found = true;
            }
            if(!result2_found && existing->get_h_atoms() == substract2_atoms) {
                result_second = existing;
                result2_found = true;
            }   
        }
        if(!result1_found) {
            result_first = alloc(hterm, substract1_atoms, large1->get_h_eq(), large1->get_loc_eq());
            existing_hterms.insert(result_first);
        }
        if(!result2_found) {
            result_second = alloc(hterm, substract2_atoms, large2->get_h_eq(), large2->get_loc_eq());
            existing_hterms.insert(result_first);
        }
        return {result_first, result_second};
    }

    bool theory_slhv::check_new_subheap_pair(hterm* smaller, hterm* larger) {
        std::set<std::pair<app*, app*>> smaller_atoms = smaller->get_h_atoms();
        std::set<std::pair<app*, app*>> larger_atoms = larger->get_h_atoms();
        // FIRST CHECK
        for(auto sp : smaller_atoms) {
            if(sp.second != nullptr) {
                for(auto lp : larger_atoms) {
                    if(lp.first == sp.first && lp.second != sp.second) {
                        return false;
                    } 
                }
            }
        }
        if(smaller->is_established() && larger->is_emp()) {
            return false;
        }
        return true;
    }

    void theory_slhv::init_model(model_generator & mg)  {
        #ifdef SLHV_DEBUG
        std::cout << "slhv init model" << std::endl;
        #endif
    }

    theory_var theory_slhv::mk_var(enode* n) {
        SASSERT(!is_attached_to_var(n));
        theory_var v = m_var2enode.size();
        m_var2enode.push_back(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;
    }

    locvar_eq::locvar_eq(theory_slhv* t, std::map<enode*, std::set<app*>>& fine_d) {
        this->th = t;
        for(auto pair : fine_d) {
            std::vector<app*> varsvec;
            for(app* v : pair.second) {
                varsvec.push_back(v);
            }
            this->fine_data[pair.first] = varsvec;
        }
    }

    bool locvar_eq::is_in_same_class(app* loc1, app* loc2) {
        if(this->fine_data[th->get_context().get_enode(loc1)->get_root()] == 
           this->fine_data[th->get_context().get_enode(loc2)->get_root()]) {
                return true;
           } else {
                return false;
           }
    }

    app* locvar_eq::get_leader_locvar(app* loc) {
        if(this->is_nil(loc)) {
            return this->th->global_nil;
        } else {
            return this->fine_data[th->get_context().get_enode(loc)->get_root()][0];
        }
    }

    bool locvar_eq::is_nil(app* loc) {
        enode* loc_root = this->th->get_context().get_enode(loc)->get_root();
        for(app* l : this->fine_data[loc_root]) {
            if(l == this->th->global_nil) {
                return true;
            }
        }
        return false;
    }


    std::vector<app*> locvar_eq::get_leader_locvars() {
        std::vector<app*> result;
        result.push_back(this->th->global_nil);
        for(auto pair : fine_data) {
            if(this->is_nil(pair.second[0])) {
                
            } else {
                result.push_back(pair.second[0]);
            }
        }
        return result;
    }

    coarse_hvar_eq::coarse_hvar_eq(theory_slhv* t) {
        this->th = t;
        for(app* hvar : this->th->curr_hvars) {
            enode* hvar_enode_root = this->th->get_context().get_enode(hvar)->get_root();
            if(coarse_data.find(hvar_enode_root) != coarse_data.end()) {
                coarse_data[hvar_enode_root].push_back(hvar);
            } else {
                std::vector<app*> varsvec;
                varsvec.push_back(hvar);
                coarse_data[hvar_enode_root] = varsvec;
            }
        }
        for(auto pair : this->coarse_data) {
            enode* rt_node = pair.first;
            if(this->th->curr_emp_hterm_enodes.find(rt_node) != this->th->curr_emp_hterm_enodes.end()) {
                bool has_emp = false;
                for(app* e : this->coarse_data[rt_node]) {
                    if(e == this->th->global_emp) {
                        has_emp = true;
                        break;
                    }
                }
                if(!has_emp) {
                    this->coarse_data[rt_node].insert(this->coarse_data[rt_node].begin(), this->th->global_emp);
                }
            }
        }
    }

    coarse_hvar_eq* coarse_hvar_eq::merge_hvar_nodes(std::vector<std::set<enode*>> nodes_sets) {
        coarse_hvar_eq* new_eq = alloc(coarse_hvar_eq, this->th);
        for(std::set<enode*> nodes : nodes_sets) {
            new_eq->merge_enodes(nodes);
        }
        return new_eq;
    }

    void coarse_hvar_eq::merge_enodes(std::set<enode*> nodes) {
        std::set<app*> merged_hvars;
        bool is_emp = false;
        for(enode* rt_node : nodes) {
            SASSERT(coarse_data.find(rt_node) != coarse_data.end());
            std::vector<app*> temp_hvars = this->coarse_data[rt_node];
            for(app* hvar : temp_hvars) {
                if(merged_hvars.find(hvar) == merged_hvars.end()) {
                    merged_hvars.insert(hvar);
                }
                if(hvar == this->th->global_emp) {
                    is_emp = true;
                }
            }
        }
        
        std::vector<app*> merged_result;
        if(is_emp) {
            merged_result.push_back(this->th->global_emp);
        }
        for(app* hvar : merged_hvars) {
            if(hvar != this->th->global_emp) {
                merged_result.push_back(hvar);
            }
        }
        for(enode* rt_node : nodes) {
            this->coarse_data[rt_node] = merged_result;
        }
    }

    int coarse_hvar_eq::is_in_same_class(app* hvar1, app* hvar2) {
        enode* hvar1_root_node = this->th->get_context().get_enode(hvar1)->get_root();
        enode* hvar2_root_node = this->th->get_context().get_enode(hvar2)->get_root();
        if(hvar1_root_node == hvar2_root_node) {
            return 1;
        } else  {
            return -1;
        }
    }


    app* coarse_hvar_eq::get_leader_hvar(app* hvar) {
        enode* hvar_root_node = this->th->get_context().get_enode(hvar)->get_root();
        if(this->is_emp_hvar(hvar) == 1) {
            return this->th->global_emp;
        } else {
            return this->coarse_data[hvar_root_node][0];
        }
    }

    int coarse_hvar_eq::is_emp_hvar(app* hvar) {
        enode* hvar_root_node = this->th->get_context().get_enode(hvar)->get_root();
        if(this->th->curr_emp_hterm_enodes.find(hvar_root_node) != this->th->curr_emp_hterm_enodes.end() || 
           this->th->get_context().get_enode(this->th->global_emp)->get_root() == hvar_root_node || 
           this->th->global_emp == hvar) {
            return 1;
        } else {
            return -1;
        }
    }


    std::vector<app*> coarse_hvar_eq::get_leader_hvars() {
        std::vector<app*> result;
        result.push_back(this->th->global_emp);
        for(auto pair : this->coarse_data) {
            bool pair_is_emp = false;
            for(app* temp_hvar : pair.second) {
                if(this->is_emp_hvar(temp_hvar) == 1) {
                    pair_is_emp = true;
                    continue;
                }
            }
            if(!pair_is_emp) {
                result.push_back(pair.second[0]);
            }
        }
        return result;
    }


    edge_labelled_dgraph::edge_labelled_dgraph(theory_slhv* t, locvar_eq* l, coarse_hvar_eq* h) {
        this->th = t;
        this->loc_eq = l;
        this->hvar_eq = h;
        this->construct_graph_from_theory();
        this->simplified = false;
    }

    edge_labelled_dgraph::edge_labelled_dgraph(theory_slhv* t, locvar_eq* l, coarse_hvar_eq* h, std::vector<dgraph_node*> ns, std::vector<dgraph_edge*> es, bool simplified) {
        this->th = t;
        this->loc_eq = l;
        this->hvar_eq = h;
        this->edges = es;
        this->nodes = ns;
        this->simplified = simplified;
    }

    void edge_labelled_dgraph::construct_graph_from_theory() {
        // construct nodes
        #ifdef SLHV_DEBUG
        std::cout << "construct nodes" << std::endl;
        #endif
        std::map<app*, dgraph_node*> node_map;
        std::vector<app*> leader_hvars = this->hvar_eq->get_leader_hvars();
        #ifdef SLHV_DEBUG
        for(app* e : leader_hvars) {
            std::cout << "leader var: " << mk_ismt2_pp(e, this->th->get_manager()) << std::endl;
        }
        #endif
        for(int i = 0; i < leader_hvars.size(); i ++) {
            SASSERT(!node_map[leader_hvars[i]]);
            dgraph_node* new_node = alloc(hvar_dgraph_node, this, leader_hvars[i]);
            node_map[leader_hvars[i]] = new_node;
            this->nodes.push_back(new_node);
        }
        std::set<std::pair<app*, app*>> addr_data_pairs;
        
        for(app* pt : this->th->curr_pts) {
            app* addr_loc_leader = this->loc_eq->get_leader_locvar(to_app(pt->get_arg(0)));
            app* data_loc_leader = this->loc_eq->get_leader_locvar(to_app(pt->get_arg(1)));
            addr_data_pairs.insert({addr_loc_leader, data_loc_leader});
        }
        for(auto pair : addr_data_pairs) {
            dgraph_node* new_node = alloc(pt_dgraph_node, this, pair.first, pair.second);
            this->nodes.push_back(new_node);
        }
        #ifdef SLHV_DEBUG
        std::cout << "construct edges" << std::endl;
        #endif
        // construct edges
        for(app* heap_equality : this->th->curr_heap_cnstr) {
            SASSERT(is_app_of(heap_equality, basic_family_id, OP_EQ));
            std::cout << "heap_equality: " << mk_ismt2_pp(heap_equality, this->th->get_manager()) << std::endl;
            app* left_hvar = to_app(heap_equality->get_arg(0));
            dgraph_node* from_dgraph_node = this->get_hvar_node(left_hvar);
            app* label = to_app(heap_equality->get_arg(1));
            if(this->th->is_uplus(label)) {
                #ifdef SLHV_DEBUG
                std::cout << "left hvar: " << mk_ismt2_pp(left_hvar, this->th->get_manager()) << " right label: " << mk_ismt2_pp(label, this->th->get_manager()) << std::endl;
                #endif
                // add edge if rhs of the equality is a uplus, since otherwise 
                // the equivalent class of hvar has already dealed with it
                for(int i = 0; i < label->get_num_args(); i ++) {
                    app* dst = to_app(label->get_arg(i));
                    dgraph_node* temp_to_dgraph_node = nullptr;
                    if(this->th->is_hvar(dst) || this->th->is_emp(dst)) {
                        temp_to_dgraph_node = this->get_hvar_node(dst);
                    } else if(this->th->is_points_to(dst)){
                        temp_to_dgraph_node = this->get_pt_node(dst);
                    } else {
                        SASSERT(false);
                        std::cout << "create dgraph edge: Currently unsupport !!" << std::endl;
                    }

                    dgraph_edge* new_edge = alloc(dgraph_edge, this, from_dgraph_node, temp_to_dgraph_node, label);
                    if(!this->has_edge(new_edge)) {
                        this->edges.push_back(new_edge);
                    }
                }
            }
        }
    }


    hvar_dgraph_node* edge_labelled_dgraph::get_hvar_node(app* orig_hvar){
        app* leader_hvar = this->hvar_eq->get_leader_hvar(orig_hvar);
        for(dgraph_node* n : nodes) {
            if(n->is_hvar()) {
                if(((hvar_dgraph_node *) n)->get_hvar_label() == leader_hvar) {
                    return (hvar_dgraph_node *) n;
                }
            }
        }
        std::cout << "get_hvar_dgraph_node error!!" << std::endl;
        return nullptr;
    }

    pt_dgraph_node* edge_labelled_dgraph::get_pt_node(app* orig_pt){
        app* orig_addr_loc = to_app(orig_pt->get_arg(0));
        app* orig_data_loc = to_app(orig_pt->get_arg(1));
        app* leader_addr_loc = this->loc_eq->get_leader_locvar(orig_addr_loc);
        app* leader_data_loc = this->loc_eq->get_leader_locvar(orig_data_loc);
        for(dgraph_node* n : nodes) {
            if(n->is_points_to()) {
                if(((pt_dgraph_node*)n)->get_pt_pair_label().first == leader_addr_loc &&
                   ((pt_dgraph_node*)n)->get_pt_pair_label().second == leader_data_loc) {
                    return (pt_dgraph_node*)n;
                }
            }
        }
        std::cout << "get_pt_dgraph_node error!!" << std::endl;
        return nullptr;
    }

    edge_labelled_dgraph* edge_labelled_dgraph::check_and_simplify() {
        SASSERT(!this->is_scc_computed());
        std::set<dgraph_node*> sources = this->get_sources();
        this->tarjanSCC(sources);
        #ifdef SLHV_DEBUG

        std::cout << "tarjan over and SCC infos: " << std::endl;
        for(dgraph_node* n : this->nodes) {
            n->print(std::cout);
            std::cout << std::endl;
        } 
        #endif
        std::map<int, int> nontrivial_SCC_ids;
        for(dgraph_node* n : this->nodes) {
            if(nontrivial_SCC_ids.find(n->get_low_index()) != nontrivial_SCC_ids.end()) {
                nontrivial_SCC_ids[n->get_low_index()] += 1;
            } else {
                nontrivial_SCC_ids[n->get_low_index()] = 0;
            }
        }
        std::set<int> nontrivial_ids;
        for(auto pair : nontrivial_SCC_ids) {
            if(pair.second > 0) {
                nontrivial_ids.insert(pair.first);
            }
        }
        // check whether some nontrivial scc can reach established node
        bool estab_reached = this->check_established_reachable(nontrivial_ids);
        if(estab_reached) {
            return nullptr;
        }
        #ifdef SLHV_DEBUG
        std::cout << "established reachable checked" << std::endl;
        #endif
        // compute the hvar eq after merging
        coarse_hvar_eq* new_hvar_eq = this->check_and_merge_scc_hvars(nontrivial_ids);
        if(new_hvar_eq == nullptr) {
            return nullptr;
        }
        #ifdef SLHV_DEBUG
        std::cout << "coarse hvar_eq computed after merging" << std::endl;
        #endif
        // compute the nodes that can be reached from some nontrivial scc
        std::set<dgraph_node*> deleted_nodes = this->get_simplified_nodes(nontrivial_ids);
        // compute the remaining node scc ids
        std::set<int> remained_nontrivial_ids = nontrivial_ids;
        for(dgraph_node* n : deleted_nodes) {
            remained_nontrivial_ids.erase(n->get_low_index());
        }

        #ifdef SLHV_DEBUG
        std::cout << "remained nontrivial ids: " << std::endl;
        for(int i : remained_nontrivial_ids) {
            std::cout << i << ",";
        }
        std::cout << std::endl;
        #endif
        // compute the remaining edges by deleting edges related to deleted nodes
        std::set<dgraph_edge*> remained_edges;
        for(dgraph_edge* e : this->edges) {
            if(deleted_nodes.find(e->get_from()) == deleted_nodes.end() &&
               deleted_nodes.find(e->get_to()) == deleted_nodes.end()) {
                    remained_edges.insert(e);
               }
        }
        std::vector<dgraph_node*> ns;
        std::vector<dgraph_edge*> es;
        edge_labelled_dgraph* new_graph = alloc(edge_labelled_dgraph, this->th, this->loc_eq, new_hvar_eq, ns, es, true);
        // create nodes for new graph
        for(dgraph_node* n : this->nodes) {
            if(nontrivial_ids.find(n->get_low_index()) == nontrivial_ids.end()) {
                if(n->is_points_to()) {
                    pt_dgraph_node* old_node = (pt_dgraph_node*)n;
                    pt_dgraph_node* new_node = alloc(pt_dgraph_node, new_graph, old_node->get_pt_pair_label().first, old_node->get_pt_pair_label().second);
                    new_node->set_dfs_index(old_node->get_dfs_index());
                    new_node->set_low_index(old_node->get_low_index());
                    new_graph->add_node(new_node);
                } else if(n->is_hvar()) {
                    hvar_dgraph_node* old_node = (hvar_dgraph_node*)n;
                    hvar_dgraph_node* new_node = alloc(hvar_dgraph_node, new_graph, old_node->get_hvar_label());
                    new_node->set_dfs_index(old_node->get_dfs_index());
                    new_node->set_low_index(old_node->get_low_index());
                    new_graph->add_node(new_node);
                } else {
                    SASSERT(false);
                }
            } 
        }

        for(int id : remained_nontrivial_ids) {
            hvar_dgraph_node* id_node = nullptr;
            for(dgraph_node* n : this->nodes) {
                if(id == n->get_low_index()) {
                    id_node = (hvar_dgraph_node*)n;
                    break;
                }
            }
            SASSERT(id_node->is_hvar());
            app* leader_hvar = id_node->get_hvar_label();
            app* leader_eq_repre = new_hvar_eq->get_leader_hvar(leader_hvar);
            hvar_dgraph_node* scc_node = alloc(hvar_dgraph_node, new_graph, leader_eq_repre);
            scc_node->set_dfs_index(0);
            scc_node->set_low_index(id);
            new_graph->add_node(scc_node);
        }
        // add edges for new graph
        for(dgraph_edge* e : remained_edges) {
            dgraph_node* new_from = new_graph->get_node_by_low(e->get_from()->get_low_index());
            dgraph_node* new_to = new_graph->get_node_by_low(e->get_to()->get_low_index());
            app* hterm_label = e->get_label();
            dgraph_edge* new_edge = alloc(dgraph_edge, new_graph, new_from, new_to, hterm_label);
            new_graph->add_edge(new_edge);
        }
        // TODO: add label complete here
        return new_graph;
    }

    bool edge_labelled_dgraph::is_scc_computed() {
        for(dgraph_node* n : this->nodes) {
            if(!n->is_tarjan_visited()) {
                return false;
            }
        }
        return true;
    }

    void edge_labelled_dgraph::add_node(dgraph_node* n)  {
        if(std::find(this->nodes.begin(), this->nodes.end(), n) != nodes.end())  {
            std::cout << "node already exists" << std::endl;
        } else {
            this->nodes.push_back(n);
        }
    }

    void edge_labelled_dgraph::add_edge(dgraph_edge* e) {
        for(dgraph_edge* ee : this->edges) {
            if(ee->get_from() == e->get_from() &&
               ee->get_to() == e->get_to() &&
               ee->get_label() == e->get_label()) {
                return;
               }
        }
        this->edges.push_back(e);
    }

    dgraph_node* edge_labelled_dgraph::get_node_by_low(int low_idx) {
        for(dgraph_node* n : this->nodes) {
            if(n->get_low_index() == low_idx) {
                return n;
            }
        }
        return nullptr;
    }

    std::vector<edge_labelled_subgraph*> edge_labelled_dgraph::extract_all_rooted_disjoint_labelcomplete_subgraphs(dgraph_node* root, 
     std::map<dgraph_node*, std::vector<edge_labelled_subgraph*>>& node2subgraphs) {
        // enumerate all subgraphs
        #ifdef SLHV_DEBUG
        std::cout << "extract all rooted disjoint label complete subgraphs for node ";
        root->print(std::cout);
        std::cout << std::endl;
        #endif
        // if computed
        if(node2subgraphs.find(root) != node2subgraphs.end()) {
            return node2subgraphs[root];
        }
        // if the node is leaf node:
        if(!this->has_edge_from(root)) {
            std::vector<edge_labelled_subgraph*> result;
            std::vector<dgraph_node*> ns; ns.insert(ns.begin(), root);
            std::vector<dgraph_edge*> es;
            edge_labelled_subgraph* subgraph = alloc(edge_labelled_subgraph, 
                this, ns, es
            );
            result.push_back(subgraph);
            #ifdef SLHV_DEBUG
            std::cout << "is leaf node" << std::endl;
            subgraph->print(std::cout);
            #endif
            node2subgraphs[root] = result;
            return result;
        } else {
            std::set<dgraph_edge*> root_edges;
            std::set<app*> edge_labels;
            for(dgraph_edge* e : this->edges) {
                if(e->get_from() == root) {
                    root_edges.insert(e);
                    edge_labels.insert(e->get_label());
                }
            }
            
            std::vector<edge_labelled_subgraph*> subgraphs;
            for(app* label : edge_labels) {
                std::vector<dgraph_edge*> curr_es;
                std::vector<dgraph_node*> curr_ns;
                std::set<dgraph_edge*> edges2merge;
                curr_ns.insert(curr_ns.begin(), root);
                for(dgraph_edge* e : root_edges) {
                    if(e->get_label() == label) {
                        curr_es.insert(curr_es.begin(), e);
                        if(node2subgraphs.find(e->get_to()) == node2subgraphs.end()) {
                            node2subgraphs[e->get_to()] =  this->extract_all_rooted_disjoint_labelcomplete_subgraphs(e->get_to(), node2subgraphs);
                        }
                        edges2merge.insert(e);
                    }
                }
                // TODO:  merge them
                std::vector<edge_labelled_subgraph*> curr_result;
                std::vector<edge_labelled_subgraph*> next_result;
                curr_ns.push_back(root);
                for(dgraph_edge* e : edges2merge) {
                    curr_es.push_back(e);
                    curr_ns.push_back(root);
                }
                edge_labelled_subgraph* stem_graph = alloc(edge_labelled_subgraph, this, curr_ns, curr_es);
                curr_result.push_back(stem_graph);
                for(dgraph_edge* e : edges2merge) {
                    next_result = this->subgraphs_union(curr_result, node2subgraphs[e->get_to()]);
                    curr_result = next_result;
                }
                for(edge_labelled_subgraph* sb : curr_result) {
                    subgraphs.push_back(sb);
                }
            }
            node2subgraphs[root] = subgraphs;
            return subgraphs;
        }
    }

    std::vector<edge_labelled_subgraph*> edge_labelled_dgraph::subgraphs_union(std::vector<edge_labelled_subgraph*> graphs1, std::vector<edge_labelled_subgraph*> graphs2) {
        std::vector<edge_labelled_subgraph*> result;
        for(edge_labelled_subgraph* sg1 : graphs1) {
            for(edge_labelled_subgraph* sg2 : graphs2) {
                SASSERT(sg1->get_parent() == sg2->get_parent());
                edge_labelled_dgraph* parent = sg1->get_parent();
                std::set<dgraph_node*> merged_nodes;
                std::set<dgraph_edge*> merged_edges;
                for(dgraph_node* n : sg1->get_nodes()) {
                    merged_nodes.insert(n);
                }
                for(dgraph_node* n : sg2->get_nodes()) {
                    merged_nodes.insert(n);
                }
                for(dgraph_edge* e : sg1->get_edges()) {
                    merged_edges.insert(e);
                }
                for(dgraph_edge* e : sg2->get_edges()) {
                    merged_edges.insert(e);
                }
                std::vector<dgraph_node*> curr_ns;
                std::vector<dgraph_edge*> curr_es;
                for(dgraph_node* n : merged_nodes) {
                    curr_ns.push_back(n);
                }
                for(dgraph_edge* e : merged_edges) {
                    curr_es.push_back(e);
                }
                edge_labelled_subgraph* merged_graph = alloc(edge_labelled_subgraph, parent, curr_ns, curr_es);
                result.push_back(merged_graph);
            }
        }
        return result;
    }



    edge_labelled_subgraph::edge_labelled_subgraph(edge_labelled_dgraph* g, std::vector<dgraph_node*> ns, std::vector<dgraph_edge*> es) : edge_labelled_dgraph(g->get_th(), g->get_locvar_eq(), g->get_hvar_eq(), ns, es, g->get_simplified()){
        for(dgraph_node* n : ns) {
            SASSERT(n->get_dgraph() == g);
        }
        for(dgraph_edge* e : es) {
            SASSERT(e->get_dgraph() == g);
        }
        this->parent = g;
    }

    hterm* edge_labelled_subgraph::obtain_graph_hterm() {
        std::set<std::pair<app*, app*>> rep_hterm;
        std::set<dgraph_node*> leaves = this->get_dest_nodes();
        for(dgraph_node* n : leaves) {
            if(n->is_hvar()) {
                hvar_dgraph_node* hvar_node = (hvar_dgraph_node*) n;
                if(rep_hterm.find({hvar_node->get_hvar_label(), nullptr}) != rep_hterm.end()) {
                    rep_hterm.erase({hvar_node->get_hvar_label(), nullptr});
                }
                rep_hterm.insert({hvar_node->get_hvar_label(), nullptr});
            } else if(n->is_points_to()) {
                pt_dgraph_node* pt_node = (pt_dgraph_node*) n;
                SASSERT(rep_hterm.find(pt_node->get_pt_pair_label()) == rep_hterm.end());
                rep_hterm.insert(pt_node->get_pt_pair_label());
            } else {
                SASSERT(false);
            }
        }
        if(rep_hterm.size() == 0) {
            rep_hterm.insert({this->get_th()->global_emp, nullptr});
        }
        hterm* result = alloc(hterm, rep_hterm, this->get_hvar_eq(), this->get_locvar_eq());
        return result;
    }

    bool edge_labelled_subgraph::is_rooted_disjoint_labelcomplete() {
        // single root
        std::set<dgraph_node*> root = this->get_sources();
        if(root.size() != 1) {
            return false;
        }
        // each node can be reached from single root and no loop exists
        std::set<dgraph_node*> visited_nodes; 
        std::set<dgraph_node*> newly_visited;
        newly_visited.insert(*root.begin());
        while(newly_visited.size() > 0) {
            std::set<dgraph_node*> next_newly_visited;
            for(dgraph_node* frontier : newly_visited) {
                for(dgraph_edge* e : this->get_edges()) {
                    if(e->get_from() == *root.begin()) {
                        if(visited_nodes.find(e->get_to()) !=  visited_nodes.end() || newly_visited.find(e->get_to()) != newly_visited.end()){
                            return false;
                        }
                        next_newly_visited.insert(e->get_to());
                    }
                }
            }
            visited_nodes = slhv_util::setUnion(visited_nodes, newly_visited);
            newly_visited = next_newly_visited;
        }
        for(dgraph_node* n : this->get_nodes()) {
            if(visited_nodes.find(n) == visited_nodes.end()) {
                return false;
            }
        }
        // all outgoing edges of a node share the same label
        for(dgraph_node* n : this->get_nodes()) {
            app* outgoing_label = nullptr;
            for(dgraph_edge* e : this->get_edges()) {
                if(outgoing_label == nullptr) {
                    outgoing_label = e->get_label();
                } else {
                    if(e->get_label() != outgoing_label) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    dgraph_node* edge_labelled_dgraph::get_root_node() {
        SASSERT(this->is_rooted());
        return *this->get_sources().begin();
    }

    std::set<dgraph_node*> edge_labelled_dgraph::get_dest_nodes() {
        std::set<dgraph_node*> leaves;
        for(dgraph_node* n : this->nodes) {
            bool is_dst = true;
            for(dgraph_edge* e : this->edges) {
                if(e->get_from() == n) {
                    is_dst = false;
                    break;
                }
            }
            if(is_dst) {
                leaves.insert(n);
            }
        }
        return leaves;
    }

    std::set<dgraph_node*> edge_labelled_dgraph::get_sources() {
        std::map<dgraph_node*, bool> is_source_map;
        for(dgraph_node* n : this->nodes) {
            is_source_map[n] = true;
        }
        for(dgraph_edge* e : this->edges) {
            is_source_map[e->get_to()] = false;
        }
        std::set<dgraph_node*> result;
        for(auto p : is_source_map) {
            if(p.second) {
                result.insert(p.first);
            }
        }
        return result;
    }

    dgraph_node* edge_labelled_dgraph::get_unvisited() {
        for(dgraph_node* n : this->nodes) {
            if(!n->is_tarjan_visited()) {
                return n;
            }
        }
        return nullptr;
    }

    bool edge_labelled_dgraph::check_established_reachable(std::set<int> nontrivial_ids) {
        SASSERT(this->is_scc_computed());
        std::set<dgraph_node*> established_reachable_nodes;
        for(dgraph_node* n : this->nodes) {
            if(n->is_established()) {
                established_reachable_nodes.insert(n);
            }
        }
        std::set<dgraph_node*> next_nodes = established_reachable_nodes;
        do {
            established_reachable_nodes = next_nodes;
            for(dgraph_edge* e : this->edges) {
                if(established_reachable_nodes.find(e->get_to()) !=  established_reachable_nodes.end()) {
                    next_nodes.insert(e->get_from());
                }
            }
        } while(next_nodes.size() - established_reachable_nodes.size() > 0);
        for(dgraph_node* n : established_reachable_nodes) {
            if(nontrivial_ids.find(n->get_low_index()) != nontrivial_ids.end()) {
                this->th->set_conflict_slhv(false);
                this->th->check_status = theory_slhv::slhv_unsat;
                return true;
            }
        }
        return false;
    }

    coarse_hvar_eq* edge_labelled_dgraph::check_and_merge_scc_hvars(std::set<int> nontrivial_ids) {
        SASSERT(this->is_scc_computed());
        std::vector<std::set<enode*>> enode_sets_to_merge;
        for(int id : nontrivial_ids) {
            std::set<dgraph_node*> nodes2merge;
            std::set<enode*> enode_set;
            for(dgraph_node* n : this->nodes) {
                if(n->get_low_index() == id) {
                    nodes2merge.insert(n);
                    SASSERT(!n->is_points_to());
                    hvar_dgraph_node* hvar_node = (hvar_dgraph_node*) n;
                    app* leader_hvar = hvar_node->get_hvar_label();
                    enode* leader_hvar_node = this->th->get_context().get_enode(leader_hvar)->get_root();
                    enode_set.insert(leader_hvar_node);
                }
                for(enode_pair p : this->th->curr_distinct_hterm_pairs) {
                    if(enode_set.find(p.first) != enode_set.end() && 
                       enode_set.find(p.second) != enode_set.end()) {
                            this->th->check_status = theory_slhv::slhv_unsat;
                            this->th->set_conflict_slhv(false);
                            return nullptr;
                       }
                }
                enode_sets_to_merge.push_back(enode_set);
            }
        }
        // new hvar equivalence class
        coarse_hvar_eq* new_hvar_eq = this->hvar_eq->merge_hvar_nodes(enode_sets_to_merge);
        return new_hvar_eq;
    }


    std::set<dgraph_node*> edge_labelled_dgraph::get_simplified_nodes(std::set<int> nontrivial_ids) {
        // return the set of ids that the nodes are simplified and eliminated in the simplified graph
        SASSERT(this->is_scc_computed());
        std::set<dgraph_node*> to_nodes;
        for(dgraph_node* n : this->nodes) {
            if(nontrivial_ids.find(n->get_low_index()) != nontrivial_ids.end()) {
                to_nodes.insert(n);
            }
        }
        std::set<dgraph_node*> temp_nodes = to_nodes;
        do {
            std::set<dgraph_node*> new_nodes;
            for(dgraph_node* n : temp_nodes) {
                for(dgraph_edge* e : this->edges) {
                    if(e->get_from() == n && to_nodes.find(e->get_to()) == to_nodes.end()) {
                        new_nodes.insert(e->get_to());
                    }
                }
            }
            temp_nodes = new_nodes;
            to_nodes = slhv_util::setUnion(to_nodes, new_nodes);
        } while(temp_nodes.size() != 0);
        for(dgraph_node* n : to_nodes) {
            if(nontrivial_ids.find(n->get_low_index()) != nontrivial_ids.end()) {
                to_nodes.erase(n);
            }
        }
        return to_nodes;
    }

    std::vector<dgraph_edge*> edge_labelled_dgraph::get_edges_from_node(dgraph_node* n) {
        std::vector<dgraph_edge*> result;
        for(dgraph_edge* e : this->edges) {
            if(e->get_from() == n) {    
                result.push_back(e);
            }
        }
        return result;
    }

    void edge_labelled_dgraph::tarjanSCC(std::set<dgraph_node*> tarjanSCC) {
        int dfs_num = 1;
        for(dgraph_node* n : this->get_sources()) {
            n->tarjanSCC(dfs_num);
        }
        dgraph_node* curr_unvisited = this->get_unvisited();
        while(curr_unvisited != nullptr) {
            curr_unvisited->tarjanSCC(dfs_num);
            curr_unvisited = this->get_unvisited();
        }
        for(dgraph_node* n : this->nodes) {
            SASSERT(n->is_tarjan_visited());
        }
    }


    bool edge_labelled_dgraph::has_edge(dgraph_edge* edge){
        for(dgraph_edge* e : this->edges) {
            if(e->get_from() == edge->get_from() && 
               e->get_to() == edge->get_to() &&
               e->get_label() == edge->get_label()) {
                return true;
               } 
        }
        return false;
    }

    bool edge_labelled_dgraph::has_edge_from(dgraph_node* node) {
        for(dgraph_edge* e : this->edges) {
            if(e->get_from() == node) {
                return true;
            }
        }
        return false;
    }

    bool edge_labelled_dgraph::has_edge_to(dgraph_node* node) {
        for(dgraph_edge* e : this->edges) {
            if(e->get_to() == node) {
                return true;
            }
        }
        return false;
    }

    dgraph_node::dgraph_node(edge_labelled_dgraph* g) {
        this->dgraph = g;
        this->dfs_index = -1;
        this->low_index = -1;
    }

    int dgraph_node::tarjanSCC(int& dfs_num) {
        if(this->dfs_index == -1) {
            this->low_index = dfs_num;
            this->dfs_index = dfs_num;
            dfs_num += 1;
        } else {
            return this->low_index;
        }
        std::vector<dgraph_edge*> edges = this->dgraph->get_edges_from_node(this);
        for(dgraph_edge* e : edges) {
            dgraph_node* curr_next_node = e->get_to();
            if(curr_next_node->dfs_index == -1) {
                int ret_low_index = curr_next_node->tarjanSCC(dfs_num);
                if(ret_low_index < this->low_index) {
                    this->low_index = ret_low_index;
                }
            }
        }
        return this->low_index;
    }


    hvar_dgraph_node::hvar_dgraph_node(edge_labelled_dgraph* g, app* hvar) : dgraph_node(g){
        this->leader_hvar = hvar;
    }

    pt_dgraph_node::pt_dgraph_node(edge_labelled_dgraph* g, app* pt_addr, app* pt_data) : dgraph_node(g) {
        this->pt_addr_leader = pt_addr;
        this->pt_data_leader = pt_data;
    }
    
    // dgraph edge
    dgraph_edge::dgraph_edge(edge_labelled_dgraph* g, dgraph_node* f, dgraph_node* t, app* hterm_label) {
        this->dgraph = g;
        this->from = f;
        this->to = t;
        this->hterm_label = hterm_label;
    }

    // graph print functions
    void pt_dgraph_node::print(std::ostream& out) {
        auto pt_pair = this->get_pt_pair_label();
        out << "(N)-(PT)-(pt " << mk_ismt2_pp(pt_pair.first, this->get_dgraph()->get_th()->get_manager()) << " " << mk_ismt2_pp(pt_pair.second, this->get_dgraph()->get_th()->get_manager()) << ")-(" << this->get_dfs_index() << ", " << this->get_low_index() << ")";
    }

    void hvar_dgraph_node::print(std::ostream& out) {
        auto hvar_label = this->get_hvar_label();
        out << "(N)-(HVAR)-(" << mk_ismt2_pp(hvar_label, this->get_dgraph()->get_th()->get_manager()) << ")-(" << this->get_dfs_index() << ", " << this->get_low_index() << ")";
    }

    void dgraph_edge::print(std::ostream& out) {
        out << "["; this->from->print(out); out << "]" << "<" << mk_ismt2_pp(this->hterm_label, this->get_dgraph()->get_th()->get_manager()) << ">["; this->to->print(out); out << "]" << std::endl;
    }

    void edge_labelled_dgraph::print(std::ostream& out) {
        out << "-------" << std::endl;
        out << "dgraph nodes: " << std::endl;
        for(dgraph_node* n : this->nodes) {
            n->print(std::cout);
            out << std::endl;
        }
        out << "dgraph edges:" << std::endl;
        for(dgraph_edge* e : this->edges) {
            e->print(std::cout);
        }
    }

    // hterm class
    bool hterm::is_sub_hterm_of(hterm* ht) {
        SASSERT(this->h_eq == ht->get_h_eq());
        std::set<std::pair<app*, app*>> h_atoms_larger = ht->get_h_atoms();
        if(slhv_util::setIsSubset(h_atoms_larger, this->h_atoms)) {
            return true;
        } else {
            return false;
        }
    }

    bool hterm::is_super_hterm_of(hterm* ht) {
        SASSERT(this->h_eq == ht->get_h_eq());
        if(slhv_util::setIsSubset(this->get_h_atoms(), ht->get_h_atoms())) {
            return true;
        } else {
            return false;
        }
    }

    bool hterm::is_established() {
        for(auto p : this->h_atoms) {
            if(p.second != nullptr) {
                return true;
            }
        }
        return false;
    }

    bool hterm::is_emp() {
        SASSERT(this->h_atoms.size() > 0);
        if(this->h_atoms.size() == 1 && (*this->h_atoms.begin()).first == this->h_eq->get_emp()) {
            return true;
        } else {
            return false;
        }
    }

    std::set<hterm*> hterm::get_all_atom_hterms() {
        std::set<hterm*> result;
        for(auto app_pair : this->h_atoms) {
            std::set<std::pair<app*, app*>> atom;
            atom.insert(app_pair); 
            hterm* atom_hterm = alloc(hterm, atom, this->h_eq, this->loc_eq);
            result.insert(atom_hterm);
        }
        return result;
    }


    std::set<hterm*> hterm::generate_all_subhterms() {
        std::set<hterm*> curr_result;
        std::set<hterm*> next_result;
        std::set<std::pair<app*, app*>> empty;
        hterm* emp_hterm = alloc(hterm, empty, this->h_eq, this->loc_eq);
        for(std::pair<app*, app*> curr_atom : this->h_atoms) {
            next_result = this->concat_subhterms(curr_result, curr_atom);
            curr_result = next_result;
        }
        return curr_result;
    }

    void hterm::print_app_pair(std::pair<app*, app*> p, std::ostream& os) {
        if(p.second != nullptr) {
            os << mk_ismt2_pp(p.first, this->loc_eq->get_th()->get_manager()) << " -> " << mk_ismt2_pp(p.second, this->loc_eq->get_th()->get_manager());
        } else {
            os << mk_ismt2_pp(p.first, this->loc_eq->get_th()->get_manager());
        }
    }
    void hterm::print(std::ostream& os) {
        if(this->h_atoms.size() > 1) {
            os << "(hterm ";
            for(auto p : this->h_atoms) {
                this->print_app_pair(p, os);
                os <<  ", ";
            }
            os << ")";
        } else {
            
            os << "(hterm ";
            this->print_app_pair(*this->h_atoms.begin(), os);
            os << ")";
        }
    }


    std::set<hterm*> hterm::concat_subhterms(std::set<hterm*> hterm_set, std::pair<app*, app*> curr_atom) {
        for(hterm* ht : hterm_set) {
            for(auto pair : ht->get_h_atoms()) {
                SASSERT(pair != curr_atom);
            }
        }
        std::set<hterm*> result_hterm_set;
        for(hterm* ht : hterm_set) {
            if(ht->get_h_atoms().size() == 1 && (*ht->get_h_atoms().begin()).first == this->h_eq->get_emp()) {
                std::set<std::pair<app*, app*>> contain_set;
                contain_set.insert(curr_atom);
                hterm* contain_hterm = alloc(hterm, contain_set, this->h_eq, this->loc_eq);
                hterm* not_contain_hterm = ht;
                result_hterm_set.insert(contain_hterm);
                result_hterm_set.insert(not_contain_hterm);
            } else {
                std::set<std::pair<app*, app*>> contain_set = ht->get_h_atoms();
                contain_set.insert(curr_atom);
                hterm* contain_hterm = alloc(hterm, contain_set, this->h_eq, this->loc_eq);
                hterm* not_contain_hterm = ht;
                result_hterm_set.insert(contain_hterm);
                result_hterm_set.insert(not_contain_hterm);
            }
        }
        return result_hterm_set;
    }

    hterm* hterm::substract_hterm(hterm* substractor) {
        SASSERT(substractor->is_sub_hterm_of(this));
        SASSERT(this->h_eq == substractor->get_h_eq());
        std::set<std::pair<app*, app*>> h_atom_remained = slhv_util::setSubstract(this->h_atoms, substractor->get_h_atoms());
        hterm* result = alloc(hterm, h_atom_remained, this->h_eq, this->loc_eq);
        return result;
    }


    hterm* hterm::replace_subhterm(hterm* orig_subhterm, hterm* replaced_subhterm) {
        SASSERT(orig_subhterm->is_sub_hterm_of(this));
        SASSERT(this->h_eq == orig_subhterm->get_h_eq() && this->h_eq == replaced_subhterm->get_h_eq());
        std::set<std::pair<app*, app*>> h_atom_replaced = slhv_util::setUnion(
            slhv_util::setSubstract(this->h_atoms, orig_subhterm->get_h_atoms()),
            replaced_subhterm->get_h_atoms()
        );
        hterm* result = alloc(hterm, h_atom_replaced, this->h_eq, this->loc_eq);
        return result;
    }
    // equiheap relation
    void equiheap_relation::add_hterm(hterm* ht) {
        SASSERT(ht->get_loc_eq() == this->loc_eq && ht->get_h_eq() == this->h_eq);
        for(hterm* t : this->hterm_set) {
            if(*ht == *t) {
                break;
            }
        }
        this->hterm_set.insert(ht);
    }

    void equiheap_relation::add_pair(hterm* ht1, hterm* ht2) {
        for(auto p : this->equiv_pairs) {
            if(*p.first == *ht1 && *p.second == *ht2 || 
               *p.second == *ht1 && *p.first == *ht2) {
                break;
            }
        }
        this->equiv_pairs.insert({ht1, ht2});
    }


    bool equiheap_relation::construct_equiv_class() {
        for(auto p : this->equiv_pairs) {
            SASSERT(this->hterm_set.find(p.first) != this->hterm_set.end());
            SASSERT(this->hterm_set.find(p.second) != this->hterm_set.end());
        }
        for(hterm* t : this->hterm_set) {
            std::set<hterm*> singleton{t};
            this->equiv_class[t] = singleton;
        }
        for(auto p : this->equiv_pairs) {
            std::set<hterm*> all_equal_hterms = slhv_util::setUnion(this->equiv_class[p.first], this->equiv_class[p.second]);
            for(hterm* t : all_equal_hterms) {
                this->equiv_class[t] = all_equal_hterms;
            }
        }
        
        bool is_consistent = this->check_inconsistency();
        return is_consistent;
    }

    bool equiheap_relation::check_inconsistency() {
        SASSERT(this->loc_eq != nullptr && this->h_eq != nullptr);
        std::set<std::set<hterm*>> distinct_hterm_eq_set;
        for(auto record : this->equiv_class) {
            if(distinct_hterm_eq_set.find(record.second) == distinct_hterm_eq_set.end()) {
                distinct_hterm_eq_set.insert(record.second);
            }
        }
        for(std::set<hterm*> hterm_eq : distinct_hterm_eq_set) {
            for(hterm* ht1 : hterm_eq) {
                for(hterm* ht2 : hterm_eq) {
                    // CRITICAL: need to prove that this is correct regarding the satisfiability
                    if(ht1->get_all_atom_hterms().size() == 1 && ht2->get_all_atom_hterms().size() == 1) {
                        std::set<std::pair<app*, app*>> ht1_app_pairs = (*ht1->get_all_atom_hterms().begin())->get_h_atoms();
                        std::set<std::pair<app*, app*>> ht2_app_pairs = (*ht2->get_all_atom_hterms().begin())->get_h_atoms();
                        // Situation 1: established equal to empty
                        if((*ht1->get_all_atom_hterms().begin())->is_established() && 
                           (*ht2->get_all_atom_hterms().begin())->is_emp()) {
                            return false;
                        }
                        // Situation 2: established equal established but with different address or same address with different data
                        if((*ht1->get_all_atom_hterms().begin())->is_established() &&
                           (*ht2->get_all_atom_hterms().begin())->is_established()) {
                            std::pair<app*, app*> ht1_app = *ht1_app_pairs.begin();
                            std::pair<app*, app*> ht2_app = *ht2_app_pairs.begin();
                            app* ht1_addr = to_app(ht1_app.second->get_arg(0));
                            app* ht1_data = to_app(ht1_app.second->get_arg(1));
                            app* ht2_addr = to_app(ht2_app.second->get_arg(0));
                            app* ht2_data = to_app(ht2_app.second->get_arg(1));
                            if(this->loc_eq->get_leader_locvar(ht1_addr) != this->loc_eq->get_leader_locvar(ht2_addr)) {
                                return false;
                            } else {
                                if(this->loc_eq->get_leader_locvar(ht1_data) != this->loc_eq->get_leader_locvar(ht2_data)) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
        return true;
    }

    // subheap relation
    void subheap_relation::add_pair(hterm* ht_smaller, hterm* ht_larger) {
        for(auto smaller_ht : ht_smaller->get_h_atoms()) {
            if(smaller_ht.second != nullptr) {
                for(auto larger_ht : ht_larger->get_h_atoms()) {
                    if(larger_ht.second != nullptr && larger_ht.first == smaller_ht.first && smaller_ht.second != larger_ht.second) {
                        SASSERT(false);
                        // this should not happen
                    }
                }
            }
        }
        this->subheap_pairs.insert({ht_smaller, ht_larger});
    }

    void subheap_relation::add_equal(hterm* first, hterm* second) {
        this->add_pair(first, second);
        this->add_pair(second, first);
    }

    bool subheap_relation::contain_hterm(hterm* ht) {
        if(this->hterm_set.find(ht) != this->hterm_set.end()) {
            return true;
        } else {
            return false;
        }
    }

    bool subheap_relation::is_subheap(hterm* smaller, hterm* larger) {
        if(this->contain_hterm(smaller) && this->contain_hterm(larger)) {
            for(auto pair : this->subheap_pairs) {
                if(smaller == pair.first && larger == pair.second) {
                    return true;
                }
            }
            return false;
        } else {
            return false;
        }
    }

    bool subheap_relation::is_equal_heap(hterm* first, hterm* second) {
        if(this->contain_hterm(first) && this->contain_hterm(second)) {
            bool subheap, overheap = false;
            for(auto pair : this->subheap_pairs) {
                if(first == pair.first && second == pair.second) {
                    subheap = true;
                }
                if(first == pair.second && second == pair.first) {
                    overheap = true;
                }
                if(subheap && overheap) {
                    return true;
                }
            }
            return false;
        } else {
            if(slhv_util::setEqual(first->get_h_atoms(), second->get_h_atoms())) {
                return true;
            } else {
                return false;
            }
        }
    }

    std::set<hterm*> subheap_relation::get_all_smaller_hterms(hterm* larger) {
        SASSERT(this->contain_hterm(larger));
        std::set<hterm*> result;
        for(auto pair : this->subheap_pairs) {
            if(pair.second == larger) {
                result.insert(pair.first);
            }
        }
        return result;
    }




    std::set<std::pair<hterm*, hterm*>> subheap_relation::extract_equivalent_hterms() {
        std::set<std::pair<hterm*, hterm*>> result; 
        for(auto p1 : this->subheap_pairs) {
            for(auto p2 : this->subheap_pairs) {
                if(p1.first == p2.second && p2.second == p1.first) {
                    result.insert({p1.first, p1.second});
                }
            }
        }
        return result;
    }
    
    void subheap_relation::print(std::ostream& os) {
        os << "subheap relation hterm set: " << std::endl;
        for(hterm* ht : this->hterm_set) {
            ht->print(os);
            os << std::endl;
        }
        os << "subheap pairs: " << std::endl;
        for(auto p : subheap_pairs) {
            p.first->print(os);
            os  << " <= ";
            p.second->print(os);
            os << std::endl;
        }
    }



    // syntax maker

    slhv_syntax_maker::slhv_syntax_maker(theory_slhv* th) {
        this->th = th;
        this->fv_maker = alloc(slhv_fresh_var_maker, th);
        this->slhv_decl_plug = (slhv_decl_plugin*) this->th->get_manager().get_plugin(this->th->get_family_id());
    }

    void slhv_syntax_maker::reset_fv_maker() {
        this->fv_maker->reset();
    }

    app* slhv_syntax_maker::mk_fresh_datavar() {
        return this->fv_maker->mk_fresh_datavar();
    }

    app* slhv_syntax_maker::mk_fresh_hvar() {
        return this->fv_maker->mk_fresh_hvar();
    }

    app* slhv_syntax_maker::mk_fresh_locvar() {
        return this->fv_maker->mk_fresh_locvar();
    }

    app* slhv_syntax_maker::mk_read_formula(app* from_hvar, app* read_addr, app* read_data) {
        SASSERT(this->th->is_hvar(from_hvar));
        app* fresh_hvar = this->mk_fresh_hvar();
        app* new_eq_left = from_hvar;
        int right_arg_num = 2;
        std::vector<app*> right_args;
        right_args.push_back(fresh_hvar);
        right_args.push_back(this->mk_points_to(read_addr, read_data));
        app* new_eq_right = this->mk_uplus(right_arg_num, right_args);
        // includes internalize:
        // literal result = this->th->mk_eq(new_eq_left, new_eq_right, false);

        app_ref result(this->th->get_context().mk_eq_atom(new_eq_left, new_eq_right), this->th->get_manager());
        
        this->th->get_context().internalize(result, false);
        return result;
    }

    app* slhv_syntax_maker::mk_read_formula_new(app* from_hvar, app* read_addr, int read_field, app* read_item) {
        bool is_read_loc = false;
        if(read_field + 1 - this->th->pt_locfield_num >= 0) {
            is_read_loc = true;
        }
        int read_index = is_read_loc ? read_field : read_field - this->th->pt_locfield_num;
        if(is_read_loc) {
            app* fresh_hvar = this->mk_fresh_hvar();
            app* eq_lhs = from_hvar;
            std::vector<app*> locvars_vec;
            std::vector<app*> datavars_vec;
            for(int i = 0; i < this->th->pt_locfield_num; i ++) {
                if(i == read_index) {
                    locvars_vec.push_back(read_item);
                } else {
                    locvars_vec.push_back(this->mk_fresh_locvar());
                }
            }
            for(int i = 0; i < this->th->pt_datafield_num; i ++) {
                datavars_vec.push_back(this->mk_fresh_datavar());
            }
            app* rhs_record = this->mk_record(locvars_vec, datavars_vec);
            app* rhs_points_to = this->mk_points_to_new(read_addr, rhs_record);
            std::vector<app*> rhs_uplus_args;
            rhs_uplus_args.push_back(fresh_hvar);
            rhs_uplus_args.push_back(rhs_points_to);
            app* eq_rhs = this->mk_uplus(2, rhs_uplus_args);
            app_ref result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());

            this->th->get_context().internalize(result, false);
            return result;
        } else {
            app* fresh_hvar = this->mk_fresh_hvar();
            app* eq_lhs = from_hvar;
            std::vector<app*> locvars_vec;
            std::vector<app*> datavars_vec;
            for(int i = 0; i < this->th->pt_locfield_num; i ++) {
                locvars_vec.push_back(this->mk_fresh_locvar());
            }
            for(int i = 0; i < this->th->pt_datafield_num; i ++) {
                if(i == read_index) {
                    datavars_vec.push_back(read_item);
                } else {
                    datavars_vec.push_back(this->mk_fresh_datavar());
                }
            }
            app* rhs_record = this->mk_record(locvars_vec, datavars_vec);
            app* rhs_points_to = this->mk_points_to_new(read_addr, rhs_record);
            std::vector<app*> rhs_uplus_args;
            rhs_uplus_args.push_back(fresh_hvar);
            rhs_uplus_args.push_back(rhs_points_to);
            app* eq_rhs = this->mk_uplus(2, rhs_uplus_args);
            app_ref result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());

            this->th->get_context().internalize(result, false);
            return result;
        }
    }

    app* slhv_syntax_maker::mk_write_formula(app* orig_hvar, app* writed_hvar, app* write_addr, app* write_data) {
        
        app* fresh_hvar = this->mk_fresh_hvar();
        app* fresh_locvar = this->mk_fresh_locvar();
        app* first_eq_left = orig_hvar;
        app* first_eq_right_pt = this->mk_points_to(write_addr, fresh_hvar);
        std::vector<app*> first_uplus_args;
        first_uplus_args.push_back(fresh_hvar);
        first_uplus_args.push_back(first_eq_right_pt);
        app* first_eq_right = this->mk_uplus(2, first_uplus_args);
        // app* first_eq = this->th->mk_eq(first_eq_left, first_eq_right, false);
        app_ref first_eq(this->th->get_context().mk_eq_atom(first_eq_left, first_eq_right), this->th->get_manager());
        this->th->get_context().internalize(first_eq, false);

        app* second_eq_left = writed_hvar;
        app* second_eq_right_pt = this->mk_points_to(write_addr, write_data);
        std::vector<app*> second_uplus_args;
        second_uplus_args.push_back(fresh_hvar);
        second_uplus_args.push_back(second_eq_right_pt);
        app* second_eq_right = this->mk_uplus(2, second_uplus_args);
        // app* second_eq = this->th->mk_eq(second_eq_left, second_eq_right, false);
        app_ref second_eq(this->th->get_context().mk_eq_atom(second_eq_left, second_eq_right), this->th->get_manager());
        this->th->get_context().internalize(second_eq, false);

        app* final_result = this->th->get_manager().mk_and(first_eq, second_eq);
        // the ast made by manager should be internalize manually
        this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_write_formula_new(app* orig_hvar, app* writed_hvar, app* write_addr, int write_field, app* write_item) {
        bool is_write_loc = false;
        if(write_field + 1 - this->th->pt_locfield_num >= 0) {
            is_write_loc = true;
        }
        int write_index = is_write_loc ? write_field : write_field - this->th->pt_locfield_num;
            
        app* fresh_hvar = this->mk_fresh_hvar();
        std::vector<app*> first_locvars_vec;
        std::vector<app*> first_datavars_vec;
        for(int i = 0; i < this->th->pt_locfield_num; i ++) {
            first_locvars_vec.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < this->th->pt_datafield_num; i ++) {
            first_datavars_vec.push_back(this->mk_fresh_datavar());
        }

        app* first_eq_lhs = orig_hvar;
        
        app* first_eq_rhs_record = this->mk_record(first_locvars_vec, first_datavars_vec);

        app* first_eq_rhs_pt = this->mk_points_to_new(write_addr, first_eq_rhs_record);
        std::vector<app*> first_eq_rhs_uplus_args;
        first_eq_rhs_uplus_args.push_back(fresh_hvar);
        first_eq_rhs_uplus_args.push_back(first_eq_rhs_pt);
        app* first_eq_rhs = this->mk_uplus(2, first_eq_rhs_uplus_args);

        app_ref first_eq(this->th->get_context().mk_eq_atom(first_eq_lhs, first_eq_rhs), this->th->get_manager());

        app* second_eq_lhs = writed_hvar;
        std::vector<app*> second_locvars_vec = first_locvars_vec;
        std::vector<app*> second_datavars_vec = first_datavars_vec;

        if(is_write_loc) {
            second_locvars_vec[write_index] = write_item;
        } else {
            second_datavars_vec[write_index] = write_item;
        }

        app* second_eq_rhs_record = this->mk_record(second_locvars_vec, second_datavars_vec);

        app* second_eq_rhs_pt = this->mk_points_to_new(write_addr, second_eq_rhs_record);

        std::vector<app*> second_eq_rhs_uplus_args;
        second_eq_rhs_uplus_args.push_back(second_eq_rhs_pt);
        second_eq_rhs_uplus_args.push_back(fresh_hvar);
        app* second_eq_rhs = this->mk_uplus(2, second_eq_rhs_uplus_args);

        app_ref second_eq(this->th->get_context().mk_eq_atom(second_eq_lhs, second_eq_rhs), this->th->get_manager());
        app* final_result = this->th->get_manager().mk_and(first_eq, second_eq);
        this->th->get_context().internalize(final_result, false);
        return final_result;
        
    }

    app* slhv_syntax_maker::mk_addr_in_hterm(app* hterm, app* addr) {
        app* fresh_unrelated_h = this->mk_fresh_hvar();
        app* addr_data_fresh_l = this->mk_fresh_locvar();
        app* eq_lhs = hterm;
        std::vector<app*> rhs_uplus_args;
        app* rhs_pt = this->mk_points_to(addr, addr_data_fresh_l);
        rhs_uplus_args.push_back(fresh_unrelated_h);
        rhs_uplus_args.push_back(rhs_pt);
        app* eq_rhs_uplus = this->mk_uplus(2, rhs_uplus_args);

        app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs_uplus), this->th->get_manager());
        this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_addr_in_hterm_new(app* hterm, app* addr) {
        app* fresh_unrelated_h = this->mk_fresh_hvar();
        std::vector<app*> record_fresh_locvars;
        std::vector<app*> record_fresh_datavars;
        for(int i = 0; i < this->th->pt_locfield_num; i ++) {
            record_fresh_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < this->th->pt_datafield_num; i ++) {
            record_fresh_datavars.push_back(this->mk_fresh_datavar());
        }
        app* addr_pt_record = this->mk_record(record_fresh_locvars, record_fresh_datavars);

        app* rhs_pt = this->mk_points_to_new(addr, addr_pt_record);
        std::vector<app*> rhs_uplus_args;
        rhs_uplus_args.push_back(fresh_unrelated_h);
        rhs_uplus_args.push_back(rhs_pt);
        app* eq_lhs = hterm;
        app* eq_rhs_uplus = this->mk_uplus(2, rhs_uplus_args);
        app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs_uplus), this->th->get_manager());
        this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_addr_notin_hterm(app* hterm, app* addr) {
        app* fresh_whole_h = this->mk_fresh_hvar();
        app* fresh_data = this->mk_fresh_locvar();
        app* eq_lhs = fresh_whole_h;
        app* rhs_points_to = this->mk_points_to(addr, fresh_data);
        std::vector<app*> uplus_args;
        uplus_args.push_back(hterm);
        uplus_args.push_back(rhs_points_to);
        app* eq_rhs = this->mk_uplus(2, uplus_args);

        app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());
        this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_addr_notin_hterm_new(app* hterm, app* addr) {
        app* fresh_whole_h = this->mk_fresh_hvar();
        std::vector<app*> record_fresh_datavars;
        std::vector<app*> record_fresh_locvars;
        for(int i = 0; i < this->th->pt_locfield_num; i ++) {
            record_fresh_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < this->th->pt_datafield_num; i ++) {
            record_fresh_datavars.push_back(this->mk_fresh_datavar());
        }
        app* rhs_record = this->mk_record(record_fresh_locvars, record_fresh_datavars);
        app* rhs_points_to = this->mk_points_to_new(addr, rhs_record);
        app* eq_lhs = fresh_whole_h;
        std::vector<app*> uplus_args;
        uplus_args.push_back(hterm);
        uplus_args.push_back(rhs_points_to);
        app* eq_rhs = this->mk_uplus(2, uplus_args);
        app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());
        this->th->get_context().internalize(final_result, false);
        return final_result;
    }

   std::vector<std::vector<app*>> slhv_syntax_maker::mk_hterm_disequality(app* lhs_hterm, app* rhs_hterm) {
        #ifdef SLHV_DEBUG
        std::cout << "mk_hterm_disequality" << std::endl;
        #endif
        app* h = this->mk_fresh_hvar();
        app* h_prime = this->mk_fresh_hvar();
        app* ht1_hvar = this->mk_fresh_hvar();
        app* ht2_hvar = this->mk_fresh_hvar();
        app* x = this->mk_fresh_locvar();
        app* y = this->mk_fresh_locvar();
        app* z = this->mk_fresh_locvar();
        std::vector<std::vector<app*>> final_result;
        // the order of arugments of equality should not be changed
        app* ht1_to_hvar_eq = this->th->get_manager().mk_eq(ht1_hvar, lhs_hterm);
        app* ht2_to_hvar_eq = this->th->get_manager().mk_eq(ht2_hvar, rhs_hterm);
        this->th->get_context().internalize(ht1_to_hvar_eq, false);
        this->th->get_context().internalize(ht2_to_hvar_eq, false);


        // first disjunct
        app* first_conj_eq_lhs = ht1_hvar;
        std::vector<app*> first_conj_eq_rhs_uplus_args;
        app* first_eq_rhs_pt = this->mk_points_to(x, y);
        #ifdef SLHV_DEBUG
        std::cout << " uplus rhs: " << mk_pp(h, this->th->get_manager()) << " " << h->get_sort()->get_name() << std::endl;
        std::cout << " uplus rhs: " << mk_pp(first_eq_rhs_pt, this->th->get_manager()) << " " << h->get_sort()->get_name() <<std::endl;
        first_eq_rhs_pt->get_sort();
        #endif
        first_conj_eq_rhs_uplus_args.push_back(h);
        first_conj_eq_rhs_uplus_args.push_back(first_eq_rhs_pt);
        app* first_conj_eq_rhs = this->mk_uplus(first_conj_eq_rhs_uplus_args.size(), first_conj_eq_rhs_uplus_args);
        app_ref first_conj_eq(this->th->get_context().mk_eq_atom(first_conj_eq_lhs, first_conj_eq_rhs), this->th->get_manager());
        this->th->get_context().internalize(first_conj_eq, false);
        
        app* second_conj_eq_lhs = ht2_hvar;
        app* second_conj_eq_rhs_pt = this->mk_points_to(x, z);
        std::vector<app*> second_conj_eq_rhs_uplus_args;
        second_conj_eq_rhs_uplus_args.push_back(h_prime);
        second_conj_eq_rhs_uplus_args.push_back(second_conj_eq_rhs_pt);
        app* second_conj_eq_rhs = this->mk_uplus(second_conj_eq_rhs_uplus_args.size(), second_conj_eq_rhs_uplus_args);
        app_ref second_conj_eq(this->th->get_context().mk_eq_atom(second_conj_eq_lhs, second_conj_eq_rhs), this->th->get_manager());
        this->th->get_context().internalize(second_conj_eq, false);

        expr_ref_vector distinct_pair(this->th->get_manager());
        distinct_pair.push_back(y);
        distinct_pair.push_back(z);
        app* third_conj_diseq = this->th->get_manager().mk_distinct(2, distinct_pair.data());
        this->th->get_context().internalize(third_conj_diseq, false);


        std::vector<app*> first_disj;
        first_disj.push_back(first_conj_eq);
        first_disj.push_back(second_conj_eq);
        first_disj.push_back(third_conj_diseq);
        first_disj.push_back(ht1_to_hvar_eq);
        first_disj.push_back(ht2_to_hvar_eq);
        
        final_result.push_back(first_disj);

        // second disjunct
        #ifdef SLHV_DEBUG
        std::cout << "second disjunct" << std::endl;
        #endif
        app* x_in_ht1 = this->mk_addr_in_hterm(ht1_hvar, x);
        app* x_notin_ht2 = this->mk_addr_notin_hterm(ht2_hvar, x);
        std::vector<app*> second_disj;
        second_disj.push_back(x_in_ht1);
        second_disj.push_back(x_notin_ht2);
        second_disj.push_back(ht1_to_hvar_eq);
        second_disj.push_back(ht2_to_hvar_eq);
        this->th->get_context().internalize(x_in_ht1, false);
        this->th->get_context().internalize(x_notin_ht2, false);
        final_result.push_back(second_disj);

        // third_disjunct

        #ifdef SLHV_DEBUG
        std::cout << "third disjunct" << std::endl;
        #endif
        app* x_in_ht2 = this->mk_addr_in_hterm(ht2_hvar, x);
        app* x_notin_ht1 = this->mk_addr_notin_hterm(ht1_hvar, x);
        std::vector<app*> third_disj;
        third_disj.push_back(x_in_ht2);
        third_disj.push_back(x_notin_ht1);
        third_disj.push_back(ht1_to_hvar_eq);
        third_disj.push_back(ht2_to_hvar_eq);
        this->th->get_context().internalize(x_in_ht2, false);
        this->th->get_context().internalize(x_notin_ht1, false);
        final_result.push_back(third_disj);
        return final_result;
    }

    std::vector<std::vector<app*>> slhv_syntax_maker::mk_hterm_disequality_new(app* lhs, app* rhs) {
        std::vector<std::vector<app*>> final_result;

        #ifdef SLHV_DEBUG
        std::cout << "mk hterm disequality new" << std::endl;
        #endif

        app* ht1_hvar = this->mk_fresh_hvar();
        app* ht2_hvar = this->mk_fresh_hvar();

        app* ht1_to_hvar_eq = this->th->get_manager().mk_eq(ht1_hvar, lhs);
        app* ht2_to_hvar_eq = this->th->get_manager().mk_eq(ht2_hvar, rhs);
        this->th->get_context().internalize(ht1_to_hvar_eq, false);
        this->th->get_context().internalize(ht2_to_hvar_eq, false);
        // first disjunction batch
        app* h = this->mk_fresh_hvar();
        app* hp = this->mk_fresh_hvar();
        app* x = this->mk_fresh_locvar();

        std::vector<app*> ht1_pt_locvars;
        std::vector<app*> ht1_pt_datavars;
        std::vector<app*> ht2_pt_locvars;
        std::vector<app*> ht2_pt_datavars;

        for(int i = 0; i < this->th->pt_locfield_num; i ++) {
            ht1_pt_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < this->th->pt_datafield_num; i ++) {
            ht1_pt_datavars.push_back(this->mk_fresh_datavar());
        }
        for(int i = 0; i < this->th->pt_locfield_num; i ++) {
            ht2_pt_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < this->th->pt_datafield_num; i ++) {
            ht2_pt_datavars.push_back(this->mk_fresh_datavar());
        }

        app* ht1_eq_lhs = ht1_hvar;
        app* ht2_eq_lhs = ht2_hvar;

        app* ht1_eq_rhs_record = this->mk_record(ht1_pt_locvars, ht1_pt_datavars);
        app* ht2_eq_rhs_record = this->mk_record(ht2_pt_locvars, ht2_pt_datavars);

        app* ht1_eq_rhs_pt = this->mk_points_to_new(x, ht1_eq_rhs_record);
        app* ht2_eq_rhs_pt = this->mk_points_to_new(x, ht2_eq_rhs_record);

        std::vector<app*> ht1_eq_rhs_uplus_args;
        std::vector<app*> ht2_eq_rhs_uplus_args;

        ht1_eq_rhs_uplus_args.push_back(h);
        ht1_eq_rhs_uplus_args.push_back(ht1_eq_rhs_pt);

        ht2_eq_rhs_uplus_args.push_back(hp);
        ht2_eq_rhs_uplus_args.push_back(ht2_eq_rhs_pt);

        app* ht1_eq_rhs = this->mk_uplus(2, ht1_eq_rhs_uplus_args);
        app* ht2_eq_rhs = this->mk_uplus(2, ht2_eq_rhs_uplus_args);

        app_ref ht1_eq(this->th->get_context().mk_eq_atom(ht1_eq_lhs, ht1_eq_rhs), this->th->get_manager());
        app_ref ht2_eq(this->th->get_context().mk_eq_atom(ht2_eq_lhs, ht2_eq_rhs), this->th->get_manager());

        std::vector<expr*> one_field_distinct;
        for(int i = 0; i < this->th->pt_locfield_num; i ++) {
            expr_ref_vector vec(this->th->get_manager());
            vec.push_back(to_expr(ht1_pt_locvars[i]));
            vec.push_back(to_expr(ht2_pt_locvars[i]));
            app* e = this->th->get_manager().mk_distinct(vec.size(), vec.data());
            one_field_distinct.push_back(e);
        }
        for(int i = 0; i < this->th->pt_datafield_num; i ++) {
            expr_ref_vector vec(this->th->get_manager());
            vec.push_back(to_expr(ht1_pt_datavars[i]));
            vec.push_back(to_expr(ht2_pt_datavars[i]));
            app* e = this->th->get_manager().mk_distinct(vec.size(), vec.data());
            one_field_distinct.push_back(e);
        }
        for(expr* e : one_field_distinct) {
            std::vector<app*> first_disj;
            first_disj.push_back(ht1_eq);
            first_disj.push_back(ht2_eq);
            first_disj.push_back(to_app(e));
            first_disj.push_back(ht1_to_hvar_eq);
            first_disj.push_back(ht2_to_hvar_eq);
            this->th->get_context().internalize(ht1_eq, false);
            this->th->get_context().internalize(ht2_eq, false);
            final_result.push_back(first_disj);
        } 
        // second disjunct
        #ifdef SLHV_DEBUG
        std::cout << "second disjunct" << std::endl;
        #endif
        app* x_in_ht1 = this->mk_addr_in_hterm(ht1_hvar, x);
        app* x_notin_ht2 = this->mk_addr_notin_hterm(ht2_hvar, x);
        std::vector<app*> second_disj;
        second_disj.push_back(x_in_ht1);
        second_disj.push_back(x_notin_ht2);
        second_disj.push_back(ht1_to_hvar_eq);
        second_disj.push_back(ht2_to_hvar_eq);
        this->th->get_context().internalize(x_in_ht1, false);
        this->th->get_context().internalize(x_notin_ht2, false);
        final_result.push_back(second_disj);

        // third_disjunct

        #ifdef SLHV_DEBUG
        std::cout << "third disjunct" << std::endl;
        #endif
        app* x_in_ht2 = this->mk_addr_in_hterm(ht2_hvar, x);
        app* x_notin_ht1 = this->mk_addr_notin_hterm(ht1_hvar, x);
        std::vector<app*> third_disj;
        third_disj.push_back(x_in_ht2);
        third_disj.push_back(x_notin_ht1);
        third_disj.push_back(ht1_to_hvar_eq);
        third_disj.push_back(ht2_to_hvar_eq);
        this->th->get_context().internalize(x_in_ht2, false);
        this->th->get_context().internalize(x_notin_ht1, false);
        final_result.push_back(third_disj);
        return final_result;
    }

    app* slhv_syntax_maker::mk_uplus(int num_arg, std::vector<app*> hterm_args) {
        SASSERT(num_arg == hterm_args.size());
        for(app* t : hterm_args) {
            SASSERT(this->th->is_heapterm(t));
        }
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : hterm_args) {
            args_vec.push_back(arg);
        }
        sort* e_ref_sort = this->slhv_decl_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        sort_ref_vector sorts_vec(this->th->get_manager());
        for(int i = 0; i < num_arg; i ++) {
            sorts_vec.push_back(e_ref_sort);
        }
        // sort* e_ref_sort = this->th->get_manager().mk_sort(symbol(INTHEAP_SORT_STR), sort_info(this->th->get_id(), INTHEAP_SORT));
        func_decl* uplus_decl = this->slhv_decl_plug->mk_func_decl(OP_HEAP_DISJUNION, 0, nullptr, num_arg, sorts_vec.data(), e_ref_sort);
        app* result = this->th->get_manager().mk_app(uplus_decl, args_vec.data());
        return result;
    }

    app* slhv_syntax_maker::mk_points_to(app* addr_loc, app* data_loc) {
        SASSERT(this->th->is_locterm(addr_loc) && this->th->is_locterm(data_loc));
        std::vector<app*> args = {addr_loc, data_loc};
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : args) {
            args_vec.push_back(arg);
        }
        sort* loc_sort = this->slhv_decl_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        sort_ref_vector sorts_vec(this->th->get_manager()); 
        sorts_vec.push_back(loc_sort);
        sorts_vec.push_back(loc_sort);
        sort* e_ref_sort = this->slhv_decl_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        // sort* e_ref_sort = this->th->get_manager().mk_sort(symbol(INTHEAP_SORT_STR), sort_info(this->th->get_id(), INTHEAP_SORT));
        func_decl* pt_decl = this->slhv_decl_plug->mk_func_decl(OP_POINTS_TO, 0, nullptr, 2, sorts_vec.data(), e_ref_sort);
        app* result = this->th->get_manager().mk_app(pt_decl, args_vec.data());
    
        return result;
    }


    app* slhv_syntax_maker::mk_points_to_new(app* addr_loc, app* record_loc) {
        SASSERT(this->th->is_locterm(addr_loc));
        SASSERT(this->th->is_recordterm(record_loc));
        std::vector<app*> args = {addr_loc, record_loc};
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : args) {
            args_vec.push_back(arg);
        }
        sort* loc_sort = this->slhv_decl_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        sort* record_sort = this->slhv_decl_plug->Pt_R_decl->get_range();
        sort_ref_vector sorts_vec(this->th->get_manager()); 
        sorts_vec.push_back(loc_sort);
        sorts_vec.push_back(record_sort);
        sort* e_ref_sort = this->slhv_decl_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        func_decl* pt_decl = this->slhv_decl_plug->mk_func_decl(OP_POINTS_TO, 0, nullptr, 2, sorts_vec.data(), e_ref_sort);
        app* result = this->th->get_manager().mk_app(pt_decl, args_vec);
        return result;
    }

    app* slhv_syntax_maker::mk_record(std::vector<app*> locvars, std::vector<app*> datavars) {
        SASSERT(locvars.size() == this->th->pt_locfield_num);
        SASSERT(datavars.size() == this->th->pt_datafield_num);
        std::vector<app*> args;
        sort* loc_sort = this->slhv_decl_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        sort* data_sort = this->th->get_manager().mk_sort(arith_family_id, INT_SORT);
        sort_ref_vector field_sorts(this->th->get_manager());
        for(app* loc : locvars) {
            args.push_back(loc);
            field_sorts.push_back(loc_sort);
        }
        for(app* data : datavars) {
            args.push_back(data);
            field_sorts.push_back(data_sort);
        }
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : args) {
            args_vec.push_back(arg);
        }
        func_decl* record_decl = this->slhv_decl_plug->Pt_R_decl;
        app* result = this->th->get_manager().mk_app(record_decl, args_vec);
        return result;
    }
 
    slhv_fresh_var_maker::slhv_fresh_var_maker(theory_slhv* t) {
        this->th = t;
        slhv_decl_plugin* slhv_plugin = (slhv_decl_plugin*)this->th->get_manager().get_plugin(this->th->get_id());
        this->fe_plug = slhv_plugin;
        this->reset();
    }

    void slhv_fresh_var_maker::reset() {
        this->curr_locvar_id = 0;
        this->curr_hvar_id = 0;
        this->curr_datavar_id = 0;
        locvar_map.clear();
        hvar_map.clear();
    }

    app* slhv_fresh_var_maker::mk_fresh_hvar() {
        std::string name = "f_th_hvar" + std::to_string(this->curr_hvar_id);
        sort* range_sort = this->fe_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        unsigned num_args = 0;
        app* fresh_hvar = this->th->get_manager().mk_app(this->fe_plug->mk_const_hvar(symbol(name), range_sort, 0, nullptr), num_args, nullptr);
        this->hvar_map[curr_hvar_id] = fresh_hvar;
        curr_hvar_id ++;
        return fresh_hvar;
    }

    app* slhv_fresh_var_maker::mk_fresh_locvar() {
        std::string name = "f_th_locvar" + std::to_string(this->curr_locvar_id);
        sort* range_sort = this->fe_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        unsigned num_args = 0;
        app* fresh_locvar = this->th->get_manager().mk_app(this->fe_plug->mk_const_locvar(symbol(name), range_sort, 0, nullptr), num_args, nullptr);
        this->locvar_map[curr_locvar_id] = fresh_locvar;
        curr_locvar_id ++;
        return fresh_locvar;
    }

    app* slhv_fresh_var_maker::mk_fresh_datavar() {
        std::string name = "f_th_datavar" + std::to_string(this->curr_datavar_id);
        family_id arith_family_id = this->th->get_manager().mk_family_id("arith");
        sort* range_sort = this->th->get_manager().mk_sort(arith_family_id, INT_SORT);
        unsigned num_args = 0;
        arith_decl_plugin* arith_plug = (arith_decl_plugin*)this->th->get_manager().get_plugin(arith_family_id);
        app* fresh_datavar = this->th->get_manager().mk_app(
            symbol(name), 0, nullptr, range_sort
        );
        curr_datavar_id ++;
        return fresh_datavar;
    }
}