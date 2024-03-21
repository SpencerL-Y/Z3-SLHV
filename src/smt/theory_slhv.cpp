#include "ast/ast_ll_pp.h"
#include "ast/slhv_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "smt/smt_context.h"
#include "smt/theory_slhv.h"
#include "smt/smt_solver.h"
#include "model/numeral_factory.h"
#include "model/locvar_factory.h"
#include "model/model_core.h"
#include "model/model_smt2_pp.h"
#include "smt/smt_model_generator.h"
#include "util/params.h"
#include <ostream>
#include <iostream>
#include <bitset>
namespace smt {

    // theory-slhv --------------------------------
    theory_slhv::theory_slhv(context& ctx) : theory(ctx, ctx.get_manager().mk_family_id("slhv")) {
        #ifdef SLHV_PRINT
        std::cout << "SLHV theory plugin created" << std::endl;
        #endif
        this->mem_mng = alloc(mem_management, this);
        this->msw = alloc(memsafe_wrapper, this);
        this->syntax_maker = alloc(slhv_syntax_maker, this, this->msw);

        this->global_emp = nullptr;
        this->global_nil = nullptr;
        this->reset_outside_configs();
    }

    bool theory_slhv::curr_locvars_contain_nil() {
        for(app* locvar : this->curr_locvars) {
            if(this->is_nil(locvar)) {
                return true;
            }
        }
        return false;
    }


    bool theory_slhv::locvars_contain_nil_disj() {
        for(app* locvar : this->locvars_disj) {
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

    bool theory_slhv::hvars_contain_emp_disj() {
        for(app* hvar : this->hvars_disj) {
            if(this->is_emp(hvar)) {
                return true;
            }
        }
        return false;
    }

    
    theory *theory_slhv::mk_fresh(context * new_ctx)  {
        #ifdef SLHV_PRINT
            std::cout << "slhv mk_fresh" << std::endl;
        #endif
        return alloc(theory_slhv, *new_ctx);
    }

    bool theory_slhv::internalize_atom(app * atom, bool gate_ctx)  {
        #ifdef SLHV_PRINT
            std::cout << "slhv internalize atom" << std::endl;
        #endif
        if(this->is_subh(atom) || this->is_disjh(atom)) {
            // do nothing since these are only auxillary assertions
            return false;
        }
        return true;
    }

    bool theory_slhv::internalize_term(app * term)  {
        #ifdef SLHV_PRINT
            std::cout << "slhv internalize term" << std::endl;
        #endif
        if(!is_uplus(term) && !is_points_to(term) && !is_locvar(term) && !is_hvar(term) && !is_nil(term) && !is_emp(term) && !is_locadd(term) && !is_readdata(term) && !is_readloc(term) && !is_writedata(term) && !is_writeloc(term) && !is_loc2int(term) && !is_int2loc(term)) {
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
            #ifdef SLHV_PRINT
            std::cout << "term name: " << term->get_name() << " is_points_to: " << is_points_to(term) << " num args: " << term->get_num_args() << std::endl;
            #endif
        } else if(is_uplus(term)) {
            SASSERT(term->get_num_args() >= 2);
            SASSERT(get_th_var(term) != -1);
            #ifdef SLHV_PRINT
            std::cout << "term name: " << term->get_name() << " is_uplus: " << is_uplus(term) << " num args: " << term->get_num_args() << std::endl;
            #endif
        } else if(is_locadd(term)) {
            SASSERT(term->get_num_args() == 2);
            enode* arg0_node = ctx.get_enode(term->get_arg(0));
            enode* arg1_node = ctx.get_enode(term->get_arg(1));
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
            #ifdef SLHV_PRINT
            std::cout << "mk_theory_var for " << mk_ismt2_pp(term, m) << std::endl;
            #endif
            mk_var(e);
            #ifdef SLHV_PRINT
            std::cout << "theory var made: " << get_th_var(e) << std::endl;
            #endif
        }
        if(m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        return true;
    }

    void theory_slhv::new_eq_eh(theory_var v1, theory_var v2)  {
        #ifdef SLHV_PRINT
            std::cout << "slhv new eq eh" << std::endl;
        #endif
    }

    void theory_slhv::new_diseq_eh(theory_var v1, theory_var v2)  {
        #ifdef SLHV_PRINT
            std::cout << "slhv internalize term" << std::endl;
        #endif

    }

    void theory_slhv::display(std::ostream & out) const {

    }

    void theory_slhv::propagate() {
        #ifdef SLHV_PRINT
        std::cout << "slhv propagate" << std::endl;
        #endif
    }

    
    std::set<expr*> theory_slhv::extract_unsat_core_booleans(expr* e) {
        std::set<expr*> result;
        app* apped_expr = to_app(e);
        if(apped_expr->get_sort() == this->get_manager().mk_bool_sort() &&
           apped_expr->get_num_args() == 0 && !this->get_manager().is_false(apped_expr) && !this->get_manager().is_true(apped_expr)) {
            result.insert(apped_expr);
        } else {
            for(int i = 0; i < apped_expr->get_num_args(); i ++) {
                result = slhv_util::setUnion(result, this->extract_unsat_core_booleans(apped_expr->get_arg(i)));
            }
        }
        return result;
    }

    std::set<expr*> theory_slhv::recover_unsat_core(formula_encoder* fec,  expr_ref_vector unsat_core){
        std::set<expr*> result;
        std::set<std::pair<int, int>> related_sh_pairs;
        std::set<std::pair<int, int>> related_dj_pairs;

        // recover ld constraints
        for(expr* e : unsat_core) {
            // bool is_ld = false;
            // for(ld_recov_node* ldn : this->ld_recovery) {
            //     if(ldn->translated_formula == e) {
            //         result.insert(ldn->original_formula);
            //         is_ld = true;
            //         break;
            //     }
            // }
            // if(is_ld) {continue;}
            std::set<expr*> boolvars = this->extract_unsat_core_booleans(e);
            for(expr* boolvar : boolvars) {
                auto result = fec->get_boolvar_id_type(to_app(boolvar));
                if(result.first.first != -1) {
                    if(result.second) {
                        related_sh_pairs.insert(result.first);
                    } else {
                        related_dj_pairs.insert(result.first);
                    }
                }
            }
        }
        // set infer graph conflict
        for(auto p : related_sh_pairs) {
            if(this->infer_graph->contain_sh_node(p)) {
                this->infer_graph->set_sh_unsat_node(p);
            } else {
                for(auto c2hts : this->constraint2hts) {
                    for(heap_term* ht : c2hts.second) {
                        if(fec->get_index2ht()[p.first] == ht || 
                           fec->get_index2ht()[p.second] == ht ||
                           fec->get_index2ht()[p.first]->is_subhterm_of(ht) || 
                           fec->get_index2ht()[p.second]->is_subhterm_of(ht)) {
                            result.insert(c2hts.first);
                        }
                    }
                }
            }
        }
        for(auto p : related_dj_pairs) {
            if(this->infer_graph->contain_dj_node(p)) {
                this->infer_graph->set_dj_unsat_node(p);
            } else {
                for(auto c2hts : this->constraint2hts) {
                    for(heap_term* ht : c2hts.second) {
                        if(fec->get_index2ht()[p.first] == ht || 
                           fec->get_index2ht()[p.second] == ht ||
                           fec->get_index2ht()[p.first]->is_subhterm_of(ht) || 
                           fec->get_index2ht()[p.second]->is_subhterm_of(ht)) {
                            result.insert(c2hts.first);
                        }
                    }
                }
            }
        }
        std::set<expr*> inf_graph_unsatcore = this->infer_graph->compute_unsat_core_expressions();
        result = slhv_util::setUnion(result, inf_graph_unsatcore);
        for(auto ld_recov : this->ld_recovery) {
            result.insert(ld_recov->original_formula);
        }
        return result;
    }

    void theory_slhv::set_conflict_slhv() {
        literal_vector unsat_core;
        for(expr* e : this->curr_outside_assignments) {
            literal expr_lit = this->ctx.get_literal(e);
            unsat_core.push_back(expr_lit);
        }
        #ifdef SLHV_PRINT
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

     void theory_slhv::set_conflict_slhv_empty() {
        literal_vector unsat_core;
        ctx.set_conflict(
            ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx, unsat_core.size(), unsat_core.data(), 0, nullptr, 0, nullptr
            ))
        );
    }


    void theory_slhv::set_conflict_slhv(std::vector<expr*> outside_unsat_core) {
        literal_vector unsat_core = this->compute_current_unsat_core(outside_unsat_core);
        #ifdef SLHV_PRINT
        std::cout << "conflict unsat core literals ====== " << std::endl;
        for(literal l : unsat_core) {
            std::cout  << l << std::endl;
        }
        std::cout << "conflict unsat core exprs ====== " << std::endl;
        for(expr* e : this->outside_unsat_core) {
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
        
    void theory_slhv::set_conflict_slhv(inference_graph* inf_graph) {
        literal_vector unsat_core = this->compute_unsat_core_by_inference_graph(this->infer_graph);
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "conflict unsat core literals ====== " << std::endl;
        for(literal l : unsat_core) {
            std::cout  << l << std::endl;
        }
        std::cout << "conflict unsat core exprs ====== " << std::endl;
        for(expr* e : this->infer_graph->unsat_core) {
            std::cout << mk_pp(e, this->m) << std::endl;
        }

        #endif
        if(this->infer_graph->unsat_core.size() > 0) {
            ctx.set_conflict(
                ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx, unsat_core.size(), unsat_core.data(), 0, nullptr, 0, nullptr
                ))
            );
        } else {
            this->set_conflict_slhv();
        }
    }



    literal_vector theory_slhv::compute_current_unsat_core(std::vector<expr*> outside_unsat_core) {
        expr_ref_vector original(this->get_manager());
        for(expr* e : outside_unsat_core) {
            original.push_back(e);
        }
        expr_ref_vector disj_removed(this->get_manager());
        // this might be buggy
        for(expr* e : original) {
            if(to_app(e)->is_app_of(basic_family_id, OP_OR)) {
                continue;
            }
            disj_removed.push_back(e);
        }
        std::vector<expr*> disj_heapneg_removed;
        #ifdef FRONTEND_HAS_HEAP_NEQ
        disj_heapneg_removed = outside_unsat_core;
        #else
        std::vector<expr_ref_vector> temp_result = this->remove_heap_equality_negation_in_assignments(disj_removed);
        for(expr_ref_vector v : temp_result) {
            for(expr* e : v) {
                disj_heapneg_removed.push_back(e);
            }
        }
        #endif
        
        literal_vector unsat_core;
        for(expr* e : disj_heapneg_removed) {
            literal expr_lit = this->ctx.get_literal(e);
            unsat_core.push_back(expr_lit);
        }
        return unsat_core;
    }


    literal_vector theory_slhv::compute_unsat_core_by_inference_graph(inference_graph* inf_graph) {
        std::set<expr*> unsat_core_exprs = inf_graph->compute_unsat_core_expressions();
        literal_vector unsat_core;
        for(expr* e : unsat_core_exprs) {
            literal expr_lit = this->ctx.get_literal(e);
            unsat_core.push_back(expr_lit);
        }
        return unsat_core;
    }

    bool theory_slhv::is_arith_formula(app* l) {
        if(l->get_num_args() == 0) {
            if(l->get_family_id() == arith_family_id) {
                return true; 
            } else {
                return false;
            }
        } else  {
            bool result = true;
            for(int i = 0; i < l->get_num_args(); i ++) {
                bool curr_result = this->is_arith_formula(to_app(l->get_arg(i)));
                result = result && curr_result;
                if(!result) {
                    return result;
                }
            }
            return result;
        } 
    }

    bool theory_slhv::is_not_heap_or_loc_formula(app* l) {
        if(l->get_num_args() == 0) {
            if(l->get_family_id() == this->get_family_id()) {
                return false;
            } else {
                return true;
            }
        } else {
            bool result = true;
            for(int i = 0; i < l->get_num_args(); i ++ ){
                bool curr_result = this->is_not_heap_or_loc_formula(to_app(l->get_arg(i)));
                result = result && curr_result;
                if(!result) {
                    return false;
                }
            }
            return result;
        }
    }

    bool theory_slhv::final_check() {
        // return final_check_using_CDCL();
        return final_check_using_DISJ();
    }

    bool theory_slhv::final_check_using_DISJ() {
            
        this->reset_outside_configs();
        ptr_vector<expr> assertions;
        this->ctx.get_assertions(assertions);
        #ifdef SLHV_HTR_DEBUG
        std::cout << "XXXXXXXXXXXXXXXXXXXX slhv final_check() XXXXXXXXXXXXXXXXXXXX" << std::endl;
        std::cout << "================= current outside assertions ==============" << std::endl;
        for(expr* e : assertions) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
            std::cout << "----" << std::endl;
        }
        std::cout << "===================== current outside assertions end ==================" << std::endl;  
        #endif
        for(expr* e : assertions) {
            this->outside_assertions_disj.push_back(to_app(e));
        }
        
        std::set<expr*> inf_creation_expr_set;
        for(auto e : this->outside_assertions_disj) {
            inf_creation_expr_set.insert(e);
        }
        inference_graph* inf_graph = alloc(inference_graph, this, inf_creation_expr_set);
        this->infer_graph = inf_graph;
        this->mem_mng->set_inf_graph(this->infer_graph);

        std::vector<app*> refined_assertions;
        for(expr* e : assertions) {
            expr* eliminated_double_uplus = this->eliminate_uplus_in_uplus_for_assertion_disj(e);
            expr* converted_to_nnf_assertion = this->convert_to_nnf_recursive(eliminated_double_uplus);
            refined_assertions.push_back(to_app(converted_to_nnf_assertion));
            inf_graph->add_refined_assignment_node(converted_to_nnf_assertion, e);
        }
        #ifdef SLHV_HTR_DEBUG
        std::cout << "================= current refined assignment ==============" << std::endl;
        for(expr* e : refined_assertions) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
        }
        std::cout << "===================== current refined assignment end ==================" << std::endl;  
        #endif
        this->refined_asssertions_disj = refined_assertions;
        // set slhv syntax plugin
        this->slhv_plug = (slhv_decl_plugin*) this->get_manager().get_plugin(this->get_id());
        SASSERT(this->slhv_plug->pt_record_map.size() > 0);

        std::set<expr*> inga;
        for(expr* e : this->refined_asssertions_disj) {
            if(!this->contain_disjunction(to_app(e))) {
                #ifdef DISJ_DEBUG
                std::cout << "ref assertion without disj: " << mk_ismt2_pp(e, this->m) << std::endl;
                #endif
                this->inf_graph_assertions_disj.insert(to_app(e));
                inga.insert(e);
            }
        }
        // inference_graph* inf_graph = alloc(inference_graph, this, inga);
        // this->infer_graph = inf_graph;

        this->preprocessing_disj();
        auto extracted_ht_result = this->extract_all_hterms_disj();
        std::set<heap_term*> all_hterms = extracted_ht_result->all_hterms;
        this->inf_graph_eq_pairs_hterms_disj = extracted_ht_result->eq_pair_hterms;
        this->inf_graph_subh_pair_hterms_disj = extracted_ht_result->sub_pair_hterms;
        this->inf_graph_disjh_pair_hterms_disj = extracted_ht_result->disj_pair_hterms;
        #ifdef DISJ_DEBUG
        std::cout << "all heap constraints: " << std::endl;
        for(app* hc : refined_heap_subassertions) {
            std::cout << mk_ismt2_pp(hc, this->m) << std::endl;
        }
        std::cout << "all hterms size: " << this->atomic_hterms_disj.size() << std::endl;
        std::cout << "all hterms: " << std::endl;
        for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
            std::cout << mk_ismt2_pp(this->atomic_hterms_disj[i], this->m) << "\t";
        }
        std::cout << std::endl;

        for(heap_term* ht : all_hterms) {
            ht->print_ht();
            ht->print(std::cout);
        }
        #endif
        for(heap_term* ht : all_hterms) {
            this->mem_mng->push_ht_ptr(ht);
        }
        formula_encoder* fec = alloc(formula_encoder, this, all_hterms);
        this->mem_mng->push_fec_ptr(fec);   

        fec->print_statistics();
        // if(true){
        if(fec->get_unsat_found()) {
            this->set_conflict_slhv();

            this->mem_mng->dealloc_all();
            return false;
        }
        std::set<expr*> encoded_formulas = fec->encode_for_disj();


        params_ref final_solver_param = params_ref();
        solver* final_solver = mk_smt_solver(this->m, final_solver_param, symbol("QF_LIA"));
        final_solver->inc_ref();

        for(expr* e: encoded_formulas) {
            if(e == nullptr) {
                // std::cout << "NULL PTR encoded" << std::endl;
            }
            final_solver->assert_expr(e);
        }
        std::cout << "lia assertion size: " << encoded_formulas.size() << std::endl;
        lbool final_result = final_solver->check_sat();
        std::cout << "XXXXXXXXXXXXXXXXX translated constraint result XXXXXXXXXXXXXXXXXXX" << std::endl;
        if(final_result == l_true) {
            #ifdef SOLVING_INFO
            std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET SAT XXXXXXXXXXXXXXXXXXXX" << std::endl;
            std::cout << " translated SAT " << std::endl;
            #endif
            // // print current refined assignment to file
            // std::ofstream output2file("./outmodel.txt", std::ios::out);
            // output2file << "SAT" << std::endl;
            // output2file << "ORIGINAL FORMULA XXXXXX" << std::endl;
            // for(expr* e : refined_assignments) {
            //     output2file << mk_ismt2_pp(e, this->m) << std::endl;
            // }   
            // output2file << "ELIMINATED FORMULA XXXXXX" << std::endl;    
            // output2file << "heap constraints ========== " << std::endl;
            // for(expr* e : heap_cnstr_assignments) {
            //     output2file << mk_ismt2_pp(e, this->m) << std::endl;
            // } 
            // output2file << "numeral constraints ========== " << std::endl;
            // for(expr* e : numeral_cnstr_assignments) {
            //     output2file << mk_ismt2_pp(e, this->m) << std::endl;
            // } 
            // output2file << "MODEL XXXXXX " << std::endl;

            std::map<std::string, expr*> name2val;
            model_ref md;
            final_solver->get_model(md);
            std::cout << "translated model: " << std::endl;
            // model_smt2_pp(std::cout, this->m, *md, 0);
            model_core& mdc = *md;
            for(int i = 0; i < mdc.get_num_constants(); i ++) {
                expr_ref temp_val(this->m);
                mdc.eval(mdc.get_constant(i), temp_val);
                // #ifdef SLHV_PRINT
                std::cout << " constant " << i << " " << mdc.get_constant(i)->get_name() << std::endl;
                std::cout << "eval: " << mk_ismt2_pp(temp_val, this->m) << std::endl; 
                // #endif
                // output2file << " constant " << i << " " << mdc.get_constant(i)->get_name() << std::endl;
                // output2file << "eval: " << mk_ismt2_pp(temp_val, this->m) << std::endl; 
                name2val[mdc.get_constant(i)->get_name().str()] = temp_val.get(); 
            }
            std::set<std::string> true_var_names;
            std::map<std::string, int> loc_data_var2val;
            for(auto key_val_p : name2val) {
                if(key_val_p.second->get_sort()->get_name() == "Bool") {
                    if(this->m.is_true(key_val_p.second)) {
                        true_var_names.insert(key_val_p.first);
                    } else if(this->m.is_false(key_val_p.second)) { 
                    } else {
                        SASSERT(false);
                    }

                } else {
                    SASSERT(key_val_p.second->get_sort()->get_name() == "Int");
                    auto param = to_app(key_val_p.second)->get_parameter(0);
                    std::cout << "int val for " << key_val_p.first << " " << " val " << param.get_rational().get_int64()<< std::endl;
                    std::cout << std::endl; 
                    std::vector<std::string> extracted_names = slhv_util::str_split(key_val_p.first, "_intvar");
                    for(std::string n : extracted_names) {
                        std::cout << n << std::endl;
                    }
                    loc_data_var2val[extracted_names[0]] =  param.get_rational().get_int64();
                }
            }
            std::set<atoms_subsumption*> atoms_subs = this->parse_and_collect_subsumption(fec, true_var_names);
            for(atoms_subsumption* sub : atoms_subs) {
                this->mem_mng->push_at_ptr(sub);
            }
            // record model information collected.
            this->model_subsume_info = atoms_subs;
            this->model_loc_data_var_val_info = loc_data_var2val;
            std::cout << "model info recorded: " << std::endl;
            // output2file << "model info recorded: " << std::endl;
            std::cout << "model subsume info size: " << this->model_subsume_info.size() << std::endl;
            // output2file << "model subsume info size: " << this->model_subsume_info.size() << std::endl; 
            for(atoms_subsumption* ats : this->model_subsume_info) {
                std::cout << "------- main" << std::endl;
                // output2file << "------- main" << std::endl;
                ats->get_main_heap_term()->print_ht();
                // ats->get_main_heap_term()->print_ht2file(output2file);
                std::cout << "------- subs" << std::endl;
                // output2file << "------- subs" << std::endl;
                for(heap_term* h : ats->get_pt_atoms()) {
                    h->print_ht();
                    // h->print_ht2file(output2file);
                }
            }
            std::cout << "locvar vals: " << std::endl;
            // output2file << "locvar vals: " << std::endl;
            for(auto r : this->model_loc_data_var_val_info) {
                std::cout << r.first << " " << r.second << std::endl;
                // output2file << r.first << " " << r.second << std::endl;
            }
            for(atoms_subsumption* sbs : this->model_subsume_info) {
                if(sbs->get_main_heap_term()->is_atom_hvar()) {
                    app* hvar_app = sbs->get_main_heap_term()->get_atoms()[0];
                    SASSERT(this->hvar2ptset.find(hvar_app) == this->hvar2ptset.end());
                    std::set<app*> pts_subsumed;
                    for(heap_term* pt_ht : sbs->get_pt_atoms()) {
                        pts_subsumed.insert(pt_ht->get_atoms()[0]);
                    }
                    this->hvar2ptset[hvar_app] = pts_subsumed;
                }
            }
            std::cout << "free heap vars:" << std::endl;
            // output2file << "free heap vars: " << std::endl;
            for(app* hv : this->curr_hvars) {
                if(this->hvar2ptset.find(hv) == this->hvar2ptset.end()) {
                    std::cout << "emp hvar: " << hv->get_name() << std::endl;
                    // output2file << "emp hvar: " << hv->get_name() << std::endl;
                }
            }
            final_solver->dec_ref();
            this->mem_mng->dealloc_all();
            return true;
        } else if(final_result == l_false) { 
        std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET UNSAT XXXXXXXXXXXXXXXXXXXX" << std::endl;
            SASSERT(final_solver->get_manager() == this->get_manager());
            this->set_conflict_slhv();

            final_solver->dec_ref();
            this->mem_mng->dealloc_all();
            return false;
        } else {    
            std::cout << " translated UNKNOWN " << std::endl;
            SASSERT(false);
            int* a = nullptr;
            *a = 10;
        }

        return false;
    }

    bool theory_slhv::final_check_using_CDCL() {
        
        this->reset_outside_configs();
        // obtain outside assignments
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);

        // inference graph intiailization
        std::set<expr*> initial_assignments;
        for(expr* e : assignments) {
            initial_assignments.insert(e);
        }
        inference_graph* inf_graph = alloc(inference_graph, this, initial_assignments);
        this->infer_graph = inf_graph;
        this->mem_mng->set_inf_graph(this->infer_graph);

        // print outside assignments
        #ifdef SOLVING_INFO
        std::cout << "XXXXXXXXXXXXXXXXXXXX slhv final_check() XXXXXXXXXXXXXXXXXXXX" << std::endl;
        std::cout << "================= current outside assignment ==============" << std::endl;
        for(expr* e : assignments) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
        }
        std::cout << "===================== current outside assignment end ==================" << std::endl;  
        #endif
        
        // eliminate outside assignments that are of the form (not (or ....))
        expr_ref_vector refined_assignments(this->m);
        for(expr* e : assignments) {
            std::vector<expr*> refined_e = this->eliminate_not_or_assignments(e);
            if(refined_e.size() == 1) {
                expr* no_uplus_uplus_e = this->eliminate_uplus_in_uplus_for_assignments(refined_e[0]);
                refined_assignments.push_back(no_uplus_uplus_e);
                // inference graph update
                this->infer_graph->add_refined_assignment_node(no_uplus_uplus_e, e);
            } else {
                for(expr* re : refined_e) {
                    // this->ctx.internalize(re, false);
                    bool same_e = false;
                    for(expr* exists_e : refined_assignments) {
                        if(exists_e != re) {
                            same_e = true;
                            break;
                        }
                    }
                    if(!same_e) {
                        expr* no_uplus_uplus_e = this->eliminate_uplus_in_uplus_for_assignments(re);
                        refined_assignments.push_back(no_uplus_uplus_e);
                        // inference graph update
                        this->infer_graph->add_refined_assignment_node(no_uplus_uplus_e, e);
                    }
                }
            }
        }
        // eliminate outside assignments that are of the form (uplus (uplus ..)..)
        // print refined assignments
        #ifdef SOLVING_INFO
        std::cout << "================= current refined assignment ==============" << std::endl;
        for(expr* e : refined_assignments) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
        }
        std::cout << "===================== current refined assignment end ==================" << std::endl;  
        #endif

        // set slhv syntax plugin
        this->slhv_plug = (slhv_decl_plugin*) this->get_manager().get_plugin(this->get_id());
        SASSERT(this->slhv_plug->pt_record_map.size() > 0);
        // print records in plugin
        #ifdef SLHV_PRINT
        for(auto item : this->slhv_plug->pt_record_map) {
            std::cout << "record type name: " << item.first << std::endl;
            item.second->print(std::cout);
        }
        #endif

        #ifdef FRONTEND_HAS_HEAP_NEQ
        //  enumerate all possible situations for negation imposed on hterm equalities
        std::vector<expr_ref_vector> elim_enums = this->eliminate_heap_equality_negation_in_assignments(refined_assignments);
        #else
        std::vector<expr_ref_vector> elim_enums = this->remove_heap_equality_negation_in_assignments(refined_assignments);
        #endif

        #ifdef SLHV_PRINT
        std::cout << "number of assignments after negations elimination: " << elim_enums.size() << std::endl;
        #endif
        
        expr_ref_vector curr_assignments = elim_enums[0];
        expr_ref_vector heap_cnstr_assignments(m);
        expr_ref_vector numeral_cnstr_assignments(m);
        for(expr* e : curr_assignments) {
            if(this->is_arith_formula(to_app(e)) || this->is_not_heap_or_loc_formula(to_app(e))) {
                numeral_cnstr_assignments.push_back(e);
            } else {
                heap_cnstr_assignments.push_back(e);
            }
        }
        // inc_ref for eliminated:
        for(expr* e : curr_assignments) {
            this->get_manager().inc_ref(e);
        }
        #ifdef SOLVING_INFO

        std::cout << "heap constraints ========== " << std::endl;
        for(expr* e : heap_cnstr_assignments) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
        } 
        std::cout << "numeral constraints ========== " << std::endl;
        for(expr* e : numeral_cnstr_assignments) {
            std::cout << mk_ismt2_pp(e, this->m) << std::endl;
        } 
        #endif
        // reset info from previous curr_assignments
        this->reset_inside_configs();
        // record current outside assignments and inside assignments
        for(expr* e : assignments) {
            this->curr_outside_assignments.push_back(e);
        }
        for(expr* e : curr_assignments) {
            this->curr_inside_assignments.push_back(e);
        }
        // ---------------------------------- NUMERAL CONSTRAINT SOLVING ------------
        solver* numeral_solver = mk_smt_solver(this->m, params_ref(), symbol("QF_LIA"));
        numeral_solver->inc_ref();
        for(expr* e: numeral_cnstr_assignments) {
            numeral_solver->assert_expr(e);
        }
        lbool result =  numeral_solver->check_sat();
        #ifdef SOLVING_INFO
        std::cout << "XXXXXXXXXXXXXXXXX coarse numeral constraint result XXXXXXXXXXXXXXXXXXX " << std::endl;
        if(result == l_true) {
            std::cout << "SAT" << std::endl;
        } else if(result == l_false) {
            std::cout << " FINAL CHECK UNSAT" << std::endl;
        } else {
            std::cout << "UNDEF" << std::endl;
        }
        std::cout << "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" << std::endl;
        #endif

        if(result == l_false) {
            // this->set_conflict_slhv(true, numeral_cnstr_core);
            this->check_status = slhv_unsat;
            std::vector<expr*> unsat_core;
            for(expr* nc : numeral_cnstr_assignments) {
                unsat_core.push_back(nc);
            }
            this->set_conflict_slhv(unsat_core);
            return false;
        } else if(result == l_true){
            model_ref nmd;
            numeral_solver->get_model(nmd);
            #ifdef SOLVING_INFO
            std::cout << "translated model: " << std::endl;
            model_smt2_pp(std::cout, this->m, *nmd, 0);
            #endif

        } else {
            #ifdef SLHV_PRINT
            std::cout << "ERROR: this should not happen" << std::endl;
            #endif
            SASSERT(false);
        }   
        // ---------------------------------- HEAP CONSTRAINT SOLVING ------------
        // preprocessing
        this->preprocessing(heap_cnstr_assignments);
        std::pair<std::set<std::pair<heap_term*, heap_term*>> ,std::set<heap_term*> > all_hterms = extract_all_hterms();
        #ifdef SOLVING_INFO
        std::cout << "all hterms: " << std::endl;
        for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
            std::cout << mk_ismt2_pp(this->curr_atomic_hterms[i], this->m) << "\t";
        }
        std::cout << std::endl;
        std::cout << "all eq pairs: " << std::endl;
        std::cout << std::endl;
        for(heap_term* ht : all_hterms.second) {
            ht->print(std::cout);
        }
        #endif
        for(heap_term* ht : all_hterms.second) {
            this->mem_mng->push_ht_ptr(ht);
        }
        formula_encoder* fec = alloc(formula_encoder, this, all_hterms.second, all_hterms.first);
        this->mem_mng->push_fec_ptr(fec);   
        // UNSAT FOUND in DEDUCTION
        if(fec->get_unsat_found()) {
            std::cout << "XXXXXXXX UNSAT in DEDUCTION XXXXXXXXXX" << std::endl;
            numeral_solver->dec_ref();
            this->set_conflict_slhv(this->infer_graph);
            this->mem_mng->dealloc_all();
            return false;
        }
        // REDUCTION ENCODING
        std::pair<expr*, expr_ref_vector> encoded_results = fec->encode_with_ass();
        expr* encoded_form = encoded_results.first;    
        expr_ref_vector assertions = encoded_results.second;
        #ifdef SOLVING_INFO
        std::ofstream debug_formula("debug_encoded.txt", std::ios::out);
        debug_formula << mk_ismt2_pp(encoded_form, this->m);
        #endif
        // std::cout << "encoded form size: " ;
        // std::cout << this->calculate_atomic_proposition(to_app(encoded_form)) << std::endl;
        // expr* encoded_form = this->get_manager().mk_false(); 
        this->get_manager().inc_ref(encoded_form);
        // std::cout << "encoded form ref count: " << encoded_form->get_ref_count() << std::endl;
        #ifdef SOLVING_INFO
        std::cout << "============= encoded formula ========== " << std::endl;
        // std::cout << mk_ismt2_pp(encoded_form, this->m) << std::endl;
        std::cout << "======================================== " << std::endl;
        #endif
        params_ref final_solver_param = params_ref();
        final_solver_param.set_bool("unsat_core", true);
        solver* final_solver = mk_smt_solver(this->m, final_solver_param, symbol("QF_LIA"));
        final_solver->inc_ref();
        for(expr* e: numeral_cnstr_assignments) {
            final_solver->assert_expr(e);
        }
        for(expr* e : assertions) {
            final_solver->assert_expr(e);
        }
        final_solver->assert_expr(encoded_form);
        std::cout << "assertion size: " << assertions.size() << std::endl;
        lbool final_result = final_solver->check_sat();
        std::cout << "XXXXXXXXXXXXXXXXX translated constraint result XXXXXXXXXXXXXXXXXXX" << std::endl;
        if(final_result == l_true) {
            #ifdef SOLVING_INFO
            std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET SAT XXXXXXXXXXXXXXXXXXXX" << std::endl;
            std::cout << " translated SAT " << std::endl;
            #endif
            // print current refined assignment to file
            std::ofstream output2file("./outmodel.txt", std::ios::out);
            output2file << "SAT" << std::endl;
            output2file << "ORIGINAL FORMULA XXXXXX" << std::endl;
            for(expr* e : refined_assignments) {
                output2file << mk_ismt2_pp(e, this->m) << std::endl;
            }   
            output2file << "ELIMINATED FORMULA XXXXXX" << std::endl;    
            output2file << "heap constraints ========== " << std::endl;
            for(expr* e : heap_cnstr_assignments) {
                output2file << mk_ismt2_pp(e, this->m) << std::endl;
            } 
            output2file << "numeral constraints ========== " << std::endl;
            for(expr* e : numeral_cnstr_assignments) {
                output2file << mk_ismt2_pp(e, this->m) << std::endl;
            } 
            output2file << "MODEL XXXXXX " << std::endl;

            std::map<std::string, expr*> name2val;
            model_ref md;
            final_solver->get_model(md);
            std::cout << "translated model: " << std::endl;
            // model_smt2_pp(std::cout, this->m, *md, 0);
            model_core& mdc = *md;
            for(int i = 0; i < mdc.get_num_constants(); i ++) {
                expr_ref temp_val(this->m);
                mdc.eval(mdc.get_constant(i), temp_val);
                // #ifdef SLHV_PRINT
                std::cout << " constant " << i << " " << mdc.get_constant(i)->get_name() << std::endl;
                std::cout << "eval: " << mk_ismt2_pp(temp_val, this->m) << std::endl; 
                // #endif
                output2file << " constant " << i << " " << mdc.get_constant(i)->get_name() << std::endl;
                output2file << "eval: " << mk_ismt2_pp(temp_val, this->m) << std::endl; 
                name2val[mdc.get_constant(i)->get_name().str()] = temp_val.get(); 
            }
            std::set<std::string> true_var_names;
            std::map<std::string, int> loc_data_var2val;
            for(auto key_val_p : name2val) {
                if(key_val_p.second->get_sort()->get_name() == "Bool") {
                    if(this->m.is_true(key_val_p.second)) {
                        true_var_names.insert(key_val_p.first);
                    } else if(this->m.is_false(key_val_p.second)) { 
                    } else {
                        SASSERT(false);
                    }

                } else {
                    SASSERT(key_val_p.second->get_sort()->get_name() == "Int");
                    auto param = to_app(key_val_p.second)->get_parameter(0);
                    std::cout << "int val for " << key_val_p.first << " " << " val " << param.get_rational().get_int64()<< std::endl;
                    std::cout << std::endl; 
                    std::vector<std::string> extracted_names = slhv_util::str_split(key_val_p.first, "_intvar");
                    for(std::string n : extracted_names) {
                        std::cout << n << std::endl;
                    }
                    loc_data_var2val[extracted_names[0]] =  param.get_rational().get_int64();
                }
            }
            std::set<atoms_subsumption*> atoms_subs = this->parse_and_collect_subsumption(fec, true_var_names);
            for(atoms_subsumption* sub : atoms_subs) {
                this->mem_mng->push_at_ptr(sub);
            }
            // record model information collected.
            this->model_subsume_info = atoms_subs;
            this->model_loc_data_var_val_info = loc_data_var2val;
            std::cout << "model info recorded: " << std::endl;
            output2file << "model info recorded: " << std::endl;
            std::cout << "model subsume info size: " << this->model_subsume_info.size() << std::endl;
            output2file << "model subsume info size: " << this->model_subsume_info.size() << std::endl; 
            for(atoms_subsumption* ats : this->model_subsume_info) {
                std::cout << "------- main" << std::endl;
                output2file << "------- main" << std::endl;
                ats->get_main_heap_term()->print_ht();
                ats->get_main_heap_term()->print_ht2file(output2file);
                std::cout << "------- subs" << std::endl;
                output2file << "------- subs" << std::endl;
                for(heap_term* h : ats->get_pt_atoms()) {
                    h->print_ht();
                    h->print_ht2file(output2file);
                }
            }
            std::cout << "locvar vals: " << std::endl;
            output2file << "locvar vals: " << std::endl;
            for(auto r : this->model_loc_data_var_val_info) {
                std::cout << r.first << " " << r.second << std::endl;
                output2file << r.first << " " << r.second << std::endl;
            }
            for(atoms_subsumption* sbs : this->model_subsume_info) {
                if(sbs->get_main_heap_term()->is_atom_hvar()) {
                    app* hvar_app = sbs->get_main_heap_term()->get_atoms()[0];
                    SASSERT(this->hvar2ptset.find(hvar_app) == this->hvar2ptset.end());
                    std::set<app*> pts_subsumed;
                    for(heap_term* pt_ht : sbs->get_pt_atoms()) {
                        pts_subsumed.insert(pt_ht->get_atoms()[0]);
                    }
                    this->hvar2ptset[hvar_app] = pts_subsumed;
                }
            }
            std::cout << "free heap vars:" << std::endl;
            output2file << "free heap vars: " << std::endl;
            for(app* hv : this->curr_hvars) {
                if(this->hvar2ptset.find(hv) == this->hvar2ptset.end()) {
                    std::cout << "emp hvar: " << hv->get_name() << std::endl;
                    output2file << "emp hvar: " << hv->get_name() << std::endl;
                }
            }
            final_solver->dec_ref();
            numeral_solver->dec_ref();
            this->m.dec_ref(encoded_form);  
            for(expr* e : curr_assignments) {
                this->get_manager().dec_ref(e);
            }
            this->mem_mng->dealloc_all();
            return true;
        } else if(final_result == l_false) { 
            std::cout << " translated UNSAT " << std::endl;
            SASSERT(final_solver->get_manager() == this->get_manager());
            // expr_ref_vector final_solver_unsat_core(this->get_manager());
            // final_solver->get_unsat_core(final_solver_unsat_core);
            // std::cout << "Final solver unsat core: " << std::endl;
            // for(expr* e : final_solver_unsat_core) {
            //     std::cout << mk_ismt2_pp(e, this->get_manager()) << std::endl;
            // }
            
            // if(final_solver_unsat_core.size() == 0) {
                this->set_conflict_slhv(this->curr_outside_assignments);
            // } else {
            //     std::vector<expr*> translated_unsat_core;
            //     std::set<expr*> unsat_core_set = this->recover_unsat_core(fec, final_solver_unsat_core);
            //     for(expr* e : unsat_core_set) {
            //         std::cout << "unsat core: " << mk_ismt2_pp(e, this->m) << std::endl;
            //         translated_unsat_core.push_back(e);
            //     }
            //     this->set_conflict_slhv(translated_unsat_core);
            // }
        } else {    
            std::cout << " translated UNKNOWN " << std::endl;
            SASSERT(false);
        }
        final_solver->dec_ref();
        numeral_solver->dec_ref();
        this->m.dec_ref(encoded_form);  
        // TODO: this may be buggy when elim num is not 1
        std::cout << "encoded form ref count after: " << encoded_form->get_ref_count() << std::endl;    
        for(expr* e : curr_assignments) {
            this->get_manager().dec_ref(e);
        }

        std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET UNSAT XXXXXXXXXXXXXXXXXXXX" << std::endl;

        std::ofstream output2file("./outmodel.txt", std::ios::out);
        output2file << "UNSAT" << std::endl;
        this->check_status = slhv_unsat;
        this->mem_mng->dealloc_all();
        return false;
    }


    std::vector<expr*> theory_slhv::eliminate_not_or_assignments(expr* expression) {
        // currently only single layered not or is eliminated

        std::vector<expr*> result;
        app* apped_expr = to_app(expression);
        if(apped_expr->is_app_of(basic_family_id, OP_NOT)) {
            app* apped_neg_arg = to_app(apped_expr->get_arg(0));
            if(apped_neg_arg->is_app_of(basic_family_id, OP_OR)) {
                for(int i = 0; i < apped_neg_arg->get_num_args(); i ++) {
                    app* disj_apped = to_app(apped_neg_arg->get_arg(i));
                    if(disj_apped->is_app_of(basic_family_id, OP_NOT)) {
                        result.push_back(disj_apped->get_arg(0));
                    } else {
                        result.push_back(this->syntax_maker->mk_not(disj_apped));
                    }
                }
                return result;
            } else if(apped_neg_arg->is_app_of(basic_family_id, OP_AND)) {
                std::cout << "ELIMINATE NOT OR NOT SUPPORT, NOT AND APPEARS" << std::endl;
            }
        }

        result.push_back(expression);
        return result;
    }


    expr* theory_slhv::eliminate_uplus_in_uplus_for_assignments(expr* expression) {
        app* apped_expr = to_app(expression);
        if(apped_expr->is_app_of(basic_family_id, OP_NOT)) {
            return expression;
        } else if(apped_expr->is_app_of(basic_family_id, OP_DISTINCT)) {
            return expression;
        } else if(apped_expr->is_app_of(basic_family_id, OP_EQ)) {
            app* arg1 = to_app(apped_expr->get_arg(0));
            app* arg2 = to_app(apped_expr->get_arg(1));
            if(this->is_uplus(arg2)) {
                app* eliminated_uplus = this->eliminate_uplus_uplus_hterm(arg2);
                if(eliminated_uplus == arg2) {
                    return expression;
                } else {
                    expr* result = this->get_manager().mk_eq(arg1, this->eliminate_uplus_uplus_hterm(arg2));
                    return result;
                }
            }
        } else {
            return expression;
        }
        return expression;
    }


    expr* theory_slhv::eliminate_uplus_in_uplus_for_assertion_disj(expr* assertion) {
        app* apped_expr = to_app(assertion);
        if(apped_expr->get_num_args() == 0) {
            return assertion;
        } else if(apped_expr->is_app_of(basic_family_id, OP_AND)) {
            expr_ref_vector conjuncts(this->m);
            for(int i = 0; i < apped_expr->get_num_args(); i ++) {
                conjuncts.push_back(this->eliminate_uplus_in_uplus_for_assertion_disj(apped_expr->get_arg(i)));
            }
            return this->syntax_maker->mk_and(conjuncts.size(), conjuncts.data());
        } else if(apped_expr->is_app_of(basic_family_id, OP_OR)) {

            expr_ref_vector disjuncts(this->m);
            for(int i = 0; i < apped_expr->get_num_args(); i ++) {
                disjuncts.push_back(this->eliminate_uplus_in_uplus_for_assertion_disj(apped_expr->get_arg(i)));
            }
            return this->syntax_maker->mk_or(disjuncts.size(), disjuncts.data());
        }
        else if(apped_expr->is_app_of(basic_family_id, OP_NOT)) {
            return this->syntax_maker->mk_not(this->eliminate_uplus_in_uplus_for_assertion_disj(apped_expr->get_arg(0)));
        } else if(apped_expr->is_app_of(basic_family_id, OP_DISTINCT)) {
            return this->syntax_maker->mk_distinct(this->eliminate_uplus_uplus_hterm(to_app(apped_expr->get_arg(0))), this->eliminate_uplus_uplus_hterm(to_app(apped_expr->get_arg(1))));
        } else if(apped_expr->is_app_of(basic_family_id, OP_EQ)) {
            app* arg1 = to_app(apped_expr->get_arg(0));
            app* arg2 = to_app(apped_expr->get_arg(1));
            if(this->is_uplus(arg2)) {
                app* eliminated_uplus = this->eliminate_uplus_uplus_hterm(arg2);
                if(eliminated_uplus == arg2) {
                    return assertion;
                } else {
                    expr* result = this->get_manager().mk_eq(arg1, this->eliminate_uplus_uplus_hterm(arg2));
                    return result;
                }
            }
        } 
        else {
            return assertion;
        }
        return assertion;
    }


    expr* theory_slhv::convert_to_nnf_recursive(expr* assertion) {
        app* apped_assertion = to_app(assertion);
        if(apped_assertion->is_app_of(basic_family_id, OP_NOT)) {
            app* inner = to_app(apped_assertion->get_arg(0));
            if(inner->is_app_of(basic_family_id, OP_NOT)) {
                return this->convert_to_nnf_recursive(inner->get_arg(0));
            } else if(inner->is_app_of(basic_family_id, OP_OR)) {
                expr_ref_vector new_args(this->m);
                for(int i = 0; i < inner->get_num_args(); i ++) {
                    new_args.push_back(this->convert_to_nnf_recursive(this->syntax_maker->mk_not(inner->get_arg(i))));
                }
                return this->syntax_maker->mk_and(new_args.size(), new_args.data());
            } else if(inner->is_app_of(basic_family_id, OP_AND)) {
                expr_ref_vector new_args(this->m);
                for(int i = 0; i < inner->get_num_args(); i ++) {
                    new_args.push_back(this->convert_to_nnf_recursive(this->syntax_maker->mk_not(inner->get_arg(i))));
                }
                return this->syntax_maker->mk_or(new_args.size(), new_args.data());
            } else if(inner->is_app_of(basic_family_id, OP_DISTINCT)) {
                return this->syntax_maker->mk_eq(inner->get_arg(0), inner->get_arg(1));
            } else {
                return apped_assertion;
            }
        } else if(apped_assertion->is_app_of(basic_family_id, OP_EQ)) {
            return apped_assertion;
        } 
        else if(apped_assertion->get_num_args() == 0) {
            return apped_assertion;
        } 
        else {
            // MAY BE BUGGY
            func_decl* apped_assertion_decl = apped_assertion->get_decl();
            std::vector<expr*> old_args;
            expr_ref_vector new_args(this->get_manager());
            for(int i = 0; i < apped_assertion->get_num_args(); i++) {
                old_args.push_back(apped_assertion->get_arg(i));
            }
            for(expr* arg : old_args) {
                new_args.push_back(this->convert_to_nnf_recursive(arg));
            }
            return this->m.mk_app(apped_assertion_decl, new_args);
        }
    }

    app* theory_slhv::eliminate_uplus_uplus_hterm(app* hterm) {
        if(this->is_uplus(hterm)) {
            std::vector<app*> new_args;
            for(int i = 0; i < hterm->get_num_args(); i ++) {
                app* uplus_i = this->eliminate_uplus_uplus_hterm(to_app(hterm->get_arg(i)));
                if(this->is_uplus(uplus_i)) {
                    for(int j = 0; j < uplus_i->get_num_args(); j ++) {
                        new_args.push_back(to_app(uplus_i->get_arg(j)));
                    }
                } else {
                    new_args.push_back(to_app(hterm->get_arg(i)));
                }
            }
            app* new_uplus = this->syntax_maker->mk_uplus_app(new_args.size(), new_args);   
            return new_uplus;
            
        } else {
            return hterm;
        }
    }

    void theory_slhv::preprocessing(expr_ref_vector assigned_literals) {
        #ifdef SLHV_PRINT
        std::cout << "slhv preprocessing" << std::endl;
        #endif
        this->collect_and_analyze_assignments(assigned_literals);
        // collect different types of constraints
        this->collect_loc_heap_and_data_cnstr_in_assignments(assigned_literals);
        #ifdef SLHV_PRINT
        std::cout << "slhv preprocessing end" << std::endl;
        #endif
    }


    void theory_slhv::preprocessing_disj() {
        #ifdef DISJ_DEBUG
        std::cout << "slhv disj preprocessing" << std::endl;
        #endif
        this->collect_and_analyze_assertions_disj(this->refined_asssertions_disj);
        // collect different types of constraints
        // DISJ TODO
        this->collect_heap_subassertions_disj(this->refined_asssertions_disj);
        this->collect_loc_data_inf_graph_assertions_disj(this->inf_graph_assertions_disj);
        #ifdef DISJ_DEBUG
        std::cout << "slhv disj preprocessing end" << std::endl;
        #endif
    }


    pt_record* theory_slhv::analyze_pt_record_type(app* record_app) {
        std::string app_record_name = record_app->get_name().bare_str();
        return this->slhv_plug->pt_record_map[app_record_name];
    }

    std::vector<expr_ref_vector> theory_slhv::eliminate_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals) {
        std::vector<std::vector<expr*>> last_result;
        for(auto e : assigned_literals) {
            std::vector<std::vector<expr*>> temp_result;
            if(this->is_not_heap_or_loc_formula(to_app(e))) {
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
                #ifdef SLHV_PRINT
                std::cout << " eliminate heap negation for " << mk_ismt2_pp(e, this->get_manager()) << std::endl;
                #endif

                temp_result = this->eliminate_heap_equality_negation(last_result, e);
                last_result = temp_result;

                #ifdef SLHV_PRINT
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

    std::vector<expr_ref_vector> theory_slhv::remove_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals) {
        std::vector<expr_ref_vector> result;
        expr_ref_vector v(this->m);
        for(auto e : assigned_literals) {
            if(this->is_not_heap_or_loc_formula(to_app(e))) {
                v.push_back(e);
            } else {
                app* curr_lit = to_app(e);
                if(is_app_of(curr_lit, basic_family_id, OP_NOT) || is_app_of(curr_lit, basic_family_id, OP_DISTINCT)) {
                    if(curr_lit->is_app_of(basic_family_id, OP_NOT)) {
                        app* equality = to_app(curr_lit->get_arg(0));
                        app* eq_lhs = to_app(equality->get_arg(0));
                        app* eq_rhs = to_app(equality->get_arg(1));
                        if(this->is_heapterm(eq_lhs) || this->is_heapterm(eq_rhs)) {
                            continue;
                        }
                    } else {
                        app* neq_lhs = to_app(curr_lit->get_arg(0));
                        app* neq_rhs = to_app(curr_lit->get_arg(1));
                        if(this->is_heapterm(neq_lhs) || this->is_heapterm(neq_rhs)) {
                            continue;
                        }
                    }
                }
                v.push_back(e);
            }
        }
        result.push_back(v);
        return result;
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
                    // std::vector<std::vector<app*>> disjuncts_after_elim = this->syntax_maker->mk_hterm_disequality_new(left_expr, right_expr);
                    std::vector<std::vector<app*>> disjuncts_after_elim = this->syntax_maker->mk_hterm_disequality_multi(left_expr, right_expr);
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
                    if(eliminated_neg_vec.size() > 0) {
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
            if(eliminated_neg_vec.size() > 0) {
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
        #ifdef SLHV_PRINT
        std::cout << "slhv collect and analyze assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            #ifdef SLHV_PRINT
            std::cout << "collect expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            app* app_e = to_app(e);
            #ifdef SLHV_PRINT
            std::cout << "collect vars in literal" << std::endl;
            #endif
            auto collected_vars = this->collect_vars(app_e);
            this->curr_locvars = slhv_util::setUnion(this->curr_locvars, std::get<0>(collected_vars));
            this->curr_hvars = slhv_util::setUnion(this->curr_hvars, std::get<1>(collected_vars));
            this->curr_datavars = slhv_util::setUnion(this->curr_datavars, std::get<2>(collected_vars));
            #ifdef SLHV_PRINT
            std::cout << "collect disj unions in literal" << std::endl;
            #endif
            this->curr_disj_unions = slhv_util::setUnion(this->curr_disj_unions, this->collect_disj_unions(app_e));

            #ifdef SLHV_PRINT
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
            #ifdef SLHV_PRINT
            std::cout << "begin construct emp" << std::endl;
            #endif
            if(!this->curr_hvars_contain_emp()) {
                SASSERT(slhv_plugin->global_emp != nullptr);
                app* ge = slhv_plugin->global_emp;
                this->get_context().internalize(ge, false);
                std::cout << "internalize " << mk_pp(ge, this->m) << std::endl;
                // this->curr_hvars.insert(ge);
                this->global_emp = ge;
            } else {
                SASSERT(this->global_emp == to_app(slhv_plugin->global_emp));
                this->get_context().internalize(to_app(slhv_plugin->global_emp), false);
            }
        } else {
            this->get_context().internalize(this->global_emp, false);
        }
        if(this->global_nil == nullptr) {
            #ifdef SLHV_PRINT
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
        for(app* pt : this->curr_pts) {
            this->curr_atomic_hterms.push_back(pt);
        }
        for(app* hv : this->curr_hvars ) {
            this->curr_atomic_hterms.push_back(hv);
        }
        this->curr_atomic_hterms.push_back(this->global_emp);
        #ifdef SLHV_PRINT
        std::cout << "collect and analyze assignments end" << std::endl;
        #endif
    }

    void theory_slhv::collect_and_analyze_assertions_disj(std::vector<app*> outside_assertions) {
        #ifdef DISJ_DEBUG
        std::cout << "slhv collect and analyze assignments" << std::endl;
        #endif
        for(auto e : outside_assertions) {
            #ifdef DISJ_DEBUG
            std::cout << "collect expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            app* app_e = to_app(e);
            auto collected_vars = this->collect_vars(app_e);
            this->locvars_disj = slhv_util::setUnion(this->locvars_disj, std::get<0>(collected_vars));
            this->hvars_disj = slhv_util::setUnion(this->hvars_disj, std::get<1>(collected_vars));
            this->datavars_disj = slhv_util::setUnion(this->datavars_disj, std::get<2>(collected_vars));
            
            this->disj_unions_disj = slhv_util::setUnion(this->disj_unions_disj, this->collect_disj_unions(app_e));

            this->pts_disj = slhv_util::setUnion(this->pts_disj,  this->collect_points_tos(app_e));
        }
        // if "emp" or "nil" does not appear in the literals, add and internalize them manually:
        decl_plugin* plug = this->m.get_plugin(get_id());
        SASSERT(plug->get_family_id() == this->get_manager().mk_family_id("slhv"));
        SASSERT(plug != nullptr);
        slhv_decl_plugin* slhv_plugin = (slhv_decl_plugin*) plug;
        if(this->global_emp == nullptr) {
            if(!this->hvars_contain_emp_disj()) {
                SASSERT(slhv_plugin->global_emp != nullptr);
                app* ge = slhv_plugin->global_emp;
                this->get_context().internalize(ge, false);
                std::cout << "internalize " << mk_pp(ge, this->m) << std::endl;
                // this->curr_hvars.insert(ge);
                this->global_emp = ge;
            } else {
                SASSERT(this->global_emp == to_app(slhv_plugin->global_emp));
                this->get_context().internalize(to_app(slhv_plugin->global_emp), false);
            }
        } else {
            this->get_context().internalize(this->global_emp, false);
        }
        if(this->global_nil == nullptr) {
            if(!this->locvars_contain_nil_disj()) {
                app* gn = slhv_plugin->global_nil;
                this->get_context().internalize(gn, false);
                std::cout << "internalize " << mk_pp(gn, this->m) << std::endl;
                this->locvars_disj.insert(gn);
                this->global_nil = slhv_plugin->global_nil;
            } else {
                SASSERT(this->global_nil == to_app(slhv_plugin->global_nil));
                this->get_context().internalize(to_app(slhv_plugin->global_nil), false);
            }
        } else {
            this->get_context().internalize(this->global_nil, false);
        }
        for(app* pt : this->pts_disj) {
            this->atomic_hterms_disj.push_back(pt);
        }
        for(app* hv : this->hvars_disj) {
            this->atomic_hterms_disj.push_back(hv);
        }
        this->atomic_hterms_disj.push_back(this->global_emp);
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
            // collected_hvars.insert(expression);
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

            #ifdef SLHV_PRINT
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


    bool theory_slhv::contain_disjunction(app const * n) {
        if(n->get_num_args() == 0) {
            return false;
        } else {
            bool result = false;
            for(int i = 0; i < n->get_num_args(); i ++) {
                result = result || this->contain_disjunction(to_app(n->get_arg(i)));
                if(result) {
                    return result;
                }
            }
            return result;
        }
    }
    
    void theory_slhv::collect_loc_heap_and_data_cnstr_in_assignments(expr_ref_vector assigned_literals){
        // collect all constrainst imposed on heap, loc and data
        for(auto e : assigned_literals) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                expr* negated = to_app(e)->get_arg(0);
                expr* negated_arg0 = to_app(negated)->get_arg(0);
                if(is_heapterm(to_app(negated_arg0))) {
                    SASSERT(false);
                    this->curr_heap_cnstr.insert(to_app(e));
                } else if(is_locterm(to_app(negated_arg0))) {
                    this->curr_loc_cnstr.insert(to_app(e));
                } else {
                    #ifdef SLHV_PRINT
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
                        SASSERT(!to_app(e)->is_app_of(basic_family_id, OP_DISTINCT));
                        this->curr_heap_cnstr.insert(to_app(e));
                    } else if(is_locterm(to_app(arg))) {
                        this->curr_loc_cnstr.insert(to_app(e));
                    } else {

                    #ifdef SLHV_PRINT
                    std::cout << "collect data cnstr: " << mk_ismt2_pp(e, this->m) << std::endl;
                    #endif
                        this->curr_data_cnstr.insert(to_app(e));
                    }
                }
            }
        }
    }

    
    // DISJ TODO
    void theory_slhv::collect_heap_subassertions_disj(std::vector<app*> outside_assertions) {
        // collect all constrainst imposed on heap, loc and data
        for(auto e : outside_assertions) {
            if(e->is_app_of(basic_family_id, OP_EQ)) {
                app* apped_arg1 = to_app(e->get_arg(0));
                if(this->is_heapterm(apped_arg1)) {
                    this->refined_heap_subassertions.insert(e);
                }
            } else if(this->is_subh(e)) {
                this->refined_subheap_assertions.insert(e);
            } else if(this->is_disjh(e)) {
                this->refined_disjheap_assertions.insert(e);
            } else {
                if(e->get_num_args() > 0) {
                    std::vector<app*> subassertions_to_collect;
                    for(int i = 0; i < e->get_num_args(); i++) {
                        subassertions_to_collect.push_back(to_app(e->get_arg(i)));
                    }
                    this->collect_heap_subassertions_disj(subassertions_to_collect);
                }
            }
        }
    }

    void theory_slhv::collect_loc_data_inf_graph_assertions_disj(std::set<app*> inf_assertions){
        for(auto e : inf_assertions) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                expr* negated = to_app(e)->get_arg(0);
                expr* negated_arg0 = to_app(negated)->get_arg(0);
                if(is_heapterm(to_app(negated_arg0))) {
                   // pass
                } else if(is_locterm(to_app(negated_arg0))) {
                    this->inf_graph_loc_assertions.insert(to_app(e));
                } else {
                    this->inf_graph_data_assertions.insert(to_app(e));
                    // this should not happen
                }
            } else {
                if(to_app(e)->is_app_of(basic_family_id, OP_DISTINCT) || 
                   to_app(e)->is_app_of(basic_family_id, OP_EQ) ){
                    expr* arg = to_app(e)->get_arg(0);
                    if(is_heapterm(to_app(arg))) {
                    } else if(is_locterm(to_app(arg))) {
                        this->inf_graph_loc_assertions.insert(to_app(e));
                    } else {
                        this->inf_graph_data_assertions.insert(to_app(e));
                    }
                } else if(this->is_subh(e)) {
                    this->inf_graph_subheap_assertions.insert(to_app(e));
                } else if(this->is_disjh(e)) {
                    this->inf_graph_disjheap_assertions.insert(to_app(e));
                }
            }
        }
    }

    void theory_slhv::reset_outside_configs() {
        this->curr_pts.clear();
        this->curr_disj_unions.clear();
        this->curr_hvars.clear();
        this->curr_locvars.clear();
        this->curr_atomic_hterms.clear();

        this->curr_loc_cnstr.clear();
        this->curr_heap_cnstr.clear();
        this->curr_data_cnstr.clear();

        this->check_status = slhv_unknown;
        
        this->curr_inside_assignments.clear();
        this->curr_outside_assignments.clear();
    }

    void theory_slhv::reset_inside_configs() {
        this->curr_pts.clear();
        this->curr_disj_unions.clear();
        this->curr_hvars.clear();
        this->curr_locvars.clear();
        this->curr_atomic_hterms.clear();

        this->curr_loc_cnstr.clear();
        this->curr_heap_cnstr.clear();
        this->curr_data_cnstr.clear();

        this->check_status = slhv_unknown;
        
        this->curr_inside_assignments.clear();
    }

    // check_logic

    std::pair<std::set<std::pair<heap_term*, heap_term*>>, std::set<heap_term*>> theory_slhv::extract_all_hterms() {
        #ifdef SLHV_PRINT
        std::cout << "begin extract all hterms" << std::endl;
        #endif
        std::set<heap_term*> eq_hterms;
        std::set<std::pair<heap_term*, heap_term*>> eq_pair_hterms;
        for(app* eq : this->curr_heap_cnstr) {
            heap_term* eq_lhs = nullptr;
            heap_term* eq_rhs = nullptr;

            SASSERT(eq != nullptr);
            SASSERT(eq->is_app_of(basic_family_id, OP_EQ));
            app* lhs_hterm = to_app(eq->get_arg(0));
            app* rhs_hterm = to_app(eq->get_arg(1));
            #ifdef SLHV_PRINT
            std::cout << "extract lhs hterm" << std::endl;
            #endif
            if(this->is_atom_hterm(lhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(lhs_hterm);
            
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                        if(atom == this->curr_atomic_hterms[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_atom_hterm = alloc(heap_term, this, this->curr_atomic_hterms, atoms_vec_count);
                    eq_hterms.insert(lhs_atom_hterm);
                    eq_lhs = lhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(lhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < lhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(lhs_hterm->get_arg(i)));
                }

                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                        if(atom == this->curr_atomic_hterms[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_bunch_hterm = alloc(heap_term, this, this->curr_atomic_hterms, atoms_contained);
                    eq_hterms.insert(lhs_bunch_hterm);
                    eq_lhs = lhs_bunch_hterm;
                    // inference graph update
                    this->infer_graph->add_compound_ht_node(lhs_bunch_hterm, eq);
                }
            }
            #ifdef SLHV_PRINT
            std::cout << "extract lhs hterm end" << std::endl;
            #endif
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm" << std::endl;
            #endif

            if(this->is_atom_hterm(rhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(rhs_hterm);
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                        if(atom == this->curr_atomic_hterms[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_atom_hterm = alloc(heap_term, this, this->curr_atomic_hterms, atoms_contained);
                    eq_hterms.insert(rhs_atom_hterm);
                    eq_rhs = rhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(rhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < rhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(rhs_hterm->get_arg(i)));
                }
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->curr_atomic_hterms.size(); i ++) {
                        if(atom == this->curr_atomic_hterms[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_bunch_hterm = alloc(heap_term, this, this->curr_atomic_hterms, atoms_contained);
                    eq_hterms.insert(rhs_bunch_hterm);
                    eq_rhs = rhs_bunch_hterm;
                    // inference graph update
                    this->infer_graph->add_compound_ht_node(rhs_bunch_hterm, eq);
                }
            }

            eq_pair_hterms.insert({eq_lhs, eq_rhs});
            // inference graph update
            this->infer_graph->add_ht_eq_pair_node({eq_lhs, eq_rhs}, eq);
            std::set<heap_term*> curr_eq_constraint_ht;
            curr_eq_constraint_ht.insert(eq_lhs);
            curr_eq_constraint_ht.insert(eq_rhs);
            this->constraint2hts[eq] = curr_eq_constraint_ht;
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm end" << std::endl;
            #endif
        }

        #ifdef SLHV_PRINT
        std::cout << "eq hterm extracted" << std::endl;
        #endif

        std::set<heap_term*> all_hterms;
        std::set<std::vector<int>> all_counts;
        std::vector<app*> atomics;
        for(heap_term* eq_hterm : eq_hterms) {
            std::set<std::vector<int>> curr_atom_counts = eq_hterm->get_atomic_subhterms_counts();
            all_counts = slhv_util::setUnion(all_counts, curr_atom_counts);
            all_hterms.insert(eq_hterm);
            atomics = eq_hterm->get_atomic_hterm_vec();
        }
        SASSERT(atomics.size() > 0);
        
        std::set<std::vector<int>> next_all_counts;
        for(auto vec : all_counts) {
            bool insert_to_next = true;
            for(heap_term* ht : all_hterms) {
                if(ht->get_atomic_count() == vec) {
                    insert_to_next = false;
                    break;
                }
            }
            if(insert_to_next) {
                next_all_counts.insert(vec);
            }
        }

        #ifdef SLHV_PRINT
        std::cout << " begin all heap term allocation" << std::endl;
        #endif
        for(std::vector<int> vec : next_all_counts) {
            heap_term* atom = alloc(heap_term, this, atomics, vec);
            all_hterms.insert(atom);
        }

        #ifdef SLHV_PRINT
        std::cout << "all heap term alloced" << std::endl;
        #endif

        bool has_emp = false;
        for(heap_term* ht : all_hterms) {
            if(ht->is_emp()) {
                has_emp = true;
                break;
            }
        }
        if(!has_emp && all_hterms.size() > 0) {
            std::vector<int> emp_vec(atomics.size(), 0);
            emp_vec[emp_vec.size() - 1] = 1;
            heap_term* emp_hterm = alloc(heap_term, this, atomics, emp_vec);
            all_hterms.insert(emp_hterm);
        }


        #ifdef SLHV_PRINT
        std::cout << "emp heap term alloced" << std::endl;
        #endif

        
        // std::vector<int> emp_hterm_count(this->curr_atomic_hterms.size(), 0);
        // emp_hterm_count[this->curr_atomic_hterms.size() - 1] = 1;
        // for(heap_term* eht : all_hterms) {
        //     if(eht->get_atomic_count() == emp_hterm_count) {
        //         break;
        //     } else {
        //         heap_term* emp_hterm = alloc(heap_term, this, this->curr_atomic_hterms, emp_hterm_count);
        //         all_hterms.insert(emp_hterm);
        //     }
        // }
        
        return {eq_pair_hterms, all_hterms};
    }


    hterm_extracted_content*  theory_slhv::extract_all_hterms_disj() {
        #ifdef DISJ_DEBUG
        std::cout << "begin extract all hterms disj" << std::endl;
        #endif
        hterm_extracted_content* result = alloc(hterm_extracted_content);
        std::set<heap_term*> eq_htr_hterms;
        std::set<std::pair<heap_term*, heap_term*>> eq_pair_hterms;
        std::set<std::pair<heap_term*, heap_term*>> sub_pair_hterms;
        std::set<std::pair<heap_term*, heap_term*>> disj_pair_hterms;
        for(app* eq : this->refined_heap_subassertions) {
            // determine whether eq in inference graph
            bool use_inf_graph = false;
            for(app* inf_e : this->inf_graph_assertions_disj) {
                if(eq == inf_e) {
                    use_inf_graph = true;
                    break;
                }
            }
            heap_term* eq_lhs = nullptr;
            heap_term* eq_rhs = nullptr;

            SASSERT(eq != nullptr);
            SASSERT(eq->is_app_of(basic_family_id, OP_EQ));
            app* lhs_hterm = to_app(eq->get_arg(0));
            app* rhs_hterm = to_app(eq->get_arg(1));
            #ifdef DISJ_DEBUG
            std::cout << "extract lhs hterm" << std::endl;
            #endif
            if(this->is_atom_hterm(lhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(lhs_hterm);
            
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_atom_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_vec_count);
                    eq_htr_hterms.insert(lhs_atom_hterm);
                    eq_lhs = lhs_atom_hterm;
                    
                }
            } else {
                SASSERT(this->is_uplus(lhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < lhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(lhs_hterm->get_arg(i)));
                }

                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_bunch_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(lhs_bunch_hterm);
                    eq_lhs = lhs_bunch_hterm;
                    // inference graph update
                    if(use_inf_graph) {
                        this->infer_graph->add_compound_ht_node(lhs_bunch_hterm, eq);
                    }
                }
            }
            #ifdef SLHV_PRINT
            std::cout << "extract lhs hterm end" << std::endl;
            #endif
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm" << std::endl;
            #endif

            if(this->is_atom_hterm(rhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(rhs_hterm);
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_atom_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(rhs_atom_hterm);
                    eq_rhs = rhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(rhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < rhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(rhs_hterm->get_arg(i)));
                }
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        eq_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_bunch_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(rhs_bunch_hterm);
                    eq_rhs = rhs_bunch_hterm;
                    // inference graph update
                    if(use_inf_graph) {
                        this->infer_graph->add_compound_ht_node(rhs_bunch_hterm, eq);
                    }
                }
            }

            // inference graph update
            if(use_inf_graph) {
                this->infer_graph->add_ht_eq_pair_node({eq_lhs, eq_rhs}, eq);
                eq_pair_hterms.insert({eq_lhs, eq_rhs});
            }
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm end" << std::endl;
            #endif
        }

        for(app* subh_atom : this->refined_subheap_assertions) {
            // determine whether eq in inference graph
            bool use_inf_graph = false;
            for(app* inf_e : this->inf_graph_assertions_disj) {
                if(subh_atom == inf_e) {
                    use_inf_graph = true;
                    break;
                }
            }
            heap_term* subh_lhs = nullptr;
            heap_term* subh_rhs = nullptr;

            SASSERT(subh_atom != nullptr);
            SASSERT(subh_atom->is_app_of(this->get_family_id(), OP_SUBH));
            app* lhs_hterm = to_app(subh_atom->get_arg(0));
            app* rhs_hterm = to_app(subh_atom->get_arg(1));
            #ifdef DISJ_DEBUG
            std::cout << "extract lhs hterm" << std::endl;
            #endif
            if(this->is_atom_hterm(lhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(lhs_hterm);
            
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        subh_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_atom_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_vec_count);
                    eq_htr_hterms.insert(lhs_atom_hterm);
                    subh_lhs = lhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(lhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < lhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(lhs_hterm->get_arg(i)));
                }

                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        subh_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_bunch_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(lhs_bunch_hterm);
                    subh_lhs = lhs_bunch_hterm;
                    // inference graph update
                    if(use_inf_graph) {
                        this->infer_graph->add_compound_ht_node(lhs_bunch_hterm, subh_atom);
                    }
                }
            }
            #ifdef SLHV_PRINT
            std::cout << "extract lhs hterm end" << std::endl;
            #endif
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm" << std::endl;
            #endif

            if(this->is_atom_hterm(rhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(rhs_hterm);
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        subh_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_atom_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(rhs_atom_hterm);
                    subh_rhs = rhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(rhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < rhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(rhs_hterm->get_arg(i)));
                }
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        subh_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_bunch_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(rhs_bunch_hterm);
                    subh_rhs = rhs_bunch_hterm;
                    // inference graph update
                    if(use_inf_graph) {
                        this->infer_graph->add_compound_ht_node(rhs_bunch_hterm, subh_atom);
                    }
                }
            }

            // inference graph update
            if(use_inf_graph) {
                this->infer_graph->add_subht_pair_node({subh_lhs, subh_rhs}, subh_atom);
                sub_pair_hterms.insert({subh_lhs, subh_rhs});
            }
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm end" << std::endl;
            #endif
        }

        for(app* disjh_atom : this->refined_disjheap_assertions) {
            // determine whether eq in inference graph
            bool use_inf_graph = false;
            for(app* inf_e : this->inf_graph_assertions_disj) {
                if(disjh_atom == inf_e) {
                    use_inf_graph = true;
                    break;
                }
            }
            heap_term* disjh_lhs = nullptr;
            heap_term* disjh_rhs = nullptr;

            SASSERT(disjh_atom != nullptr);
            SASSERT(disjh_atom->is_app_of(this->get_family_id(), OP_SUBH));
            app* lhs_hterm = to_app(disjh_atom->get_arg(0));
            app* rhs_hterm = to_app(disjh_atom->get_arg(1));
            #ifdef DISJ_DEBUG
            std::cout << "extract lhs hterm" << std::endl;
            #endif
            if(this->is_atom_hterm(lhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(lhs_hterm);
            
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        disjh_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_atom_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_vec_count);
                    eq_htr_hterms.insert(lhs_atom_hterm);
                    disjh_lhs = lhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(lhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < lhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(lhs_hterm->get_arg(i)));
                }

                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        disjh_lhs = ht;
                        break;
                    }
                }
                if(!found) {
                    heap_term* lhs_bunch_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(lhs_bunch_hterm);
                    disjh_lhs = lhs_bunch_hterm;
                    // inference graph update
                    if(use_inf_graph) {
                        this->infer_graph->add_compound_ht_node(lhs_bunch_hterm, disjh_atom);
                    }
                }
            }
            #ifdef SLHV_PRINT
            std::cout << "extract lhs hterm end" << std::endl;
            #endif
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm" << std::endl;
            #endif

            if(this->is_atom_hterm(rhs_hterm)) {
                std::vector<app*> atoms_contained;
                atoms_contained.push_back(rhs_hterm);
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        disjh_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_atom_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(rhs_atom_hterm);
                    disjh_rhs = rhs_atom_hterm;
                }
            } else {
                SASSERT(this->is_uplus(rhs_hterm));
                std::vector<app*> atoms_contained;
                for(int i = 0; i < rhs_hterm->get_num_args(); i ++) {
                    atoms_contained.push_back(to_app(rhs_hterm->get_arg(i)));
                }
                std::vector<int> atoms_vec_count;
                for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                    atoms_vec_count.push_back(0);
                }
                for(app* atom : atoms_contained) {
                    for(int i = 0; i < this->atomic_hterms_disj.size(); i ++) {
                        if(atom == this->atomic_hterms_disj[i]) {
                            atoms_vec_count[i] ++;
                        }
                    }
                }
                bool found = false;
                for(heap_term* ht : eq_htr_hterms) {
                    if(ht->get_atomic_count() == atoms_vec_count) {
                        found = true;
                        disjh_rhs = ht;
                        break;
                    }
                }

                if(!found) {
                    heap_term* rhs_bunch_hterm = alloc(heap_term, this, this->atomic_hterms_disj, atoms_contained);
                    eq_htr_hterms.insert(rhs_bunch_hterm);
                    disjh_rhs = rhs_bunch_hterm;
                    // inference graph update
                    if(use_inf_graph) {
                        this->infer_graph->add_compound_ht_node(rhs_bunch_hterm, disjh_atom);
                    }
                }
            }

            // inference graph update
            if(use_inf_graph) {
                this->infer_graph->add_disjht_pair_node({disjh_lhs, disjh_rhs}, disjh_atom);
                disj_pair_hterms.insert({disjh_lhs, disjh_rhs});
            }
            #ifdef SLHV_PRINT
            std::cout << "extract rhs hterm end" << std::endl;
            #endif
        }

        #ifdef SLHV_PRINT
        std::cout << "eq hterm extracted" << std::endl;
        #endif

        std::set<heap_term*> all_hterms;
        std::set<std::vector<int>> all_counts;
        std::vector<app*> atomics;
        for(heap_term* eq_hterm : eq_htr_hterms) {
            std::set<std::vector<int>> curr_atom_counts = eq_hterm->get_atomic_subhterms_counts();
            all_counts = slhv_util::setUnion(all_counts, curr_atom_counts);
            all_hterms.insert(eq_hterm);
            atomics = eq_hterm->get_atomic_hterm_vec();
        }
        SASSERT(atomics.size() > 0);
        
        std::set<std::vector<int>> next_all_counts;
        for(auto vec : all_counts) {
            bool insert_to_next = true;
            for(heap_term* ht : all_hterms) {
                if(ht->get_atomic_count() == vec) {
                    insert_to_next = false;
                    break;
                }
            }
            if(insert_to_next) {
                next_all_counts.insert(vec);
            }
        }

        #ifdef SLHV_PRINT
        std::cout << " begin all heap term allocation" << std::endl;
        #endif
        for(std::vector<int> vec : next_all_counts) {
            heap_term* atom = alloc(heap_term, this, atomics, vec);
            all_hterms.insert(atom);
        }

        #ifdef SLHV_PRINT
        std::cout << "all heap term alloced" << std::endl;
        #endif

        bool has_emp = false;
        for(heap_term* ht : all_hterms) {
            if(ht->is_emp()) {
                has_emp = true;
                break;
            }
        }
        if(!has_emp && all_hterms.size() > 0) {
            std::vector<int> emp_vec(atomics.size(), 0);
            emp_vec[emp_vec.size() - 1] = 1;
            heap_term* emp_hterm = alloc(heap_term, this, atomics, emp_vec);
            all_hterms.insert(emp_hterm);
        }


        #ifdef SLHV_PRINT
        std::cout << "emp heap term alloced" << std::endl;
        #endif

        
        // std::vector<int> emp_hterm_count(this->curr_atomic_hterms.size(), 0);
        // emp_hterm_count[this->curr_atomic_hterms.size() - 1] = 1;
        // for(heap_term* eht : all_hterms) {
        //     if(eht->get_atomic_count() == emp_hterm_count) {
        //         break;
        //     } else {
        //         heap_term* emp_hterm = alloc(heap_term, this, this->curr_atomic_hterms, emp_hterm_count);
        //         all_hterms.insert(emp_hterm);
        //     }
        // }
        result->all_hterms = all_hterms;
        result->disj_pair_hterms = disj_pair_hterms;
        result->sub_pair_hterms = sub_pair_hterms;
        result->eq_pair_hterms = eq_pair_hterms;
        return result;
    }




    void theory_slhv::print_all_hterms(std::ostream& os){
        os << "current atomic hterms: " << std::endl;
        for(app* ht : this->curr_atomic_hterms) {
            os << mk_ismt2_pp(ht, this->m) << "\t";
        }
        os << std::endl;
    }


    std::set<atoms_subsumption*> theory_slhv::parse_and_collect_subsumption(formula_encoder* enc, std::set<std::string> true_bool_strs) {
        std::set<std::pair<heap_term*, heap_term*>> subparent_pairs;
        for(std::string name : true_bool_strs) {
            if(name.find("ish") != name.npos) {
                std::vector<std::string> tokens = slhv_util::str_split(name, "_");
                SASSERT(tokens[0].compare("ish") == 0);
                int subsumed_id = atoi(tokens[1].data());
                int parent_id = atoi(tokens[2].data());
                subparent_pairs.insert({enc->get_ht_by_id(subsumed_id), enc->get_ht_by_id(parent_id)});
            } else if(name.find("idj") != name.npos) {
            } else {
                SASSERT(false);
            }
        }
        std::map<heap_term*, std::set<heap_term*>> ht2subpts;
        for(auto p : subparent_pairs) {
            if(p.first->is_atom_pt()) {
                if(ht2subpts.find(p.second) != ht2subpts.end()) {
                    ht2subpts[p.second].insert(p.first);
                } else {
                    std::set<heap_term*> subpts;
                    subpts.insert(p.first);
                    ht2subpts[p.second] = subpts;
                }
            }
        }
        std::set<atoms_subsumption*> result;
        for(auto r : ht2subpts) {
            atoms_subsumption* s = alloc(atoms_subsumption, r.first, r.second);
            result.insert(s);
        }
        return result;
    }



    theory_var theory_slhv::mk_var(enode* n) {
        SASSERT(!is_attached_to_var(n));
        theory_var v = m_var2enode.size();
        m_var2enode.push_back(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;
    }

    // heap term
    heap_term::heap_term(theory_slhv* th, std::vector<app*> atomics, std::vector<app*> atoms) {
        this->th = th;
        this->atomic_hterms_vec = atomics;
        for(int i = 0; i < this->atomic_hterms_vec.size(); i ++) {
            this->atomic_hterms_count.push_back(0);
        }
        for(app* atom_contained : atoms) {
            for(int i = 0; i < this->atomic_hterms_vec.size(); i ++) {
                if(this->atomic_hterms_vec[i] == atom_contained) {
                    this->atomic_hterms_count[i] ++;
                    break;
                }
                SASSERT(false);
            }
        }
    }

    bool heap_term::is_subhterm_of(heap_term* ht) {
        SASSERT(this->get_atomic_hterm_vec() == ht->get_atomic_hterm_vec());
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(this->get_pos(i) > ht->get_pos(i)) {
                return false;
            }
        }
        return true;
    }

    bool heap_term::is_suphterm_of(heap_term* ht) {
        SASSERT(this->get_atomic_hterm_vec() == ht->get_atomic_hterm_vec());
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(ht->get_pos(i) > this->get_pos(i)) {
                return false;
            }
        }
        return true;
    }

    heap_term* heap_term::intersect_with(heap_term* ht) {
        SASSERT(this->get_atomic_hterm_vec() == ht->get_atomic_hterm_vec());
        std::vector<int> new_count;
        for(int i = 0; i < this->get_vec_size(); i ++) {
            new_count[i] = 0;
        }
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(this->get_pos(i) > 0 && ht->get_pos(i) > 0) {
                int min = this->get_pos(i) > this->get_pos(i) ? this->get_pos(i) : this->get_pos(i);
                new_count[i] = min;
            }
        }
        heap_term* intersected_hterm = alloc(heap_term, this->th, this->get_atomic_hterm_vec(), new_count);
        return intersected_hterm;
    }

    std::vector<app*> heap_term::get_atoms() {
        std::vector<app*> result;
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(this->get_pos(i)) {
                for(int j = 0; j < this->get_pos(i); j ++) {
                    result.push_back(this->atomic_hterms_vec[i]);
                }
            }
        }
        return result;
    }



    bool heap_term::is_emp() {
        if(this->get_pos(this->get_vec_size() - 1) != 1) {
            return false;
        }
        for(int i = 0; i < this->get_vec_size() - 1; i ++) {
            if(this->get_pos(i) > 0) {
                return false;
            }
        }
        return true;
    }

    bool heap_term::is_atom_pt() {
        return this->get_pt_num() == 1 && this->get_hvar_num() == 0 && !this->is_emp();
    }

    bool heap_term::is_atom_hvar() {
        return this->get_pt_num() == 0 && this->get_hvar_num() == 1 && !this->is_emp();
    }

    int heap_term::get_pt_num() {
        int result = 0;
        for(int i = 0; i < this->get_vec_size(); i++) {
            if(this->th->is_points_to(this->atomic_hterms_vec[i])) {
                result += this->get_pos(i);
            }
        }
        return result;
    }


    bool heap_term::is_uplus_hterm() {
        if(this->get_hvar_num() + this->get_pt_num() > 1) {
            return true;
        }
        return false;
    }

    int heap_term::get_hvar_num() {
        int result = 0;
        for(int i = 0; i < this->get_vec_size(); i++) {
            if(this->th->is_hvar(this->atomic_hterms_vec[i])) {
                result += this->get_pos(i);
            }
        }
        return result;
    }

    int heap_term::get_emp_num() {
        int result = 0;
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(this->th->is_emp(this->atomic_hterms_vec[i])) {
                result += this->get_pos(i);
            }
        }
        return result;
    }

    std::set<heap_term*> heap_term::get_subhterms() {
        std::set<heap_term*> result;
        std::set<std::vector<int>> current_enum;
        std::set<std::vector<int>> next_enum;
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(i == 0) {
                for(int j = 0; j <= this->get_pos(i); j ++) {
                    std::vector<int> partial_vec;
                    partial_vec.push_back(j);
                    next_enum.insert(partial_vec);
                }
            } else {
                for(std::vector<int> last_partial_vec : current_enum) {
                    for(int j = 0; j <= this->get_pos(i); j ++) {
                        std::vector<int>  next_partial_vec = last_partial_vec;
                        next_partial_vec.push_back(j);
                        next_enum.insert(next_partial_vec);
                    }
                }
            }
            current_enum = next_enum;
            next_enum.clear();
        }
        for(std::vector<int> atoms_count : current_enum) {
            bool is_valid_hterm = false;
            for(int hterm_num : atoms_count) {
                if(hterm_num > 0) {
                    is_valid_hterm = true;
                    break;
                }
            }
            if(is_valid_hterm) {
                heap_term* subhterm = alloc(heap_term, this->th, this->atomic_hterms_vec, atoms_count);
                result.insert(subhterm);
            }
        }
        return result;
    }


    std::set<std::vector<int>> heap_term::get_atomic_subhterms_counts() {
        std::set<std::vector<int>> atomic_counts;
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(this->get_pos(i) > 0) {
                std::vector<int> temp_count(this->get_vec_size(), 0);
                temp_count[i] = 1;
                atomic_counts.insert(temp_count);
            }
        }
        return atomic_counts;
    }


    std::set<std::pair<std::vector<int>, std::vector<int>>> heap_term::get_splitted_subpairs() {
        SASSERT(!this->is_atom_hvar() && !this->is_atom_pt() && !this->is_emp());
        std::set<std::vector<int>> curr_enum;
        std::set<std::vector<int>> next_enum;
        for(int i = 0; i < this->get_vec_size(); i ++) {
            if(i == 0) {
                for(int j = 0; j <= this->get_pos(i); j ++) {
                    std::vector<int> partial_vec;
                    partial_vec.push_back(j);
                    next_enum.insert(partial_vec);
                }
            } else {
                for(std::vector<int> last_partial_vec : curr_enum) {
                    for(int j = 0; j <= this->get_pos(i); j ++) {
                        std::vector<int> next_partial_vec = last_partial_vec;
                        next_partial_vec.push_back(j);
                        next_enum.insert(next_partial_vec);
                    }
                }
            }
            curr_enum = next_enum;
            next_enum.clear();
        }


        for(std::vector<int> atoms_count : curr_enum) {
            bool is_valid_hterm = false;
            for(int i = 0; i < this->get_vec_size(); i ++) {
                if(atoms_count[i] > 0) {
                    is_valid_hterm = true;
                    break;
                }
            }
            if(is_valid_hterm) {
                next_enum.insert(atoms_count);
            }
        }
        curr_enum = next_enum;

        std::set<std::pair<std::vector<int>, std::vector<int>>> result;
        for(std::vector<int> first_elem_vector : curr_enum) {
            std::vector<int> whole_vec = this->get_atomic_count();
            std::vector<int> remnant_vec = whole_vec;
            for(int i = 0; i < this->get_vec_size(); i ++) {
                remnant_vec[i] -= first_elem_vector[i];
            }
            bool pair_exists = false;
            for(auto p : result) {
                if(p.second == first_elem_vector && p.first == remnant_vec || 
                   p.first == first_elem_vector && p.second == remnant_vec) {
                    pair_exists = true;
                    break;
                }
            }
            if(!pair_exists) {
                result.insert({first_elem_vector, remnant_vec});
            }
        }
        return result;
    }


    std::set<std::pair<std::vector<int>, std::vector<int>>> heap_term::get_all_distinct_atomic_pairs() {
        std::set<std::vector<int>> atomic_pairs = this->get_atomic_subhterms_counts();
        std::set<std::pair<std::vector<int>, std::vector<int>>> result;
        for(std::vector<int> v1 : atomic_pairs) {
            for(std::vector<int> v2 : atomic_pairs) {
                if(v1 != v2) {
                    result.insert({v1, v2});
                }
            }
        }
        return result;
    }
    


    void heap_term::print_ht() {
        std::cout << "( ";                    
        for(int i = 0; i < this->get_vec_size(); i ++) {
            for(int l = 0; l < this->get_pos(i); l ++) {
                std::cout << mk_ismt2_pp(this->atomic_hterms_vec[i], this->th->get_manager()) << " | ";
            }
        }
        std::cout << ")" << std::endl;
    }


    void heap_term::print_ht2file(std::ofstream& f) {
        f << "( ";                    
        for(int i = 0; i < this->get_vec_size(); i ++) {
            for(int l = 0; l < this->get_pos(i); l ++) {
                f << mk_ismt2_pp(this->atomic_hterms_vec[i], this->th->get_manager()) << " | ";
            }
        }
        f << ")" << std::endl;
    }



    void heap_term::print(std::ostream& os) {
        os << "hterm id: ";
        for(int index = 0; index < this->get_vec_size(); index ++) {
            os << " " << this->atomic_hterms_count[index] << " ";
        }
        os << std::endl;
    }
    
    // encoder
    formula_encoder::formula_encoder(theory_slhv* th, std::set<heap_term*> all_hterms, std::set<std::pair<heap_term*, heap_term*>>  eq_hterm_pairs) {
        // record all kinds of hts
        this->th = th;
        this->emp_ht = nullptr;
        this->unsat_found = false;
        int i = 0;
        for(heap_term* ht : all_hterms) {
            this->ht2index_map[ht] = i;
            this->index2ht.push_back(ht);
            i ++;
        }
        this->hts = all_hterms;
        this->eq_ht_pairs = eq_hterm_pairs;
        for(heap_term* ht : this->hts) {
            this->ht2root[ht] = ht;
            if(ht->is_emp()) {
                SASSERT(this->emp_ht == nullptr);
                this->emp_ht = ht;
            } else if(ht->is_atom_pt()) {
                this->atom_hts.insert(ht);
                this->pt_hts.insert(ht);
            } else if(ht->is_atom_hvar()) {
                this->atom_hts.insert(ht);
                this->hvar_hts.insert(ht);
            } else {
                // compound ht
            }
        }
        this->syntax_maker = this->th->syntax_maker;

        // create boolean variables
        for(int ht1_index = 0; ht1_index < this->hts.size(); ht1_index ++) {
            for(int ht2_index = 0; ht2_index < this->hts.size(); ht2_index ++) {
                if(ht1_index != ht2_index || this->djrel_var_map.find({ht1_index, ht2_index}) == this->djrel_var_map.end()) {
                    std::string idj_name_prefix = "idj";
                    std::string ish_name_prefix = "ish";
                    std::pair<int, int> key_pair = {ht1_index, ht2_index};
                    app* idj_boolvar = this->syntax_maker->mk_boolvar(idj_name_prefix + "_" + std::to_string(key_pair.first) + "_" + std::to_string(key_pair.second));

                    app* ish_boolvar = this->syntax_maker->mk_boolvar(ish_name_prefix + "_" + std::to_string(key_pair.first) + "_" + std::to_string(key_pair.second));

                    this->djrel_var_map[key_pair] = idj_boolvar;
                    this->shrel_var_map[key_pair] = ish_boolvar;
                    this->djrel_var2pair[idj_boolvar] = key_pair;
                    this->shrel_var2pair[ish_boolvar] = key_pair;
                } 
            }
        }
        // create intvar for locvar
        for(app* lv : this->th->curr_locvars) {
            SASSERT(this->th->is_locvar(lv));
            std::string name = lv->get_name().str();
            std::string int_name = name + "_intvar";
            app* intvar = this->syntax_maker->mk_lia_intvar(int_name);
            SASSERT(this->locvar2intvar_map.find(lv) == this->locvar2intvar_map.end());
            this->locvar2intvar_map[lv] = intvar;
        }
        #ifdef SLHV_PRINT
        std::cout << "formula encoder created" << std::endl;
        #endif

        this->ded = alloc(slhv_deducer, th, this, false);
        // std::cout << "begin deducing" << std::endl;
        ded->deduce();
        if(this->ded->get_is_unsat()) {
            this->unsat_found = true;
        }
        this->construct_ht2root_from_deducer();
        #ifdef SOLVING_INFO
        ded->print_current(std::cout);
        std::cout << "deduce unsat: " << ded->get_is_unsat() << std::endl;
        #endif
    }


    formula_encoder::formula_encoder(theory_slhv* th, std::set<heap_term*> all_hterms) {
        // record all kinds of hts
        this->th = th;
        this->emp_ht = nullptr;
        this->unsat_found = false;
        int i = 0;
        for(heap_term* ht : all_hterms) {
            this->ht2index_map[ht] = i;
            this->index2ht.push_back(ht);
            i ++;
        }
        this->hts = all_hterms;
        // inf_graph assertions 
        this->eq_ht_pairs = this->th->inf_graph_eq_pairs_hterms_disj;
        this->subht_pairs = this->th->inf_graph_subh_pair_hterms_disj;
        this->disjht_pairs  = this->th->inf_graph_disjh_pair_hterms_disj;
        for(heap_term* ht : this->hts) {
            this->ht2root[ht] = ht;
            if(ht->is_emp()) {
                SASSERT(this->emp_ht == nullptr);
                this->emp_ht = ht;
            } else if(ht->is_atom_pt()) {
                this->atom_hts.insert(ht);
                this->pt_hts.insert(ht);
            } else if(ht->is_atom_hvar()) {
                this->atom_hts.insert(ht);
                this->hvar_hts.insert(ht);
            } else {
                // compound ht
            }
        }
        this->syntax_maker = this->th->syntax_maker;

        // create boolean variables
        for(int ht1_index = 0; ht1_index < this->hts.size(); ht1_index ++) {
            for(int ht2_index = 0; ht2_index < this->hts.size(); ht2_index ++) {
                if(ht1_index != ht2_index || this->djrel_var_map.find({ht1_index, ht2_index}) == this->djrel_var_map.end()) {
                    std::string idj_name_prefix = "idj";
                    std::string ish_name_prefix = "ish";
                    std::pair<int, int> key_pair = {ht1_index, ht2_index};
                    app* idj_boolvar = this->syntax_maker->mk_boolvar(idj_name_prefix + "_" + std::to_string(key_pair.first) + "_" + std::to_string(key_pair.second));

                    app* ish_boolvar = this->syntax_maker->mk_boolvar(ish_name_prefix + "_" + std::to_string(key_pair.first) + "_" + std::to_string(key_pair.second));

                    this->djrel_var_map[key_pair] = idj_boolvar;
                    this->shrel_var_map[key_pair] = ish_boolvar;
                    this->djrel_var2pair[idj_boolvar] = key_pair;
                    this->shrel_var2pair[ish_boolvar] = key_pair;
                } 
            }
        }
        // create intvar for locvar
        for(app* lv : this->th->locvars_disj) {
            SASSERT(this->th->is_locvar(lv));
            std::string name = lv->get_name().str();
            std::string int_name = name + "_intvar";
            app* intvar = this->syntax_maker->mk_lia_intvar(int_name);
            SASSERT(this->locvar2intvar_map.find(lv) == this->locvar2intvar_map.end());
            this->locvar2intvar_map[lv] = intvar;
        }
        #ifdef SLHV_PRINT
        std::cout << "formula encoder created" << std::endl;
        #endif

        // DISJ TODO: add deducing for disj method
        this->ded = alloc(slhv_deducer, th, this, true);
        ded->deduce();
        if(this->ded->get_is_unsat()) {
            this->unsat_found = true;
        }
        this->construct_ht2root_from_deducer_disj();
        // this->construct_ht2root_from_nothing();
        // ded->print_current(std::cout);
        #ifdef SOLVING_INFO
        ded->print_current(std::cout);
        std::cout << "deduce unsat: " << ded->get_is_unsat() << std::endl;
        #endif
    }

    void formula_encoder::construct_ht2root_from_deducer() {
        for(heap_term* ht1 : this->hts) {
            for(heap_term* ht2 : this->hts) {
                if(ht1 != ht2) {
                    // merge equivalent class and remain all uplus term
                    int ht1_index = this->ht2index_map[ht1];
                    int ht2_index = this->ht2index_map[ht2];
                    if(ded->has_shrel(ht1_index, ht2_index) &&
                       ded->has_shrel(ht2_index, ht1_index) &&
                       !(ht1->is_uplus_hterm() || ht2->is_uplus_hterm())) {
                        // merge
                        if(this->ht2root[ht1] != this->ht2root[ht2]) {
                            if(this->ht2root[ht1] == this->emp_ht || this->ht2root[ht2] == this->emp_ht) {
                                heap_term* orig_root1 = this->ht2root[ht1];
                                heap_term* orig_root2 = this->ht2root[ht2];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root1 || item.second == orig_root2) {
                                        this->ht2root[item.first] = this->emp_ht;
                                    }
                                }
                                this->ht2root[ht1] = this->emp_ht;
                                this->ht2root[ht2] = this->emp_ht;
                            } else if(this->ht2root[ht1]->is_atom_pt()) {
                                heap_term* orig_root2 = this->ht2root[ht2];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root2) {
                                        this->ht2root[item.first] = this->ht2root[ht1];
                                    }
                                }
                                this->ht2root[ht2] = this->ht2root[ht1];
                            } else if(this->ht2root[ht2]->is_atom_pt()) {
                                
                                heap_term* orig_root1 = this->ht2root[ht1];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root1) {
                                        this->ht2root[item.first] = this->ht2root[ht2];
                                    }
                                }
                                this->ht2root[ht1] = this->ht2root[ht2];
                            } else {
                                heap_term* orig_root2 = this->ht2root[ht2];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root2) {
                                        this->ht2root[item.first] = this->ht2root[ht1];
                                    }
                                }
                                this->ht2root[ht2] = this->ht2root[ht1];
                            }
                        } else {
                            // do nothing
                        }
                    }
                }
            }
        }
        for(auto item : this->ht2root) {
            this->repre_hts.insert(item.second);
            if(item.second->is_atom_hvar()) {
                this->repre_atoms.insert(item.second);
                this->repre_hvars.insert(item.second);
            } else if(item.second->is_atom_pt()) {
                this->repre_atoms.insert(item.second);
                this->repre_pts.insert(item.second);
            } else {
                
            }
        }
    }



    void formula_encoder::construct_ht2root_from_deducer_disj() {
        std::set<heap_term*> all_must_hold_hterms;
        for(auto eq_p : this->eq_ht_pairs) {
            all_must_hold_hterms.insert(eq_p.first);
            all_must_hold_hterms.insert(eq_p.second);
        }
        for(heap_term* ht1 : this->hts){
            for(heap_term* ht2 : this->hts) {
                if(ht1 != ht2) {
                    // merge equivalent class and remain all uplus term
                    int ht1_index = this->ht2index_map[ht1];
                    int ht2_index = this->ht2index_map[ht2];
                    if(ded->has_shrel(ht1_index, ht2_index) &&
                       ded->has_shrel(ht2_index, ht1_index) &&
                       !(ht1->is_uplus_hterm() || ht2->is_uplus_hterm())) {
                        // merge
                        if(this->ht2root[ht1] != this->ht2root[ht2]) {
                            if(this->ht2root[ht1] == this->emp_ht || this->ht2root[ht2] == this->emp_ht) {
                                heap_term* orig_root1 = this->ht2root[ht1];
                                heap_term* orig_root2 = this->ht2root[ht2];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root1 || item.second == orig_root2) {
                                        this->ht2root[item.first] = this->emp_ht;
                                    }
                                }
                                this->ht2root[ht1] = this->emp_ht;
                                this->ht2root[ht2] = this->emp_ht;
                            } else if(this->ht2root[ht1]->is_atom_pt()) {
                                heap_term* orig_root2 = this->ht2root[ht2];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root2) {
                                        this->ht2root[item.first] = this->ht2root[ht1];
                                    }
                                }
                                this->ht2root[ht2] = this->ht2root[ht1];
                            } else if(this->ht2root[ht2]->is_atom_pt()) {
                                
                                heap_term* orig_root1 = this->ht2root[ht1];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root1) {
                                        this->ht2root[item.first] = this->ht2root[ht2];
                                    }
                                }
                                this->ht2root[ht1] = this->ht2root[ht2];
                            } else {
                                heap_term* orig_root2 = this->ht2root[ht2];
                                for(auto item : this->ht2root) {
                                    if(item.second == orig_root2) {
                                        this->ht2root[item.first] = this->ht2root[ht1];
                                    }
                                }
                                this->ht2root[ht2] = this->ht2root[ht1];
                            }
                        } else {
                            // do nothing
                        }
                    }
                }
            }
        }
        for(auto item : this->ht2root) {
            this->repre_hts.insert(item.second);
            if(item.second->is_atom_hvar()) {
                this->repre_atoms.insert(item.second);
                this->repre_hvars.insert(item.second);
            } else if(item.second->is_atom_pt()) {
                this->repre_atoms.insert(item.second);
                this->repre_pts.insert(item.second);
            } else {
                
            }
        }
    }

    void formula_encoder::construct_ht2root_from_nothing() {

        for(auto item : this->ht2root) {
            this->repre_hts.insert(item.second);
            if(item.second->is_atom_hvar()) {
                this->repre_atoms.insert(item.second);
                this->repre_hvars.insert(item.second);
            } else if(item.second->is_atom_pt()) {
                this->repre_atoms.insert(item.second);
                this->repre_pts.insert(item.second);
            } else {
                
            }
        }
    }

        
    app* formula_encoder::get_shrel_boolvar(heap_term* subht, heap_term* supht) {
        int sub_index = this->ht2index_map[subht];
        int sup_index = this->ht2index_map[supht];

        std::pair<int, int> key = {sub_index, sup_index};
        return this->shrel_var_map[key];
    }

    app* formula_encoder::get_djrel_boolvar(heap_term* firstht, heap_term* secondht) {
        int first_index = this->ht2index_map[firstht];
        int second_index = this->ht2index_map[secondht];

        std::pair<int, int> key = {first_index, second_index};
        return this->djrel_var_map[key];
    }


    std::pair<std::pair<int, int>, bool> formula_encoder::get_boolvar_id_type(app* boolvar) {
        if(this->djrel_var2pair.find(boolvar) != this->djrel_var2pair.end()) {
            return {this->djrel_var2pair[boolvar], false};
        } else if(this->shrel_var2pair.find(boolvar) != this->shrel_var2pair.end()) {
            return {this->shrel_var2pair[boolvar], true};
        } else {
            std::cout << "ERROR: boolvar not found: " << mk_ismt2_pp(boolvar, this->th->get_manager()) << std::endl;
            return {{-1, -1}, false};
        }
    }
    
    app* formula_encoder::locvar2intvar(app* locvar) {
        if(this->locvar2intvar_map.find(locvar) == this->locvar2intvar_map.end()) {
            return nullptr;
        }
        return this->locvar2intvar_map[locvar];
    }


    std::set<heap_term*> formula_encoder::get_sub_atom_hts(heap_term* orig_ht) {
        std::vector<int> ht_atom_vec = orig_ht->get_atomic_count();
        std::set<std::vector<int>> atom_counts;
        for(int i = 0; i < orig_ht->get_vec_size(); i ++) {
            if(ht_atom_vec[i] != 0) {
                std::vector<int> atom_count(orig_ht->get_vec_size(), 0);
                atom_count[i] = 1;
                atom_counts.insert(atom_count);
            }
        }
        // find atoms 
        std::set<heap_term*> result;
        for(std::vector<int> id_vec : atom_counts) {
            for(heap_term* aht : this->atom_hts) {
                if(aht->get_atomic_count() == id_vec) {
                    result.insert(aht);
                    break;
                }
            }
        }
        return result;
    }

    app* formula_encoder::translate_locterm_to_liaterm(app* locterm) {
        arith_util a(this->th->get_manager());
        if(this->th->is_locvar(locterm)) {
            return this->locvar2intvar(locterm);
        } else if(this->th->is_nil(locterm)) {
            return this->syntax_maker->mk_lia_intconst(0);
        } else if(this->th->is_locadd(locterm)){
            SASSERT(locterm->get_num_args() == 2);
            app* arg1 = to_app(locterm->get_arg(0));
            app* arg2 = to_app(locterm->get_arg(1));
            app* first = this->translate_locterm_to_liaterm(arg1);
            app* second = this->translate_locterm_to_liaterm(arg2);
            app* result = a.mk_add(first, second);
            return result;
        } else {
            return locterm;
        }
    }



    expr* formula_encoder::translate_locdata_formula(expr* formula) {
        app* apped_formula = to_app(formula);
        if(apped_formula->is_app_of(basic_family_id, OP_NOT)) {
            app* inner = to_app(apped_formula->get_arg(0));
            expr* inner_translated = this->translate_locdata_formula(inner);
            expr* result = this->syntax_maker->mk_not(inner_translated);
            return result;
        } else if(apped_formula->is_app_of(basic_family_id, OP_DISTINCT)) {
            app* inner_first = to_app(apped_formula->get_arg(0));
            app* inner_second = to_app(apped_formula->get_arg(1));
            app* translated_inner_first = this->translate_locterm_to_liaterm(inner_first);
            app* translated_inner_second = this->translate_locterm_to_liaterm(inner_second);
            expr* result = this->syntax_maker->mk_distinct(translated_inner_first, translated_inner_second);

            return result;
        } else if(apped_formula->is_app_of(basic_family_id, OP_EQ)) {
            app* inner_lhs = to_app(apped_formula->get_arg(0));
            app* inner_rhs = to_app(apped_formula->get_arg(1));
            app* translated_inner_lhs = this->translate_locterm_to_liaterm(inner_lhs);
            app* translated_inner_rhs = this->translate_locterm_to_liaterm(inner_rhs);
            expr* result = this->syntax_maker->mk_eq(translated_inner_lhs, translated_inner_rhs);
            
            return result;
        } else if(this->th->get_manager().is_bool(apped_formula)) {
            // ATTENTION, MAY MISS SITUATIONS
            return formula;
        }
        else {
            std::cout << "UNRESOLVED FORMULA: " << mk_ismt2_pp(formula, this->th->get_manager()) << std::endl;
            return formula;
        }
    }

    expr* formula_encoder::generate_deduced_premises() {
        #ifdef SOLVING_INFO
        std::cout << "generate deduce premises" << std::endl;
        #endif
        if(this->ded->get_is_unsat()) {
            return this->th->get_manager().mk_false();
        }
        expr* result = this->th->get_manager().mk_true();
        for(auto p : this->ded->get_dj_pair_set()) {
            result = this->syntax_maker->mk_and(result, this->djrel_var_map[p]);
        }
        for(auto p : this->ded->get_sh_pair_set()) {
            result = this->syntax_maker->mk_and(result, this->shrel_var_map[p]);
        }
        
        for(auto i : this->ded->get_ldvar2eqroot()) {
            app* translated_first = this->translate_locterm_to_liaterm(i.first);
            app* translated_second = this->translate_locterm_to_liaterm(i.second);
            result = this->syntax_maker->mk_and(result, this->syntax_maker->mk_eq(translated_first, translated_second));
        }
        for(auto i : this->ded->get_ldvar2neqvars()) {
            app* translated_first = this->translate_locterm_to_liaterm(i.first);
            for(auto neq_var : i.second) {
                app* translated_neq_var = this->translate_locterm_to_liaterm(neq_var);
                result = this->syntax_maker->mk_and(
                    result,
                    this->syntax_maker->mk_distinct(translated_first, translated_neq_var)
                );
            }
        }
        return result;
    }

    std::set<expr*> formula_encoder::generate_deduced_assumptions() {
        #ifdef SOLVING_INFO
        std::cout << "generate deduce assumptions" << std::endl;
        #endif
        std::set<expr*> result_ass;
        if(this->ded->get_is_unsat()) {
            result_ass.insert(this->th->get_manager().mk_false());
            return result_ass;
        }
        expr* result = this->th->get_manager().mk_true();
        for(auto p : this->ded->get_dj_pair_set()) {
            result_ass.insert(this->djrel_var_map[p]);
        }
        for(auto p : this->ded->get_sh_pair_set()) {
            result_ass.insert(this->shrel_var_map[p]);
        }
        
        for(auto i : this->ded->get_ldvar2eqroot()) {
            app* translated_first = this->translate_locterm_to_liaterm(i.first);
            app* translated_second = this->translate_locterm_to_liaterm(i.second);
            result_ass.insert(this->syntax_maker->mk_eq(translated_first, translated_second));
        }
        for(auto i : this->ded->get_ldvar2neqvars()) {
            app* translated_first = this->translate_locterm_to_liaterm(i.first);
            for(auto neq_var : i.second) {
                app* translated_neq_var = this->translate_locterm_to_liaterm(neq_var);
                result_ass.insert(this->syntax_maker->mk_distinct(translated_first, translated_neq_var));
            }
        }
        return result_ass;
    }


    std::set<expr*> formula_encoder::generate_deduced_assumptions_disj() {
        std::set<expr*> result_ass;
        if(this->ded->get_is_unsat()) {
            result_ass.insert(this->th->get_manager().mk_false());
            return result_ass;
        }
        expr* result = this->th->get_manager().mk_true();
        for(auto p : this->ded->get_dj_pair_set()) {
            result_ass.insert(this->djrel_var_map[p]);
        }
        for(auto p : this->ded->get_sh_pair_set()) {
            result_ass.insert(this->shrel_var_map[p]);
        }
        
        for(auto i : this->ded->get_ldvar2eqroot()) {
            app* translated_first = this->translate_locterm_to_liaterm(i.first);
            app* translated_second = this->translate_locterm_to_liaterm(i.second);
            result_ass.insert(this->syntax_maker->mk_eq(translated_first, translated_second));
        }
        for(auto i : this->ded->get_ldvar2neqvars()) {
            app* translated_first = this->translate_locterm_to_liaterm(i.first);
            for(auto neq_var : i.second) {
                app* translated_neq_var = this->translate_locterm_to_liaterm(neq_var);
                result_ass.insert(this->syntax_maker->mk_distinct(translated_first, translated_neq_var));
            }
        }
        return result_ass;
    }

    
    expr* formula_encoder::generate_ld_formula() {
        #ifdef SOLVING_INFO
        std::cout << "generate ld formula" << std::endl;
        #endif
        expr* result = this->th->get_manager().mk_true();
        for(app* loc_constraint : this->th->curr_loc_cnstr) {
            expr* translated_loc_constraint =  this->translate_locdata_formula(loc_constraint);
            result = this->syntax_maker->mk_and(result, translated_loc_constraint);
        }
        for(app* data_constraint : this->th->curr_data_cnstr) {
            expr* translated_data_constraint = this->translate_locdata_formula(data_constraint);
            result = this->syntax_maker->mk_and(result, translated_data_constraint);
        }
        return result;
    }

    std::pair<std::set<expr*>, std::set<ld_recov_node*>> formula_encoder::generate_ld_assumptions() {
        #ifdef SOLVING_INFO
        std::cout << "generate ld assumptions" << std::endl;
        #endif
        std::set<expr*> result_ass;
        std::set<ld_recov_node*> recov_nodes;
        for(app* loc_constraint : this->th->curr_loc_cnstr) {
            expr* translated_loc_constraint =  this->translate_locdata_formula(loc_constraint);
            result_ass.insert(translated_loc_constraint);
            ld_recov_node* rec_node = alloc(ld_recov_node, loc_constraint, translated_loc_constraint);
            this->th->mem_mng->push_recov_node_ptr(rec_node);
            recov_nodes.insert(rec_node);
        }
        for(app* data_constraint : this->th->curr_data_cnstr) {
            expr* translated_data_constraint = this->translate_locdata_formula(data_constraint);
            result_ass.insert(translated_data_constraint);
            ld_recov_node* rec_node = alloc(ld_recov_node, data_constraint, translated_data_constraint);
            this->th->mem_mng->push_recov_node_ptr(rec_node);
            recov_nodes.insert(rec_node);
        }
        return {result_ass, recov_nodes};
    }

    expr* formula_encoder::generate_init_formula() {
        #ifdef SOLVING_INFO
        std::cout << "generate init formula" << std::endl;
        #endif
        expr* disj_form = this->th->get_manager().mk_true();
        for(heap_term* uplus_ht : this->repre_hts) {
            if(uplus_ht->is_uplus_hterm()) {
                for(auto vec_pair : uplus_ht->get_all_distinct_atomic_pairs()) {
                    std::pair<heap_term*, heap_term*> htp = this->get_ht_pair_by_vec_pair(vec_pair);
                    std::pair<heap_term*, heap_term*> cand_htp = {this->ht2root[htp.first], this->ht2root[htp.second]};
                    if(!cand_htp.first->is_emp() && !cand_htp.second->is_emp()) {
                        disj_form = this->syntax_maker->mk_and(disj_form, this->get_djrel_boolvar(cand_htp.first, cand_htp.second));
                    }
                }
            }
        }
        
        expr* emp_subsume_form = this->th->get_manager().mk_true();
        for(heap_term* ht : this->repre_hts) {
            emp_subsume_form = this->syntax_maker->mk_and(emp_subsume_form, this->get_shrel_boolvar(this->emp_ht, ht));
        }

        expr* sub_ht_form = this->th->get_manager().mk_true();
        for(heap_term* ht1 : this->repre_hts) {
            for(heap_term* ht2 : this->repre_hts) {
                if(!(ht1->is_emp() || ht2->is_emp()) && ht1->is_subhterm_of(ht2)) {
                    sub_ht_form = this->syntax_maker->mk_and(sub_ht_form, this->get_shrel_boolvar(ht1, ht2));
                }
            }
        }

        expr* eq_induced_subht_form = this->th->get_manager().mk_true();
        for(std::pair<heap_term*, heap_term*> p : this->eq_ht_pairs) {
            std::pair<heap_term*, heap_term*> cand_eqp = {this->ht2root[p.first], this->ht2root[p.second]};
            eq_induced_subht_form = this->syntax_maker->mk_and(
                eq_induced_subht_form,
                this->get_shrel_boolvar(cand_eqp.first, cand_eqp.second),
                this->get_shrel_boolvar(cand_eqp.second, cand_eqp.first)
            );

        }
        expr_ref_vector expr_vec(this->th->get_manager());
        expr_vec.push_back(disj_form);
        expr_vec.push_back(emp_subsume_form);
        expr_vec.push_back(sub_ht_form);
        expr_vec.push_back(eq_induced_subht_form);


        expr* result = this->syntax_maker->mk_and(4, expr_vec.data());

        return result;
    }

    std::set<expr*> formula_encoder::generate_init_assumptions() {
        #ifdef SOLVING_INFO
        std::cout << "generate init formula" << std::endl;
        #endif
        std::set<expr*> result_ass;
        for(heap_term* uplus_ht : this->repre_hts) {
            if(uplus_ht->is_uplus_hterm()) {
                for(auto vec_pair : uplus_ht->get_all_distinct_atomic_pairs()) {
                    std::pair<heap_term*, heap_term*> htp = this->get_ht_pair_by_vec_pair(vec_pair);std::pair<heap_term*, heap_term*> cand_htp = {this->ht2root[htp.first], this->ht2root[htp.second]};
                    if(!cand_htp.first->is_emp() && !cand_htp.second->is_emp()) {
                        result_ass.insert(this->get_djrel_boolvar(cand_htp.first, cand_htp.second));
                    }
                }
            }
        }
        
        for(heap_term* ht : this->repre_hts) {
            result_ass.insert(this->get_shrel_boolvar(this->emp_ht, ht));
        }

        for(heap_term* ht1 : this->repre_hts) {
            for(heap_term* ht2 : this->repre_hts) {
                if(!(ht1->is_emp() || ht2->is_emp()) && ht1->is_subhterm_of(ht2)) {
                    result_ass.insert(this->get_shrel_boolvar(ht1, ht2));
                }
            }
        }
        for(std::pair<heap_term*, heap_term*> p : this->eq_ht_pairs) {
            std::pair<heap_term*, heap_term*> cand_eqp = {this->ht2root[p.first], this->ht2root[p.second]};
            result_ass.insert(this->get_shrel_boolvar(cand_eqp.first, cand_eqp.second));
            result_ass.insert(this->get_shrel_boolvar(cand_eqp.second, cand_eqp.first));
        }

        return result_ass;
    }

    expr* formula_encoder::generate_pto_formula() {
        #ifdef SOLVING_INFO
        std::cout << "generate pto formula" << std::endl;
        #endif
        expr* first_conj = this->th->get_manager().mk_true();
        expr* second_conj = this->th->get_manager().mk_true();
        for(heap_term* pt : this->repre_pts) {
            for(heap_term* ptp : this->repre_pts) {
                int pt_index = this->ht2index_map[pt];
                int ptp_index = this->ht2index_map[ptp];
                std::vector<app*> pt_atom = pt->get_atoms();
                SASSERT(pt_atom.size() == 1);
                app* pt_addr = to_app(pt_atom[0]->get_arg(0));
                app* pt_rcd = to_app(pt_atom[0]->get_arg(1));
                SASSERT(this->th->is_recordterm(pt_rcd));
                app* pt_content = to_app(pt_rcd->get_arg(0));
                
                std::vector<app*> ptp_atom = ptp->get_atoms();
                SASSERT(ptp_atom.size() == 1);
                app* ptp_addr = to_app(ptp_atom[0]->get_arg(0));
                app* ptp_rcd = to_app(ptp_atom[0]->get_arg(1));
                SASSERT(this->th->is_recordterm(pt_rcd));
                app* ptp_content = to_app(ptp_rcd->get_arg(0));

                expr* disj_temp_form = this->syntax_maker->mk_implies(
                    this->get_djrel_boolvar(pt, ptp),
                    this->syntax_maker->mk_not(
                        this->syntax_maker->mk_eq(
                            this->translate_locterm_to_liaterm(pt_addr),
                            this->translate_locterm_to_liaterm(ptp_addr)
                        )
                    )
                );
                expr* content_eq_temp_form = nullptr;
                // ATTENTION: this is commented since the set of address is a subset of data
                // if(ptp_content->get_family_id() == pt_content->get_family_id()) {
                    // std::cout << mk_ismt2_pp(pt_content, this->th->get_manager()) << std::endl;
                    // std::cout << mk_ismt2_pp(ptp_content, this->th->get_manager()) << std::endl;
                    content_eq_temp_form = this->syntax_maker->mk_eq(
                        this->translate_locterm_to_liaterm(pt_content),
                        this->translate_locterm_to_liaterm(ptp_content)
                    );

                // } else {
                //     content_eq_temp_form = this->th->get_manager().mk_false();
                // }
                expr* sh_temp_form = this->syntax_maker->mk_implies(
                    this->get_shrel_boolvar(pt, ptp),
                    this->syntax_maker->mk_and(
                        this->syntax_maker->mk_eq(
                            this->translate_locterm_to_liaterm(pt_addr),
                            this->translate_locterm_to_liaterm(ptp_addr)
                        ),
                        content_eq_temp_form
                    )
                );

                first_conj = this->syntax_maker->mk_and(
                    first_conj,
                    disj_temp_form,
                    sh_temp_form
                );

                for(heap_term* ht : this->repre_hts) {
                    int ht_index = this->ht2index_map[ht];
                    // use deduction results
                    if(this->ded->has_shrel(pt_index, ht_index) && this->ded->has_shrel(ptp_index, ht_index)) {
                        second_conj = this->syntax_maker->mk_and(
                            second_conj,
                            this->syntax_maker->mk_or(
                                this->syntax_maker->mk_and(
                                    this->get_shrel_boolvar(ptp, pt), 
                                    this->get_shrel_boolvar(pt, ptp)
                                ),
                                this->get_djrel_boolvar(pt, ptp)
                            )
                        );
                    }
                    else {
                        second_conj = this->syntax_maker->mk_and(
                            second_conj,
                            this->syntax_maker->mk_implies(
                                this->syntax_maker->mk_and(
                                    this->get_shrel_boolvar(pt, ht),
                                    this->get_shrel_boolvar(ptp, ht)
                                ),
                                this->syntax_maker->mk_or(
                                    this->syntax_maker->mk_and(
                                        this->get_shrel_boolvar(ptp, pt), 
                                        this->get_shrel_boolvar(pt, ptp)
                                    ),
                                    this->get_djrel_boolvar(pt, ptp)
                                )
                            )
                        );
                    }
                }
            }
        }

        expr* result = this->syntax_maker->mk_and(first_conj, second_conj);

        
        return result;
    }


    std::set<expr*> formula_encoder::generate_pto_assumptions() {
        std::set<expr*> result_ass;
        #ifdef SOLVING_INFO
        std::cout << "generate pto formula" << std::endl;
        #endif
        for(heap_term* pt : this->repre_pts) {
            for(heap_term* ptp : this->repre_pts) {
                
                int pt_index = this->ht2index_map[pt];
                int ptp_index = this->ht2index_map[ptp];
                std::vector<app*> pt_atom = pt->get_atoms();
                SASSERT(pt_atom.size() == 1);
                app* pt_addr = to_app(pt_atom[0]->get_arg(0));
                app* pt_rcd = to_app(pt_atom[0]->get_arg(1));
                SASSERT(this->th->is_recordterm(pt_rcd));
                app* pt_content = to_app(pt_rcd->get_arg(0));
                
                std::vector<app*> ptp_atom = ptp->get_atoms();
                SASSERT(ptp_atom.size() == 1);
                app* ptp_addr = to_app(ptp_atom[0]->get_arg(0));
                app* ptp_rcd = to_app(ptp_atom[0]->get_arg(1));
                SASSERT(this->th->is_recordterm(pt_rcd));
                app* ptp_content = to_app(ptp_rcd->get_arg(0));

                expr* disj_temp_form = this->syntax_maker->mk_implies(
                    this->get_djrel_boolvar(pt, ptp),
                    this->syntax_maker->mk_not(
                        this->syntax_maker->mk_eq(
                            this->translate_locterm_to_liaterm(pt_addr),
                            this->translate_locterm_to_liaterm(ptp_addr)
                        )
                    )
                );
                expr* content_eq_temp_form = nullptr;
                // ATTENTION: this is commented since the set of address is a subset of data
                // if(ptp_content->get_family_id() == pt_content->get_family_id()) {
                    // std::cout << mk_ismt2_pp(pt_content, this->th->get_manager()) << std::endl;
                    // std::cout << mk_ismt2_pp(ptp_content, this->th->get_manager()) << std::endl;
                    content_eq_temp_form = this->syntax_maker->mk_eq(
                        this->translate_locterm_to_liaterm(pt_content),
                        this->translate_locterm_to_liaterm(ptp_content)
                    );

                // } else {
                //     content_eq_temp_form = this->th->get_manager().mk_false();
                // }
                expr* sh_temp_form = this->syntax_maker->mk_implies(
                    this->get_shrel_boolvar(pt, ptp),
                    this->syntax_maker->mk_and(
                        this->syntax_maker->mk_eq(
                            this->translate_locterm_to_liaterm(pt_addr),
                            this->translate_locterm_to_liaterm(ptp_addr)
                        ),
                        content_eq_temp_form
                    )
                );
                result_ass.insert(disj_temp_form);
                result_ass.insert(sh_temp_form);

                for(heap_term* ht : this->repre_hts) {
                    int ht_index = this->ht2index_map[ht];
                    // use deduction results
                    if(this->ded->has_shrel(pt_index, ht_index) && this->ded->has_shrel(ptp_index, ht_index)) {
                        result_ass.insert(
                            this->syntax_maker->mk_or(
                                this->syntax_maker->mk_and(
                                    this->get_shrel_boolvar(ptp, pt), 
                                    this->get_shrel_boolvar(pt, ptp)
                                ),
                                this->get_djrel_boolvar(pt, ptp)
                            )
                        );
                    }
                    else {
                        result_ass.insert(
                            this->syntax_maker->mk_implies(
                                this->syntax_maker->mk_and(
                                    this->get_shrel_boolvar(pt, ht),
                                    this->get_shrel_boolvar(ptp, ht)
                                ),
                                this->syntax_maker->mk_or(
                                    this->syntax_maker->mk_and(
                                        this->get_shrel_boolvar(ptp, pt), 
                                        this->get_shrel_boolvar(pt, ptp)
                                    ),
                                    this->get_djrel_boolvar(pt, ptp)
                                )
                            )
                        );
                    }
                }
            }
        }

        
        return result_ass;
    }

    std::set<expr*> formula_encoder::generate_pto_assumptions_disj() {
        std::set<expr*> result_ass;
        #ifdef DISJ_DEBUG
        std::cout << "generate pto formula disj" << std::endl;
        #endif
        for(heap_term* pt : this->repre_pts) {
            for(heap_term* ptp : this->repre_pts) {
                
                int pt_index = this->ht2index_map[pt];
                int ptp_index = this->ht2index_map[ptp];
                std::vector<app*> pt_atom = pt->get_atoms();
                SASSERT(pt_atom.size() == 1);
                app* pt_addr = to_app(pt_atom[0]->get_arg(0));
                app* pt_rcd = to_app(pt_atom[0]->get_arg(1));
                SASSERT(this->th->is_recordterm(pt_rcd));
                app* pt_content = to_app(pt_rcd->get_arg(0));
                
                std::vector<app*> ptp_atom = ptp->get_atoms();
                SASSERT(ptp_atom.size() == 1);
                app* ptp_addr = to_app(ptp_atom[0]->get_arg(0));
                app* ptp_rcd = to_app(ptp_atom[0]->get_arg(1));
                SASSERT(this->th->is_recordterm(pt_rcd));
                app* ptp_content = to_app(ptp_rcd->get_arg(0));

                expr* disj_temp_form = this->syntax_maker->mk_implies(
                    this->get_djrel_boolvar(pt, ptp),
                    this->syntax_maker->mk_not(
                        this->syntax_maker->mk_eq(
                            this->translate_locterm_to_liaterm(pt_addr),
                            this->translate_locterm_to_liaterm(ptp_addr)
                        )
                    )
                );
                expr* content_eq_temp_form = nullptr;
                // ATTENTION: this is commented since the set of address is a subset of data
                // if(ptp_content->get_family_id() == pt_content->get_family_id()) {
                    // std::cout << mk_ismt2_pp(pt_content, this->th->get_manager()) << std::endl;
                    // std::cout << mk_ismt2_pp(ptp_content, this->th->get_manager()) << std::endl;
                    content_eq_temp_form = this->syntax_maker->mk_eq(
                        this->translate_locterm_to_liaterm(pt_content),
                        this->translate_locterm_to_liaterm(ptp_content)
                    );

                // } else {
                //     content_eq_temp_form = this->th->get_manager().mk_false();
                // }
                expr* sh_temp_form = this->syntax_maker->mk_implies(
                    this->get_shrel_boolvar(pt, ptp),
                    this->syntax_maker->mk_and(
                        this->syntax_maker->mk_eq(
                            this->translate_locterm_to_liaterm(pt_addr),
                            this->translate_locterm_to_liaterm(ptp_addr)
                        ),
                        content_eq_temp_form
                    )
                );
                result_ass.insert(disj_temp_form);
                result_ass.insert(sh_temp_form);

                for(heap_term* ht : this->repre_hts) {
                    int ht_index = this->ht2index_map[ht];
                    // use deduction results
                    if(this->ded->has_shrel(pt_index, ht_index) && this->ded->has_shrel(ptp_index, ht_index)) {
                        result_ass.insert(
                            this->syntax_maker->mk_or(
                                this->syntax_maker->mk_and(
                                    this->get_shrel_boolvar(ptp, pt), 
                                    this->get_shrel_boolvar(pt, ptp)
                                ),
                                this->get_djrel_boolvar(pt, ptp)
                            )
                        );
                    }
                    else {
                        result_ass.insert(
                            this->syntax_maker->mk_implies(
                                this->syntax_maker->mk_and(
                                    this->get_shrel_boolvar(pt, ht),
                                    this->get_shrel_boolvar(ptp, ht)
                                ),
                                this->syntax_maker->mk_or(
                                    this->syntax_maker->mk_and(
                                        this->get_shrel_boolvar(ptp, pt), 
                                        this->get_shrel_boolvar(pt, ptp)
                                    ),
                                    this->get_djrel_boolvar(pt, ptp)
                                )
                            )
                        );
                    }
                }
            }
        }
        return result_ass;
    }

    

    expr* formula_encoder::generate_iso_formula() {
        #ifdef SOLVING_INFO
        std::cout << "generate iso formula" << std::endl;
        #endif
        expr* first_conj = this->th->get_manager().mk_true();
        expr* second_conj = this->th->get_manager().mk_true();
        expr* third_conj = this->th->get_manager().mk_true();

        for(heap_term* pt : this->repre_pts) {
            for(heap_term* ht : this->repre_hts) {
                if(ht != this->emp_ht) {
                    int pt_index = this->ht2index_map[pt];
                    int ht_index = this->ht2index_map[ht];
                    // use deduction information
                    bool atom_selected = false;
                    for(heap_term* a : this->get_sub_atom_hts(ht)) {
                        heap_term* cand_a = this->ht2root[a];
                        int a_index = this->ht2index_map[cand_a];
                        if(this->ded->has_shrel(pt_index, a_index)) {
                            atom_selected = true;
                            break;
                        }
                    }
                    if(atom_selected) {
                        continue;
                    }
                    // use deduction information
                    if(this->ded->has_shrel(pt_index, ht_index)) {
                        expr* atom_belonging_disj = this->th->get_manager().mk_false();
                        for(heap_term* a : this->get_sub_atom_hts(ht)) {
                            heap_term* cand_a = this->ht2root[a];
                            atom_belonging_disj = this->syntax_maker->mk_or(atom_belonging_disj, this->get_shrel_boolvar(pt, cand_a));
                        }
                        first_conj = this->syntax_maker->mk_and(
                            first_conj,
                            atom_belonging_disj
                        );
                    } else {
                        expr* first_conj_ipl_lhs = this->get_shrel_boolvar(pt, ht);
                        expr* first_conj_ipl_rhs = this->th->get_manager().mk_false();
                        for(heap_term* a : this->get_sub_atom_hts(ht)) {
                            heap_term* cand_a = this->ht2root[a];
                            first_conj_ipl_rhs = this->syntax_maker->mk_or(first_conj_ipl_rhs, this->get_shrel_boolvar(pt, cand_a));
                        }
                        first_conj = this->syntax_maker->mk_and(
                            first_conj,
                            this->syntax_maker->mk_implies(first_conj_ipl_lhs, first_conj_ipl_rhs)
                        );
                    }
                }
            }
        }

        for(heap_term* ht1 : this->repre_pts) {
            for(heap_term* ht2 : this->repre_hts) {
                for(heap_term* ht3 : this->repre_hts) {
                    int ht1_index = this->ht2index_map[ht1];
                    int ht3_index = this->ht2index_map[ht3];
                    // use deduction
                    if(this->ded->has_shrel(ht1_index, ht3_index)) {
                        continue;
                    }
                    expr* second_conj_ipl_lhs = this->syntax_maker->mk_and(
                        this->get_shrel_boolvar(ht1, ht2),
                        this->get_shrel_boolvar(ht2, ht3)
                    );
                    expr* second_conj_ipl_rhs =  this->get_shrel_boolvar(ht1, ht3);
                    second_conj = this->syntax_maker->mk_and(
                        second_conj, 
                        this->syntax_maker->mk_implies(second_conj_ipl_lhs, second_conj_ipl_rhs)
                    );
                }
            }
        }

        expr* result = this->syntax_maker->mk_and(first_conj, second_conj);

        // expr* result = first_conj;
        return result;
    }

    std::set<expr*> formula_encoder::generate_iso_assumptions() {
        #ifdef SOLVING_INFO
        std::cout << "generate iso formula" << std::endl;
        #endif
        expr* first_conj = this->th->get_manager().mk_true();
        expr* second_conj = this->th->get_manager().mk_true();
        expr* third_conj = this->th->get_manager().mk_true();

        std::set<expr*> result_ass;

        for(heap_term* pt : this->repre_pts) {
            for(heap_term* ht : this->repre_hts) {
                if(ht != this->emp_ht) {
                    int pt_index = this->ht2index_map[pt];
                    int ht_index = this->ht2index_map[ht];
                    // use deduction information
                    bool atom_selected = false;
                    for(heap_term* a : this->get_sub_atom_hts(ht)) {
                        heap_term* cand_a = this->ht2root[a];
                        int a_index = this->ht2index_map[cand_a];
                        if(this->ded->has_shrel(pt_index, a_index)) {
                            atom_selected = true;
                            break;
                        }
                    }
                    if(atom_selected) {
                        continue;
                    }
                    // use deduction information
                    if(this->ded->has_shrel(pt_index, ht_index)) {
                        expr* atom_belonging_disj = this->th->get_manager().mk_false();
                        for(heap_term* a : this->get_sub_atom_hts(ht)) {
                            heap_term* cand_a = this->ht2root[a];
                            atom_belonging_disj = this->syntax_maker->mk_or(atom_belonging_disj, this->get_shrel_boolvar(pt, cand_a));
                        }
                        result_ass.insert(
                            atom_belonging_disj
                        );
                    } else {
                        expr* first_conj_ipl_lhs = this->get_shrel_boolvar(pt, ht);
                        expr* first_conj_ipl_rhs = this->th->get_manager().mk_false();
                        for(heap_term* a : this->get_sub_atom_hts(ht)) {
                            heap_term* cand_a = this->ht2root[a];
                            first_conj_ipl_rhs = this->syntax_maker->mk_or(first_conj_ipl_rhs, this->get_shrel_boolvar(pt, cand_a));
                        }
                        result_ass.insert(
                            this->syntax_maker->mk_implies(first_conj_ipl_lhs, first_conj_ipl_rhs)
                        );
                    }
                }
            }
        }

        for(heap_term* ht1 : this->repre_pts) {
            for(heap_term* ht2 : this->repre_hts) {
                for(heap_term* ht3 : this->repre_hts) {
                    int ht1_index = this->ht2index_map[ht1];
                    int ht3_index = this->ht2index_map[ht3];
                    // use deduction
                    if(this->ded->has_shrel(ht1_index, ht3_index)) {
                        continue;
                    }
                    expr* second_conj_ipl_lhs = this->syntax_maker->mk_and(
                        this->get_shrel_boolvar(ht1, ht2),
                        this->get_shrel_boolvar(ht2, ht3)
                    );
                    expr* second_conj_ipl_rhs =  this->get_shrel_boolvar(ht1, ht3);
                    result_ass.insert(
                        this->syntax_maker->mk_implies(second_conj_ipl_lhs, second_conj_ipl_rhs)
                    );
                }
            }
        }

        return result_ass;
    }


    std::set<expr*> formula_encoder::generate_iso_assumptions_disj() {
        #ifdef DISJ_DEBUG
        std::cout << "generate iso formula disj" << std::endl;
        #endif
        expr* first_conj = this->th->get_manager().mk_true();
        expr* second_conj = this->th->get_manager().mk_true();
        expr* third_conj = this->th->get_manager().mk_true();

        std::set<expr*> result_ass;

        for(heap_term* pt : this->repre_pts) {
            for(heap_term* ht : this->repre_hts) {
                if(ht != this->emp_ht) {
                    int pt_index = this->ht2index_map[pt];
                    int ht_index = this->ht2index_map[ht];
                    // use deduction information
                    bool atom_selected = false;
                    for(heap_term* a : this->get_sub_atom_hts(ht)) {
                        heap_term* cand_a = this->ht2root[a];
                        int a_index = this->ht2index_map[cand_a];
                        if(this->ded->has_shrel(pt_index, a_index)) {
                            atom_selected = true;
                            break;
                        }
                    }
                    if(atom_selected) {
                        continue;
                    }
                    // use deduction information
                    if(this->ded->has_shrel(pt_index, ht_index)) {
                        expr* atom_belonging_disj = this->th->get_manager().mk_false();
                        for(heap_term* a : this->get_sub_atom_hts(ht)) {
                            heap_term* cand_a = this->ht2root[a];
                            atom_belonging_disj = this->syntax_maker->mk_or(atom_belonging_disj, this->get_shrel_boolvar(pt, cand_a));
                        }
                        result_ass.insert(
                            atom_belonging_disj
                        );
                    } else {
                        expr* first_conj_ipl_lhs = this->get_shrel_boolvar(pt, ht);
                        expr* first_conj_ipl_rhs = this->th->get_manager().mk_false();
                        for(heap_term* a : this->get_sub_atom_hts(ht)) {
                            heap_term* cand_a = this->ht2root[a];
                            first_conj_ipl_rhs = this->syntax_maker->mk_or(first_conj_ipl_rhs, this->get_shrel_boolvar(pt, cand_a));
                        }
                        result_ass.insert(
                            this->syntax_maker->mk_implies(first_conj_ipl_lhs, first_conj_ipl_rhs)
                        );
                    }
                }
            }
        }

        for(heap_term* ht1 : this->repre_pts) {
            for(heap_term* ht2 : this->repre_hts) {
                for(heap_term* ht3 : this->repre_hts) {
                    int ht1_index = this->ht2index_map[ht1];
                    int ht3_index = this->ht2index_map[ht3];
                    // use deduction
                    if(this->ded->has_shrel(ht1_index, ht3_index)) {
                        continue;
                    }
                    expr* second_conj_ipl_lhs = this->syntax_maker->mk_and(
                        this->get_shrel_boolvar(ht1, ht2),
                        this->get_shrel_boolvar(ht2, ht3)
                    );
                    expr* second_conj_ipl_rhs =  this->get_shrel_boolvar(ht1, ht3);
                    result_ass.insert(
                        this->syntax_maker->mk_implies(second_conj_ipl_lhs, second_conj_ipl_rhs)
                    );
                }
            }
        }

        return result_ass;
    }

    expr* formula_encoder::generate_idj_formula() {

        #ifdef SOLVING_INFO
        std::cout << "generate idj formula" << std::endl;
        #endif
        expr* result = this->th->get_manager().mk_true();
        for(heap_term* ht1 : this->repre_pts) {
            if(ht1 == this->emp_ht) {continue;}
            for(heap_term* ht2 : this->repre_pts) {
                if(ht2 == this->emp_ht) {continue;}
                int ht1_index = this->ht2index_map[ht1];
                int ht2_index = this->ht2index_map[ht2];
                // use deduction
                if(this->ded->has_djrel(ht1_index, ht2_index)) {
                    continue;
                }
                for(heap_term* ht3 : this->repre_atoms) {
                    if(ht3 == this->emp_ht) {continue;}
                    for(heap_term* ht4 : this->repre_atoms) {
                        if(ht4 == this->emp_ht) {continue;}
                        expr* impl_lhs = this->syntax_maker->mk_and(
                            this->get_shrel_boolvar(ht1, ht3),
                            this->get_shrel_boolvar(ht2, ht4),
                            this->get_djrel_boolvar(ht3, ht4)
                        );
                        expr* impl_rhs = this->get_djrel_boolvar(ht1, ht2);
                        result = this->syntax_maker->mk_and(
                            result,
                            this->syntax_maker->mk_implies(impl_lhs, impl_rhs)
                        );
                    }
                }
            }
        }

        return result;
    }

    std::set<expr*> formula_encoder::generate_idj_assumptions() {

        #ifdef SOLVING_INFO
        std::cout << "generate idj formula" << std::endl;
        #endif
        std::set<expr*> result_ass;
        for(heap_term* ht1 : this->repre_pts) {
            if(ht1 == this->emp_ht) {continue;}
            for(heap_term* ht2 : this->repre_pts) {
                if(ht2 == this->emp_ht) {continue;}
                int ht1_index = this->ht2index_map[ht1];
                int ht2_index = this->ht2index_map[ht2];
                // use deduction
                if(this->ded->has_djrel(ht1_index, ht2_index)) {
                    continue;
                }
                for(heap_term* ht3 : this->repre_atoms) {
                    if(ht3 == this->emp_ht) {continue;}
                    for(heap_term* ht4 : this->repre_atoms) {
                        if(ht4 == this->emp_ht) {continue;}
                        expr* impl_lhs = this->syntax_maker->mk_and(
                            this->get_shrel_boolvar(ht1, ht3),
                            this->get_shrel_boolvar(ht2, ht4),
                            this->get_djrel_boolvar(ht3, ht4)
                        );
                        expr* impl_rhs = this->get_djrel_boolvar(ht1, ht2);
                        result_ass.insert(
                            this->syntax_maker->mk_implies(impl_lhs, impl_rhs)
                        );
                    }
                }
            }
        }

        return result_ass;
    }

    std::set<expr*> formula_encoder::generate_idj_assumptions_disj() {
        #ifdef DISJ_DEBUG
        std::cout << "generate idj formula disj" << std::endl;
        #endif
        std::set<expr*> result_ass;
        for(heap_term* ht1 : this->repre_pts) {
            if(ht1 == this->emp_ht) {continue;}
            for(heap_term* ht2 : this->repre_pts) {
                if(ht2 == this->emp_ht) {continue;}
                int ht1_index = this->ht2index_map[ht1];
                int ht2_index = this->ht2index_map[ht2];
                // use deduction
                if(this->ded->has_djrel(ht1_index, ht2_index)) {
                    continue;
                }
                for(heap_term* ht3 : this->repre_atoms) {
                    if(ht3 == this->emp_ht) {continue;}
                    for(heap_term* ht4 : this->repre_atoms) {
                        if(ht4 == this->emp_ht) {continue;}
                        expr* impl_lhs = this->syntax_maker->mk_and(
                            this->get_shrel_boolvar(ht1, ht3),
                            this->get_shrel_boolvar(ht2, ht4),
                            this->get_djrel_boolvar(ht3, ht4)
                        );
                        expr* impl_rhs = this->get_djrel_boolvar(ht1, ht2);
                        result_ass.insert(
                            this->syntax_maker->mk_implies(impl_lhs, impl_rhs)
                        );
                    }
                }
            }
        }

        return result_ass;
    }

    expr* formula_encoder::generate_final_formula() {


        #ifdef SOLVING_INFO
        std::cout << "generate final formula" << std::endl;
        #endif

        expr* result = this->th->get_manager().mk_true();
        for(heap_term* pt : this->pt_hts) {
            result = this->syntax_maker->mk_and(
                result,
                this->syntax_maker->mk_not(this->get_shrel_boolvar(pt, this->emp_ht))
            );
        }

        return result;
    }

    std::set<expr*> formula_encoder::generate_final_assumptions() {
        std::set<expr*> result_ass;
        for(heap_term* pt : this->pt_hts) {
            result_ass.insert(
                this->syntax_maker->mk_not(this->get_shrel_boolvar(pt, this->emp_ht))
            );
        }
        return result_ass;
    }


    std::set<expr*> formula_encoder::generate_final_assumptions_disj(){
        #ifdef DISJ_DEBUG
        std::cout << "generate final assumptions disj" << std::endl;
        #endif
        std::set<expr*> result_ass;
        for(heap_term* pt : this->pt_hts) {
            result_ass.insert(
                this->syntax_maker->mk_not(this->get_shrel_boolvar(pt, this->emp_ht))
            );
        }
        return result_ass;
    }

    expr* formula_encoder::generate_loc_var_constraints() {
        // generate locvar constraints
        std::cout << "generate loc var constraints" << std::endl;
        expr* result = this->th->get_manager().mk_true();
        arith_util a(this->th->get_manager());
        for(auto item : this->locvar2intvar_map) {
            SASSERT(this->th->is_locvar(item.first));
            if(this->th->is_nil(item.first)) {
                result = this->syntax_maker->mk_and(
                    result,
                    a.mk_eq(item.second, a.mk_int(0))
                );
            } else {
                result = this->syntax_maker->mk_and(
                    result,
                    a.mk_ge(item.second, a.mk_int(0))
                );
            }
        }
        for(app* curr_pt : this->th->curr_pts) {
            app* addr = to_app(curr_pt->get_arg(0));
            SASSERT(this->th->is_locvar(addr));
            result = this->syntax_maker->mk_and(
                result,
                this->syntax_maker->mk_distinct(this->locvar2intvar(addr), a.mk_int(0))
            );
        }
        return result;
    }

    std::pair<expr*, expr_ref_vector> formula_encoder::encode() {

        #ifdef SOLVING_INFO
        std::cout << "==== begin encode" << std::endl;
        #endif
        expr_ref_vector assumptions(this->th->get_manager());
        expr_ref_vector all_conj(this->th->get_manager());

        expr* deduced_result = this->generate_deduced_premises();        
        all_conj.push_back(deduced_result);
        expr* ld_result = this->generate_ld_formula();
        all_conj.push_back(ld_result);
        // all_conj.push_back(this->generate_init_formula());
        all_conj.push_back(this->generate_pto_formula());
        all_conj.push_back(this->generate_iso_formula());
        all_conj.push_back(this->generate_idj_formula());

        all_conj.push_back(this->generate_final_formula());
        all_conj.push_back(this->generate_loc_var_constraints());
        expr* result = this->syntax_maker->mk_and(
            all_conj.size(),
            all_conj.data()
        );

        #ifdef SOLVING_INFO
        std::cout << "==== end encode" << std::endl;
        #endif
        return {result, assumptions};
    }


    std::pair<expr*, expr_ref_vector> formula_encoder::encode_with_ass() {
        expr_ref_vector v(this->th->get_manager());
        std::set<expr*> asses;
        expr* formula = this->th->get_manager().mk_true();
        asses = slhv_util::setUnion(asses, this->generate_deduced_assumptions());
        auto ld_assumptions = this->generate_ld_assumptions();
        this->th->ld_recovery = ld_assumptions.second;
        asses = slhv_util::setUnion(asses, ld_assumptions.first);
        asses = slhv_util::setUnion(asses, this->generate_pto_assumptions());
        asses = slhv_util::setUnion(asses, this->generate_iso_assumptions());
        asses = slhv_util::setUnion(asses, this->generate_idj_assumptions());
        asses = slhv_util::setUnion(asses, this->generate_final_assumptions());
        for(expr* e : asses) {
            v.push_back(e);
        }
        formula = this->syntax_maker->mk_and(formula, this->generate_loc_var_constraints());
        return {formula, v};
    }


    std::set<expr*> formula_encoder::encode_for_disj() {
        #ifdef DISJ_DEBUG
        std::cout << "encode for disj" << std::endl;
        #endif
        std::set<expr*> result;
        result = slhv_util::setUnion(result, this->generate_init_ld_locvar_constraint_for_all_assertions());
        #ifdef DISJ_DEBUG
        std::cout << "generate_deduced_assumptions" << std::endl;
        #endif
        result = slhv_util::setUnion(result, this->generate_deduced_assumptions_disj());
        #ifdef DISJ_DEBUG
        std::cout << "generate_pto_assumptions" << std::endl;
        #endif
        result = slhv_util::setUnion(result, this->generate_pto_assumptions_disj());
        #ifdef DISJ_DEBUG
        std::cout << "generate_iso_assumptions" << std::endl;
        #endif
        result = slhv_util::setUnion(result, this->generate_iso_assumptions_disj());
        #ifdef DISJ_DEBUG
        std::cout << "generate_idj_assumptions" << std::endl;
        #endif
        result = slhv_util::setUnion(result, this->generate_idj_assumptions_disj());
        #ifdef DISJ_DEBUG
        std::cout << "generate_final_assumptions" << std::endl;
        #endif
        result = slhv_util::setUnion(result, this->generate_final_assumptions_disj());
        #ifdef DISJ_DEBUG
        std::cout << "encode for disj end" << std::endl;
        #endif
        return result;
    }


    std::set<expr*> formula_encoder::generate_init_ld_locvar_constraint_for_all_assertions() {
        #ifdef DISJ_DEBUG
        std::cout << "generate_init_ld_locvar_constraint_for_all_assertions" << std::endl;
        #endif
        std::set<expr*> result;
        std::set<app*> collected_locvars;
        arith_util a(this->th->get_manager());
        for(app* refined_assertion : this->th->refined_asssertions_disj) {
            collected_locvars = slhv_util::setUnion(collected_locvars, this->collect_locvars_recursive(refined_assertion));
        }
        expr_ref_vector locvar_ge_0_constraints(this->th->get_manager());
        for(app* lv : collected_locvars) {
            locvar_ge_0_constraints.push_back(
                a.mk_ge(this->translate_locterm_to_liaterm(lv), a.mk_int(0))
            );
        }
        expr* loc_ge_constraint = this->syntax_maker->mk_and(locvar_ge_0_constraints.size(), locvar_ge_0_constraints.data());
        result.insert(loc_ge_constraint);

        for(app* refined_assertion : this->th->refined_asssertions_disj) {
            result.insert(this->generate_init_ld_locvar_constraint_recursive(refined_assertion));
        }

        #ifdef DISJ_DEBUG
        std::cout << "generate_init_ld_locvar_constraint_for_all_assertions end" << std::endl;
        #endif
        return result;
    }
    
    
    expr* formula_encoder::generate_init_ld_locvar_constraint_recursive(app* assertion) {
        #ifdef DISJ_DEBUG
        std::cout << "generate_init_ld_locvar_constraint_recursive " << mk_ismt2_pp(assertion, this->th->get_manager()) << std::endl;
        #endif
        arith_util a(this->th->get_manager());
        if(assertion->is_app_of(basic_family_id, OP_OR)) {
            if(assertion->get_num_args() == 2) {
                expr* fresh_bool = this->syntax_maker->mk_fresh_boolvar();
                expr* fresh_bool_neg = this->syntax_maker->mk_not(fresh_bool);
                app* first_apped_arg = to_app(assertion->get_arg(0));
                app* second_apped_arg = to_app(assertion->get_arg(1));
                expr* first_generated = this->generate_init_ld_locvar_constraint_recursive(first_apped_arg);
                expr* second_generated = this->generate_init_ld_locvar_constraint_recursive(second_apped_arg);
                return this->syntax_maker->mk_or(
                    this->syntax_maker->mk_and(first_generated, fresh_bool),
                    this->syntax_maker->mk_and(second_generated, fresh_bool_neg)
                );
            } else {
                app* branch_intvar = this->syntax_maker->mk_fresh_datavar();
                expr_ref_vector disjuncts(this->th->get_manager());
                for(int i = 0; i < assertion->get_num_args(); i++) {
                    expr* ith_generated = this->generate_init_ld_locvar_constraint_recursive(to_app(assertion->get_arg(i)));
                    disjuncts.push_back(
                        this->syntax_maker->mk_and(
                            this->syntax_maker->mk_eq(branch_intvar, a.mk_int(i)),
                            ith_generated
                        )
                    );
                }
                
                return this->syntax_maker->mk_or(disjuncts.size(), disjuncts.data());
            }
        } else if(assertion->is_app_of(basic_family_id, OP_AND)) {
            expr_ref_vector all_conjuncts(this->th->get_manager());
            for(int i = 0; i < assertion->get_num_args(); i ++) {
                all_conjuncts.push_back(this->generate_init_ld_locvar_constraint_recursive(to_app(assertion->get_arg(i))));
            }
            return this->syntax_maker->mk_and(all_conjuncts.size(), all_conjuncts.data());
        } else if(assertion->is_app_of(basic_family_id, OP_NOT)) {
            app* inner = to_app(assertion->get_arg(0));
            if(inner->is_app_of(basic_family_id, OP_EQ)) {
                if(this->th->is_heapterm(to_app(inner->get_arg(0)))) {
                    std::cout << "ERROR: heq negation !!!!!" << mk_ismt2_pp(assertion, this->th->get_manager()) << std::endl;
                    return nullptr;
                }
            }
            return this->translate_locdata_formula(assertion);
        } else if(assertion->is_app_of(basic_family_id, OP_EQ)) {
            app* first_arg = to_app(assertion->get_arg(0));
            if(this->th->is_heapterm(first_arg)) {
                return this->generate_init_ld_locvar_constraint_for_hteq(assertion);
            } else {
                return this->translate_locdata_formula(assertion);
            }
        } else if(assertion->is_app_of(basic_family_id, OP_DISTINCT)) {
            return this->translate_locdata_formula(assertion);
        } else if(this->th->is_subh(assertion) || this->th->is_disjh(assertion)) {
            return this->generate_init_ld_locvar_constraint_for_subht_disjht(assertion);
        } 
        else if(this->th->get_manager().is_bool(assertion)) {
            // ATTENTION: MAY MISS SITUATIONS
            return this->translate_locdata_formula(assertion);
        }
        else {
            std::cout << "disj encoding: unresolved formula " << mk_ismt2_pp(assertion, this->th->get_manager()) << std::endl;
            return nullptr;
        }
    }

    expr* formula_encoder::generate_init_ld_locvar_constraint_for_hteq(app* heq) {

        #ifdef DISJ_DEBUG
        std::cout << "generate_init_ld_locvar_constraint_for_hteq " << mk_ismt2_pp(heq, this->th->get_manager()) << std::endl;
        #endif
        arith_util a(this->th->get_manager());
        // pt addr constraint
        std::set<app*> collected_pts = this->collect_hteq_all_pts(heq);
        expr_ref_vector ptaddr_neq_0_constraints(this->th->get_manager());
        for(app* ptterm : collected_pts) {
            app* addr = to_app(ptterm->get_arg(0));
            ptaddr_neq_0_constraints.push_back(
                this->syntax_maker->mk_distinct(this->translate_locterm_to_liaterm(addr), a.mk_int(0))
            );
        }
        expr* ptaddr_neq_0_constraint = this->syntax_maker->mk_and(ptaddr_neq_0_constraints.size(), ptaddr_neq_0_constraints.data());

        // =========== init relation constraint
        expr_ref_vector init_shdj_rel_of_hteq(this->th->get_manager());
        // left right subsumption
        app* lhs_orig_ht = to_app(heq->get_arg(0));
        app* rhs_orig_ht = to_app(heq->get_arg(1));

        heap_term* lhs_cand_heapterm = this->find_heap_term_for_ht_disj(lhs_orig_ht);
        heap_term* rhs_cand_heapterm = this->find_heap_term_for_ht_disj(rhs_orig_ht);
        init_shdj_rel_of_hteq.push_back(this->get_shrel_boolvar(lhs_cand_heapterm, rhs_cand_heapterm));
        init_shdj_rel_of_hteq.push_back(this->get_shrel_boolvar(rhs_cand_heapterm, lhs_cand_heapterm));

        // atoms subsumption
        std::vector<app*> lhs_orig_atomic_hts;
        std::vector<app*> rhs_orig_atomic_hts;

        if(this->th->is_atom_hterm(lhs_orig_ht)) {
            lhs_orig_atomic_hts.push_back(lhs_orig_ht);
        } else {
            for(int i = 0; i < lhs_orig_ht->get_num_args(); i ++) {
                lhs_orig_atomic_hts.push_back(to_app(lhs_orig_ht->get_arg(i)));
            }
        }

        if(this->th->is_atom_hterm(rhs_orig_ht)) {
            rhs_orig_atomic_hts.push_back(rhs_orig_ht);
        } else {
            for(int i = 0; i < rhs_orig_ht->get_num_args(); i ++) {
                rhs_orig_atomic_hts.push_back(to_app(rhs_orig_ht->get_arg(i)));
            }
        }
        for(int i = 0; i < lhs_orig_atomic_hts.size(); i ++) {
            heap_term* cand_aheapterm = this->find_heap_term_for_ht_disj(lhs_orig_atomic_hts[i]);
            init_shdj_rel_of_hteq.push_back(
                this->get_shrel_boolvar(cand_aheapterm, lhs_cand_heapterm)
            );
        }
        for(int i = 0; i < rhs_orig_atomic_hts.size(); i ++) {
            heap_term* cand_aheapterm = this->find_heap_term_for_ht_disj(rhs_orig_atomic_hts[i]);
            init_shdj_rel_of_hteq.push_back(
                this->get_shrel_boolvar(cand_aheapterm, rhs_cand_heapterm)
            );
        }

        // compound dj
        for(int i = 0; i < lhs_orig_atomic_hts.size(); i ++) {
            for(int j = 0; j < lhs_orig_atomic_hts.size(); j ++) {
                if(i != j) {
                    heap_term* cand_ahti = this->find_heap_term_for_ht_disj(lhs_orig_atomic_hts[i]);
                    heap_term* cand_ahtj = this->find_heap_term_for_ht_disj(lhs_orig_atomic_hts[j]);
                    if(cand_ahti->is_emp() || cand_ahtj->is_emp()) {
                        continue;
                    }
                    init_shdj_rel_of_hteq.push_back(
                        this->get_djrel_boolvar(cand_ahti, cand_ahtj)
                    );
                    init_shdj_rel_of_hteq.push_back(
                        this->get_djrel_boolvar(cand_ahtj, cand_ahti)
                    );
                }
            }
        }
        for(int i = 0; i < rhs_orig_atomic_hts.size(); i ++) {
            for(int j = 0; j < rhs_orig_atomic_hts.size(); j ++) {
                if(i != j) {
                    heap_term* cand_ahti = this->find_heap_term_for_ht_disj(rhs_orig_atomic_hts[i]);
                    heap_term* cand_ahtj = this->find_heap_term_for_ht_disj(rhs_orig_atomic_hts[j]);
                    if(cand_ahti->is_emp() || cand_ahtj->is_emp()) {
                        continue;
                    }
                    init_shdj_rel_of_hteq.push_back(
                        this->get_djrel_boolvar(cand_ahti, cand_ahtj)
                    );
                    init_shdj_rel_of_hteq.push_back(
                        this->get_djrel_boolvar(cand_ahtj, cand_ahti)
                    );
                }
            }
        }
        expr* init_shdj_constraint_for_hteq = this->syntax_maker->mk_and(init_shdj_rel_of_hteq.size(), init_shdj_rel_of_hteq.data());
        expr* result = this->syntax_maker->mk_and(ptaddr_neq_0_constraint, init_shdj_constraint_for_hteq);
        return result;
    }


    expr* formula_encoder::generate_init_ld_locvar_constraint_for_subht_disjht(app* subdjht) {
        if(!(this->th->is_subh(subdjht) || this->th->is_disjh(subdjht))) {
            std::cout << "wrong app type for subh and disjh" << std::endl;
            return nullptr;
        } else {
            app* lhs_arg = to_app(subdjht->get_arg(0));
            app* rhs_arg = to_app(subdjht->get_arg(1));
            heap_term* lhs_hterm = this->find_heap_term_for_ht_disj(lhs_arg);
            heap_term* rhs_hterm = this->find_heap_term_for_ht_disj(rhs_arg);
            if(this->th->is_subh(subdjht)) {
                return this->get_shrel_boolvar(lhs_hterm, rhs_hterm);
            } else {
                expr_ref_vector init_shdj_rel_of_disjht(this->th->get_manager());
                init_shdj_rel_of_disjht.push_back(this->get_djrel_boolvar(lhs_hterm, rhs_hterm));
                init_shdj_rel_of_disjht.push_back(this->get_djrel_boolvar(rhs_hterm, lhs_hterm));
                return this->syntax_maker->mk_and(2, init_shdj_rel_of_disjht.data());
            }
        }
    }

    heap_term* formula_encoder::find_heap_term_for_ht_disj(app* orig_ht) {
        // DISJ method, obtain heap_term from app
        std::vector<int> atomic_count(this->th->atomic_hterms_disj.size(), 0);
        if(this->th->is_atom_hterm(orig_ht)) {
            for(int i = 0; i < this->th->atomic_hterms_disj.size(); i ++) {
                if(orig_ht == this->th->atomic_hterms_disj[i]) {
                    atomic_count[i] = 1;
                    break;
                }
            }
            for(heap_term* ht : this->hts) {
                if(ht->get_atomic_count() == atomic_count) {
                    return this->ht2root[ht];
                } 
            }
            std::cout << "ERROR: error finding heap term for ht" << std::endl;
            return nullptr;
        } else if(this->th->is_uplus(orig_ht)) {
            std::set<app*> uplus_atoms;
            for(int i = 0; i < orig_ht->get_num_args(); i ++) {
                bool found = false;
                for(int j = 0; j < this->th->atomic_hterms_disj.size(); j ++) {
                    if(to_app(orig_ht->get_arg(i)) == this->th->atomic_hterms_disj[j]) {
                        found = true;
                        atomic_count[j] += 1;
                        break;
                    }
                }
                if(!found) {
                    std::cout << "ERROR: error1 finding heap term for uplus ht" << mk_ismt2_pp(orig_ht->get_arg(i), this->th->get_manager()) << std::endl;
                }
            }
            
            for(heap_term* ht : this->hts) {
                if(ht->get_atomic_count() == atomic_count) {
                    return this->ht2root[ht];
                } 
            }
            std::cout << "ERROR: error2 finding heap term for uplus ht" << std::endl;
            return nullptr;
        } else {
            return nullptr;
            std::cout << "unknown ht in finding heap term" << std::endl;
        }
    }

    std::set<app*> formula_encoder::collect_locvars_recursive(app* term) {
        std::set<app*> locvar_result;
        if(this->th->is_locvar(term)) {
            locvar_result.insert(term);
            return locvar_result;
        } else {
            if(term->get_num_args() == 0) {
                return locvar_result;
            } else {
                for(int i = 0; i < term->get_num_args(); i ++) {
                    std::set<app*> temp_result = this->collect_locvars_recursive(to_app(term->get_arg(i)));
                    locvar_result = slhv_util::setUnion(locvar_result, temp_result);
                }
                return locvar_result;
            }
        }
    }


    std::set<app*> formula_encoder::collect_hteq_all_pts(app* hteq) {
        SASSERT(hteq->is_app_of(basic_family_id, OP_EQ));
        app* arg1 = to_app(hteq->get_arg(0));
        app* arg2 = to_app(hteq->get_arg(1));
        std::set<app*> hteq_pts;
        if(this->th->is_points_to(arg1)) {
            hteq_pts.insert(arg1);
        } else if(this->th->is_hvar(arg1)) {
            // Do nothing
        } else if(this->th->is_uplus(arg1)) {
            for(int i = 0; i < arg1->get_num_args(); i ++) {
                app* apped_arg = to_app(arg1->get_arg(i));
                if(this->th->is_points_to(apped_arg)) {
                    hteq_pts.insert(apped_arg);
                }
            }
        } else if(this->th->is_emp(arg1)) {
            // Do nothing
        }
        else {
            std::cout << "ERROR: unknown hterm in collect hteq pt" << std::endl;
        }

        if(this->th->is_points_to(arg2)) {
            hteq_pts.insert(arg2);
        } else if(this->th->is_hvar(arg2)) {
            // Do nothing
        } else if(this->th->is_uplus(arg2)) {
            for(int i = 0; i < arg2->get_num_args(); i ++) {
                app* apped_arg = to_app(arg2->get_arg(i));
                if(this->th->is_points_to(apped_arg)) {
                    hteq_pts.insert(apped_arg);
                }
            }
        } else if(this->th->is_emp(arg2)) {
            // Do nothing
        } else {
            std::cout << "ERROR: unknown hterm in collect hteq pt" << std::endl;
        }

        return hteq_pts;
    }


    std::pair<heap_term*, heap_term*> formula_encoder::get_ht_pair_by_vec_pair(std::pair<std::vector<int>, std::vector<int>> vec_pair) {
        heap_term* first_ht = nullptr;
        heap_term* second_ht = nullptr;
        for(heap_term* ht : this->hts) {
            if(ht->get_atomic_count() == vec_pair.first) {
                SASSERT(first_ht == nullptr);
                first_ht = ht;
            }
            if(ht->get_atomic_count() == vec_pair.second) {
                SASSERT(second_ht == nullptr);
                second_ht = ht;
            }
            if(first_ht != nullptr && second_ht != nullptr) {
                break;
            }
        }
        return {first_ht, second_ht};
    }


    // deducer

    bool slhv_deducer::insert_sh_pair(std::pair<int, int> sh_pair, std::set<std::pair<int, int>>& nxt_sh_pair_set, std::map<int, std::set<std::pair<int, int>>>& nxt_sh_1nd_elem_map, std::map<int, std::set<std::pair<int, int>>>& nxt_sh_2nd_elem_map) {

        bool result = nxt_sh_pair_set.insert(sh_pair).second;
        if(result) {
            if(nxt_sh_1nd_elem_map.find(sh_pair.first) != nxt_sh_1nd_elem_map.end()) {
                nxt_sh_1nd_elem_map[sh_pair.first].insert(sh_pair);
            } else {
                std::set<std::pair<int, int>> new_pair_set;
                new_pair_set.insert(sh_pair);
                nxt_sh_1nd_elem_map[sh_pair.first] = new_pair_set;
            }
            if(nxt_sh_2nd_elem_map.find(sh_pair.second) != nxt_sh_2nd_elem_map.end()) {
                nxt_sh_2nd_elem_map[sh_pair.second].insert(sh_pair);
            } else {
                std::set<std::pair<int, int>> new_pair_set;
                new_pair_set.insert(sh_pair);
                nxt_sh_2nd_elem_map[sh_pair.second] = new_pair_set;
            }
        }
        return result;
    }

    bool slhv_deducer::insert_dj_pair(std::pair<int, int> dj_pair, std::set<std::pair<int, int>>& nxt_dj_pair_set, std::map<int, std::set<std::pair<int, int>>>& nxt_dj_1nd_elem_map, std::map<int, std::set<std::pair<int, int>>>& nxt_dj_2nd_elem_map) {
        bool result = nxt_dj_pair_set.insert(dj_pair).second;
        if(result) {
            if(nxt_dj_1nd_elem_map.find(dj_pair.first) != nxt_dj_1nd_elem_map.end()) {
                nxt_dj_1nd_elem_map[dj_pair.first].insert(dj_pair);
            } else {
                std::set<std::pair<int, int>> new_pair_set;
                new_pair_set.insert(dj_pair);
                nxt_dj_1nd_elem_map[dj_pair.first] = new_pair_set;
            }
            if(nxt_dj_2nd_elem_map.find(dj_pair.second) != nxt_dj_2nd_elem_map.end()) {
                nxt_dj_2nd_elem_map[dj_pair.second].insert(dj_pair);
            } else {
                std::set<std::pair<int, int>> new_pair_set;
                new_pair_set.insert(dj_pair);
                nxt_dj_2nd_elem_map[dj_pair.second] = new_pair_set;
            }
        }
        return result;
    }

    bool slhv_deducer::insert_sh_pair(std::pair<int, int> sh_pair) {
        return this->insert_sh_pair(sh_pair, this->shpair_set, this->sh_pair_1st_elem_map, this->sh_pair_2nd_elem_map);
    }

    bool slhv_deducer::insert_dj_pair(std::pair<int, int> dj_pair) {
        return this->insert_dj_pair(dj_pair, this->djpair_set, this->dj_pair_1st_elem_map, this->dj_pair_2nd_elem_map);
    }

    void slhv_deducer::initialize_shdj() {
        // RULE P2 and P3
        SASSERT(fec != nullptr);
        std::set<heap_term*> all_hterms = this->fec->get_all_hterms();
        std::set<std::pair<heap_term*, heap_term*>> all_eq_pairs = this->fec->get_eq_ht_pairs();
        for(auto p : all_eq_pairs) {
            this->insert_sh_pair({this->ht2index[p.first], this->ht2index[p.second]});
            this->insert_sh_pair({this->ht2index[p.second], this->ht2index[p.first]});
            // inference graph update
            this->th->infer_graph->add_sh_rel_pair({this->ht2index[p.first], this->ht2index[p.second]}, p);
            this->th->infer_graph->add_sh_rel_pair({this->ht2index[p.second], this->ht2index[p.first]}, p);
        }
        heap_term* emp_ht = this->fec->get_emp_ht();
        for(heap_term* ht : all_hterms) {
            this->insert_sh_pair({this->ht2index[emp_ht], this->ht2index[ht]});
            // inference graph update
            this->th->infer_graph->add_isolated_sh_rel_pair({this->ht2index[emp_ht], this->ht2index[ht]});
        }
        for(heap_term* ht1 : all_hterms) {
            for(heap_term* ht2 : all_hterms) {
                if(ht1->is_subhterm_of(ht2)) {
                    this->insert_sh_pair({this->ht2index[ht1], this->ht2index[ht2]});
                    // inference graph update
                    if(!(ht2->is_atom_hvar() || ht2->is_atom_pt() || ht2->is_emp())) {
                        this->th->infer_graph->add_sh_rel_pair({this->ht2index[ht1], this->ht2index[ht2]}, ht2);
                    } else {
                        this->th->infer_graph->add_isolated_sh_rel_pair({this->ht2index[ht1], this->ht2index[ht2]});
                    }
                }
            }
        }
        for(heap_term* ht : all_hterms) {
            if(!(ht->is_atom_hvar() || ht->is_atom_pt())) {
                auto pset = ht->get_all_distinct_atomic_pairs();
                for(auto pair : pset) {
                    auto ht_pair = this->fec->get_ht_pair_by_vec_pair(pair);
                    if(!ht_pair.first->is_emp() && !ht_pair.second->is_emp()) { 
                        this->insert_dj_pair({this->ht2index[ht_pair.first], this->ht2index[ht_pair.second]});
                        this->insert_dj_pair({this->ht2index[ht_pair.second], this->ht2index[ht_pair.first]});
                        // inference graph update
                        this->th->infer_graph->add_disj_rel_pair({this->ht2index[ht_pair.first], this->ht2index[ht_pair.second]}, ht);
                        this->th->infer_graph->add_disj_rel_pair({this->ht2index[ht_pair.second], this->ht2index[ht_pair.first]}, ht);
                    }
                }
            }
        }
    }

    void slhv_deducer::initialize_shdj_disj() {
        // RULE P2 and P3
        SASSERT(fec != nullptr);
        std::set<heap_term*> all_must_hold_hterms;
        std::set<std::pair<heap_term*, heap_term*>> all_eq_pairs = this->fec->get_eq_ht_pairs();
        std::set<std::pair<heap_term*, heap_term*>> subht_pairs = this->fec->get_subht_pairs();
        std::set<std::pair<heap_term*, heap_term*>> disjht_pairs = this->fec->get_disjht_pairs();
        // all must hold hterms are used to denote uplus hts such that the disjoint relation induced by them is added to the graph globally
        for(auto p : all_eq_pairs) {
            all_must_hold_hterms.insert(p.first);
            all_must_hold_hterms.insert(p.second);
        }
        for(auto p : subht_pairs) {
            all_must_hold_hterms.insert(p.first);
            all_must_hold_hterms.insert(p.second);
        }
        for(auto p : disjht_pairs) {
            all_must_hold_hterms.insert(p.first);
            all_must_hold_hterms.insert(p.second);
        }
        for(auto p : all_eq_pairs) {
            this->insert_sh_pair({this->ht2index[p.first], this->ht2index[p.second]});
            this->insert_sh_pair({this->ht2index[p.second], this->ht2index[p.first]});
            // inference graph update
            this->th->infer_graph->add_sh_rel_pair({this->ht2index[p.first], this->ht2index[p.second]}, p);
            this->th->infer_graph->add_sh_rel_pair({this->ht2index[p.second], this->ht2index[p.first]}, p);
        }
        for(auto p : subht_pairs) {
            this->insert_sh_pair({this->ht2index[p.first], this->ht2index[p.second]});
            // inference graph update
            this->th->infer_graph->add_sh_rel_pair_subht({this->ht2index[p.first], this->ht2index[p.second]}, p);
        }
        for(auto p : disjht_pairs) {
            this->insert_dj_pair({this->ht2index[p.first], this->ht2index[p.second]});
            this->insert_dj_pair({this->ht2index[p.second], this->ht2index[p.first]});
            this->th->infer_graph->add_disj_rel_pair_disjht({this->ht2index[p.first], this->ht2index[p.second]}, p);
            this->th->infer_graph->add_disj_rel_pair_disjht({this->ht2index[p.second], this->ht2index[p.first]}, p);
        }
        heap_term* emp_ht = this->fec->get_emp_ht();
        for(heap_term* ht : all_must_hold_hterms) {
            this->insert_sh_pair({this->ht2index[emp_ht], this->ht2index[ht]});
            // inference graph update
            this->th->infer_graph->add_isolated_sh_rel_pair({this->ht2index[emp_ht], this->ht2index[ht]});
        }
        for(heap_term* ht1 : this->fec->get_all_hterms()) {
            for(heap_term* ht2 : all_must_hold_hterms) {
                if(ht1->is_subhterm_of(ht2)) {
                    this->insert_sh_pair({this->ht2index[ht1], this->ht2index[ht2]});
                    // inference graph update
                    if(!(ht2->is_atom_hvar() || ht2->is_atom_pt() || ht2->is_emp())) {
                        if(this->th->infer_graph->contain_comht_node(ht2)) {
                            this->th->infer_graph->add_sh_rel_pair({this->ht2index[ht1], this->ht2index[ht2]}, ht2);
                        }
                    } else {
                        this->th->infer_graph->add_isolated_sh_rel_pair({this->ht2index[ht1], this->ht2index[ht2]});
                    }
                }
            }
        }
        for(heap_term* ht : all_must_hold_hterms) {
            if(!(ht->is_atom_hvar() || ht->is_atom_pt())) {
                auto pset = ht->get_all_distinct_atomic_pairs();
                for(auto pair : pset) {
                    auto ht_pair = this->fec->get_ht_pair_by_vec_pair(pair);
                    if(!ht_pair.first->is_emp() && !ht_pair.second->is_emp()) { 
                        this->insert_dj_pair({this->ht2index[ht_pair.first], this->ht2index[ht_pair.second]});
                        this->insert_dj_pair({this->ht2index[ht_pair.second], this->ht2index[ht_pair.first]});
                        // inference graph update
                        if(this->th->infer_graph->contain_comht_node(ht)) {
                            this->th->infer_graph->add_disj_rel_pair({this->ht2index[ht_pair.first], this->ht2index[ht_pair.second]}, ht);
                            this->th->infer_graph->add_disj_rel_pair({this->ht2index[ht_pair.second], this->ht2index[ht_pair.first]}, ht);
                        }
                    }
                }
            }
        }
    }
           

    void slhv_deducer::initialize_ldeqneq() {
        // initialize eq classes
        for(app* var : this->th->curr_datavars) {
            this->ldvar2eqroot[var]  = var;
        }
        for(app* var : this->th->curr_locvars) {
            this->ldvar2eqroot[var] = var;
        }
        this->ldvar2eqroot[this->th->global_nil] = this->th->global_nil;
        
        // RULE P1
        SASSERT(this->th != nullptr);
        std::set<app*> data_cnstrs = this->th->curr_data_cnstr;
        std::set<app*> loc_cnstrs = this->th->curr_loc_cnstr;

        // for eqclass node construction
        std::set<app*> loc_eq_constraints;
        std::set<app*> data_eq_constraints;
        std::set<app*> loc_neq_constraints;
        std::set<app*> data_neq_constraints;
        // deal with eq and neq vars in data constraints
        for(app* dc : data_cnstrs) {
            if(dc->is_app_of(basic_family_id, OP_EQ)) {
                app* arg1 = to_app(dc->get_arg(0));
                app* arg2 = to_app(dc->get_arg(1));
                if(this->th->is_datavar(arg1) && this->th->is_datavar(arg2))  {
                    if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end() && this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        // merge equivalence class
                        if(this->ldvar2eqroot[arg1] != this->ldvar2eqroot[arg2]) {
                            app* new_root = this->ldvar2eqroot[arg1];
                            app* replaced_root = this->ldvar2eqroot[arg2];
                            if(new_root == replaced_root) {
                                continue;
                            }
                            std::map<app*, app*> tmp_ldvar2eqroot = this->ldvar2eqroot;
                            for(auto item : this->ldvar2eqroot) {
                                if(item.second == replaced_root) {
                                    tmp_ldvar2eqroot[item.first] = new_root;
                                }
                            }
                            this->ldvar2eqroot = tmp_ldvar2eqroot;
                        }
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    } else {
                        app* new_root = arg1;
                        this->ldvar2eqroot[arg1] = new_root;
                        this->ldvar2eqroot[arg2] = new_root;
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    }
                }
            } else if(dc->is_app_of(basic_family_id, OP_DISTINCT)) {
                app* arg1 = to_app(dc->get_arg(0));
                app* arg2 = to_app(dc->get_arg(1));
                if(this->th->is_datavar(arg1) && this->th->is_datavar(arg2))  {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    }
                }
            } else if(dc->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(dc->get_arg(0));
                if(inner->is_app_of(basic_family_id, OP_EQ)) {
                    app* arg1 = to_app(inner->get_arg(0));
                    app* arg2 = to_app(inner->get_arg(1));
                    if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2)))  {
                        if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg1].insert(arg2);
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg2);
                            this->ldvar2neqvars[arg1] = new_neq_set;
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        }
                        if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg2].insert(arg1);
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg1);
                            this->ldvar2neqvars[arg2] = new_neq_set;
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        }
                    }
                }
            } else {
                std::cout << "unsupported data constraint operation" << std::endl;
                SASSERT(false);
            }
        }

        // deal with eq and neq vars in loc constraints
        for(app* lc : loc_cnstrs) {
            if(lc->is_app_of(basic_family_id, OP_EQ)) {
                app* arg1 = to_app(lc->get_arg(0));
                app* arg2 = to_app(lc->get_arg(1));
                if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2))) {
                    #ifdef DED_INFO
                    std::cout << "add eq vars: " << mk_ismt2_pp(arg1, this->th->get_manager() ) << " == " <<mk_ismt2_pp(arg2, this->th->get_manager()) << std::endl;
                    #endif
                    if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end() && this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        // merge
                        app* new_root = this->ldvar2eqroot[arg1];
                        app* replaced_root = this->ldvar2eqroot[arg2];
                        if(new_root == replaced_root) {
                            continue;
                        }
                        std::map<app*, app*> tmp_ldvar2eqroot = this->ldvar2eqroot;
                        for(auto item : this->ldvar2eqroot) {
                            if(item.second == replaced_root) {
                                tmp_ldvar2eqroot[item.first] = new_root;
                            }
                        }
                        this->ldvar2eqroot = tmp_ldvar2eqroot;
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    } else {
                        app* new_root = arg1;
                        this->ldvar2eqroot[arg1] = new_root;
                        this->ldvar2eqroot[arg2] = new_root;
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    }
                }
            } else if(lc->is_app_of(basic_family_id, OP_DISTINCT)) {
                app* arg1 = to_app(lc->get_arg(0));
                app* arg2 = to_app(lc->get_arg(1));
                if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2))) {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                }
            } else if(lc->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(lc->get_arg(0));
                SASSERT(inner->is_app_of(basic_family_id, OP_EQ));
                app* arg1 = to_app(inner->get_arg(0));
                app* arg2 = to_app(inner->get_arg(1));
                if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2))) {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                    
                }
            } else {
                std::cout << "unsupported loc constraint operation" << std::endl;
                SASSERT(false);
            }
        }
        // inference graph update
        this->th->infer_graph->add_loc_eqclass_node(loc_eq_constraints);
        this->th->infer_graph->add_loc_neqclass_node(loc_neq_constraints);
        this->th->infer_graph->add_data_eqclass_node(data_eq_constraints);
        this->th->infer_graph->add_data_neqclass_node(data_neq_constraints);
    }



    void slhv_deducer::initialize_ldeqneq_disj() {
        // initialize eq classes
        for(app* var : this->th->datavars_disj) {
            this->ldvar2eqroot[var]  = var;
        }
        for(app* var : this->th->locvars_disj) {
            this->ldvar2eqroot[var] = var;
        }
        this->ldvar2eqroot[this->th->global_nil] = this->th->global_nil;
        
        // RULE P1
        SASSERT(this->th != nullptr);
        std::set<app*> data_cnstrs = this->th->inf_graph_data_assertions;
        std::set<app*> loc_cnstrs = this->th->inf_graph_loc_assertions;

        // for eqclass node construction
        std::set<app*> loc_eq_constraints;
        std::set<app*> data_eq_constraints;
        std::set<app*> loc_neq_constraints;
        std::set<app*> data_neq_constraints;
        // deal with eq and neq vars in data constraints
        for(app* dc : data_cnstrs) {
            if(dc->is_app_of(basic_family_id, OP_EQ)) {
                app* arg1 = to_app(dc->get_arg(0));
                app* arg2 = to_app(dc->get_arg(1));
                if(this->th->is_datavar(arg1) && this->th->is_datavar(arg2))  {
                    if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end() && this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        // merge equivalence class
                        if(this->ldvar2eqroot[arg1] != this->ldvar2eqroot[arg2]) {
                            app* new_root = this->ldvar2eqroot[arg1];
                            app* replaced_root = this->ldvar2eqroot[arg2];
                            if(new_root == replaced_root) {
                                continue;
                            }
                            std::map<app*, app*> tmp_ldvar2eqroot = this->ldvar2eqroot;
                            for(auto item : this->ldvar2eqroot) {
                                if(item.second == replaced_root) {
                                    tmp_ldvar2eqroot[item.first] = new_root;
                                }
                            }
                            this->ldvar2eqroot = tmp_ldvar2eqroot;
                        }
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    } else {
                        app* new_root = arg1;
                        this->ldvar2eqroot[arg1] = new_root;
                        this->ldvar2eqroot[arg2] = new_root;
                        // for eqclass node construction
                        data_eq_constraints.insert(dc);
                    }
                }
            } else if(dc->is_app_of(basic_family_id, OP_DISTINCT)) {
                app* arg1 = to_app(dc->get_arg(0));
                app* arg2 = to_app(dc->get_arg(1));
                if(this->th->is_datavar(arg1) && this->th->is_datavar(arg2))  {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                        // for neq relation node construction
                        data_neq_constraints.insert(dc);
                    }
                }
            } else if(dc->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(dc->get_arg(0));
                if(inner->is_app_of(basic_family_id, OP_EQ)) {
                    app* arg1 = to_app(inner->get_arg(0));
                    app* arg2 = to_app(inner->get_arg(1));
                    if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2)))  {
                        if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg1].insert(arg2);
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg2);
                            this->ldvar2neqvars[arg1] = new_neq_set;
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        }
                        if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg2].insert(arg1);
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg1);
                            this->ldvar2neqvars[arg2] = new_neq_set;
                            // for neq relation node construction
                            data_neq_constraints.insert(dc);
                        }
                    }
                }
            } else {
                std::cout << "unsupported data constraint operation" << std::endl;
                SASSERT(false);
            }
        }

        // deal with eq and neq vars in loc constraints
        for(app* lc : loc_cnstrs) {
            if(lc->is_app_of(basic_family_id, OP_EQ)) {
                app* arg1 = to_app(lc->get_arg(0));
                app* arg2 = to_app(lc->get_arg(1));
                if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2))) {
                    #ifdef DED_INFO
                    std::cout << "add eq vars: " << mk_ismt2_pp(arg1, this->th->get_manager() ) << " == " <<mk_ismt2_pp(arg2, this->th->get_manager()) << std::endl;
                    #endif
                    if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end() && this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        // merge
                        app* new_root = this->ldvar2eqroot[arg1];
                        app* replaced_root = this->ldvar2eqroot[arg2];
                        if(new_root == replaced_root) {
                            continue;
                        }
                        std::map<app*, app*> tmp_ldvar2eqroot = this->ldvar2eqroot;
                        for(auto item : this->ldvar2eqroot) {
                            if(item.second == replaced_root) {
                                tmp_ldvar2eqroot[item.first] = new_root;
                            }
                        }
                        this->ldvar2eqroot = tmp_ldvar2eqroot;
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    } else {
                        app* new_root = arg1;
                        this->ldvar2eqroot[arg1] = new_root;
                        this->ldvar2eqroot[arg2] = new_root;
                        // for eqclass node construction
                        loc_eq_constraints.insert(lc);
                    }
                }
            } else if(lc->is_app_of(basic_family_id, OP_DISTINCT)) {
                app* arg1 = to_app(lc->get_arg(0));
                app* arg2 = to_app(lc->get_arg(1));
                if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2))) {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                }
            } else if(lc->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(lc->get_arg(0));
                SASSERT(inner->is_app_of(basic_family_id, OP_EQ));
                app* arg1 = to_app(inner->get_arg(0));
                app* arg2 = to_app(inner->get_arg(1));
                if((this->th->is_locvar(arg1) || this->th->is_nil(arg1)) && (this->th->is_locvar(arg2) || this->th->is_nil(arg2))) {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                        // for neq relation node construction
                        loc_neq_constraints.insert(lc);
                    }
                    
                }
            } else {
                std::cout << "unsupported loc constraint operation" << std::endl;
                SASSERT(false);
            }
        }
        // inference graph update
        this->th->infer_graph->add_loc_eqclass_node(loc_eq_constraints);
        this->th->infer_graph->add_loc_neqclass_node(loc_neq_constraints);
        this->th->infer_graph->add_data_eqclass_node(data_eq_constraints);
        this->th->infer_graph->add_data_neqclass_node(data_neq_constraints);
    }

    bool slhv_deducer::propagate_eq_neq(){
        bool has_new = false;
        // RULE P4
        for(auto htid_p : this->djpair_set) {
            if(this->is_pt(htid_p.first) && this->is_pt(htid_p.second)) {
                heap_term* first_ht = this->index2ht[htid_p.first];
                heap_term* second_ht = this->index2ht[htid_p.second];

                app* first_pt_app = first_ht->get_atoms()[0];
                app* second_pt_app = second_ht->get_atoms()[0];

                app* first_addr = to_app(first_pt_app->get_arg(0));
                SASSERT(this->th->is_locvar(first_addr));
                app* second_addr = to_app(second_pt_app->get_arg(0));
                SASSERT(this->th->is_locvar(second_addr));
                bool add_neq_result =  this->add_ld_neq_vars(first_addr, second_addr);
                has_new = has_new || add_neq_result;
                // inference graph update
                if(add_neq_result) {
                    if(this->th->is_locvar(first_addr) && this->th->is_locvar(second_addr)) {
                        this->th->infer_graph->add_loc_neqclass_node(htid_p);
                    } else if(this->th->is_datavar(first_addr) && this->th->is_datavar(second_addr)) {
                        this->th->infer_graph->add_data_neqclass_node(htid_p);
                    }
                }
            }
        }

        // RULE P5
        for(auto htid_p : this->shpair_set) {
            if(this->is_pt(htid_p.first) && this->is_pt(htid_p.second)) {
                heap_term* first_ht = this->index2ht[htid_p.first];
                heap_term* second_ht = this->index2ht[htid_p.second];

                app* first_pt_app = first_ht->get_atoms()[0];
                app* first_addr = to_app(first_pt_app->get_arg(0));
                app* second_pt_app = second_ht->get_atoms()[0];
                app* second_addr = to_app(second_pt_app->get_arg(0));
                app* first_content_record = to_app(first_pt_app->get_arg(1));
                app* first_content = to_app(first_content_record->get_arg(0));
                app* second_content_record = to_app(second_pt_app->get_arg(1));
                app* second_content = to_app(second_content_record->get_arg(0));
                SASSERT(this->th->is_datavar(first_content) && this->th->is_datavar(second_content) || 
                this->th->is_locvar(first_content) && this->th->is_locvar(second_content));
                bool add_first_eq_result = this->add_ld_eq_vars(first_addr, second_addr);
                has_new = has_new || add_first_eq_result;

                // inference graph update
                if(add_first_eq_result) {
                    if(this->th->is_locvar(first_addr) && this->th->is_locvar(second_addr)) {
                        this->th->infer_graph->add_loc_eqclass_node(htid_p);
                    } else if(this->th->is_datavar(first_addr) && this->th->is_datavar(second_addr)) {
                        this->th->infer_graph->add_data_eqclass_node(htid_p);
                    }
                }
                bool add_second_eq_result = this->add_ld_eq_vars(first_content, second_content);
                has_new = has_new || add_second_eq_result;

                // inference graph update
                if(add_second_eq_result) {
                    if(this->th->is_locvar(first_content) && this->th->is_locvar(second_content)) {
                        this->th->infer_graph->add_loc_eqclass_node(htid_p);
                    } else if(this->th->is_datavar(first_content) && this->th->is_datavar(second_content)) {
                        this->th->infer_graph->add_data_eqclass_node(htid_p);
                    }
                }
            }
        }
        return has_new;
    }

    bool slhv_deducer::propagate_shdj_by_eq_neq() {
        // RULE P7
        bool new_sh_dj_found = false;
        std::set<std::pair<int, int>> nxt_shpair_set = this->shpair_set;
        std::set<std::pair<int, int>> nxt_djpair_set = this->djpair_set;
        std::map<int, std::set<std::pair<int, int>>> nxt_sh_1st_elem_map = this->sh_pair_1st_elem_map;
        std::map<int, std::set<std::pair<int, int>>> nxt_sh_2nd_elem_map = this->sh_pair_2nd_elem_map;
        std::map<int, std::set<std::pair<int, int>>> nxt_dj_1st_elem_map = this->dj_pair_1st_elem_map;
        std::map<int, std::set<std::pair<int, int>>> nxt_dj_2nd_elem_map = this->dj_pair_2nd_elem_map;

        for(auto sh_p1 : this->shpair_set) {
            if(this->sh_pair_2nd_elem_map.find(sh_p1.second) == this->sh_pair_2nd_elem_map.end() || !this->is_pt(sh_p1.first)) {
                continue;
            }
            for(auto sh_p2 : this->sh_pair_2nd_elem_map[sh_p1.second]) {
                if(sh_p1 != sh_p2 && this->is_pt(sh_p2.first)) {
                    heap_term* pt1 = this->index2ht[sh_p1.first];
                    heap_term* pt2 = this->index2ht[sh_p2.first];
                    SASSERT(pt1->is_atom_pt() && pt2->is_atom_pt());
                    app* first_pt = pt1->get_atoms()[0];
                    app* second_pt = pt2->get_atoms()[0];
                    app* first_addr_var = to_app(first_pt->get_arg(0));
                    app* second_addr_var = to_app(second_pt->get_arg(0));
                    app* first_pt_content_record = to_app(first_pt->get_arg(1));
                    app* second_pt_content_record = to_app(second_pt->get_arg(1));
                    app* first_pt_content = to_app(first_pt_content_record->get_arg(0));
                    app* second_pt_content = to_app(second_pt_content_record->get_arg(0));

                    if(this->ldvar2neqvars[first_addr_var].find(second_addr_var) != this->ldvar2neqvars[first_addr_var].end()) {
                        // if current setting find that address are not equal
                        SASSERT(this->ldvar2neqvars[second_addr_var].find(first_addr_var) != this->ldvar2neqvars[second_addr_var].end());
                        if(this->djpair_set.find({sh_p1.first, sh_p2.first}) != this->djpair_set.end() || 
                        this->is_emp(sh_p1.first) || 
                        this->is_emp(sh_p2.first)) {
                            SASSERT(this->djpair_set.find({sh_p2.first, sh_p1.first}) != this->djpair_set.end());
                            // pair exist, do nothing
                        } else {
                            std::pair<int, int> new_dj_pair = {sh_p1.first, sh_p2.first};
                            std::pair<int, int> mirror_pair = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #ifdef DED_INFO
                            std::cout << "5new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                            std::cout << "6new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                            #endif
                            // nxt_djpair_set.insert(new_dj_pair);
                            // nxt_djpair_set.insert(mirror_pair);
                            this->insert_dj_pair(new_dj_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
                            this->insert_dj_pair(mirror_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
                            // inference graph update
                            this->th->infer_graph->add_disj_rel_pair_locdata_neqclass(new_dj_pair, sh_p1, sh_p2);
                            this->th->infer_graph->add_disj_rel_pair_locdata_neqclass(mirror_pair, sh_p1, sh_p2);
                        }
                    } else if(this->ldvar2neqvars[first_pt_content].find(second_pt_content) != this->ldvar2neqvars[first_pt_content].end()) {
                        // if current setting find that record content are not equal
                        SASSERT(this->ldvar2neqvar[second_pt_content].find(first_pt_content) !=  this->ldvar2neqvars[second_pt_content].end());
                        std::pair<int, int> new_dj_pair = {sh_p1.first, sh_p2.first};
                        std::pair<int, int> mirror_pair = {sh_p2.first, sh_p1.first};
                        if(this->djpair_set.find({sh_p1.first, sh_p2.first}) != this->djpair_set.end() || 
                        this->is_emp(sh_p1.first) ||
                        this->is_emp(sh_p2.first)
                        ) {
                            SASSERT(this->djpair_set.find(mirror_pair) != this->djpair_set.end());
                            // pair exists, do nothing
                        } else {
                            // std::pair<int, int> new_dj_pair = {sh_p1.first, sh_p2.first};
                            // std::pair<int, int> mirror_pair = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #ifdef DED_INFO
                            std::cout << "1new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                            std::cout << "2new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                            #endif
                            // nxt_djpair_set.insert(new_dj_pair);
                            // nxt_djpair_set.insert(mirror_pair);
                            this->insert_dj_pair(new_dj_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
                            this->insert_dj_pair(mirror_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
                            // inference graph update
                            this->th->infer_graph->add_disj_rel_pair_locdata_neqclass(new_dj_pair, sh_p1, sh_p2);
                            this->th->infer_graph->add_disj_rel_pair_locdata_neqclass(mirror_pair, sh_p1, sh_p2);
                            
                        }
                    } else if(this->ldvar2eqroot[first_addr_var] == this->ldvar2eqroot[second_addr_var]){
                        if(this->shpair_set.find({sh_p1.first, sh_p2.first}) != this->shpair_set.end()) {
                            // pair exists, do nothing
                        } else {
                            std::pair<int, int> new_sh_pair1 = {sh_p1.first, sh_p2.first};
                            std::pair<int, int> new_sh_pair2 = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #ifdef DED_INFO
                            std::cout << "new sh pair: " << new_sh_pair1.first << " << " << new_sh_pair1.second << std::endl;
                            #endif
                            // nxt_shpair_set.insert(new_sh_pair1);
                            this->insert_sh_pair(new_sh_pair1, nxt_shpair_set, nxt_sh_1st_elem_map, nxt_sh_2nd_elem_map);

                            // inference graph update
                            this->th->infer_graph->add_sh_rel_pair_locdata_eqclass(new_sh_pair1, sh_p1, sh_p2);
                        }
                        if(this->shpair_set.find({sh_p2.first, sh_p1.first}) != this->shpair_set.end()) {
                            // pair exists, do nothing
                        } else {
                            std::pair<int, int> new_sh_pair1 = {sh_p1.first, sh_p2.first};
                            std::pair<int, int> new_sh_pair2 = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #ifdef DED_INFO
                            std::cout << "new sh pair: " << new_sh_pair2.first << " << " << new_sh_pair2.second << std::endl;
                            #endif
                            // nxt_shpair_set.insert(new_sh_pair2);
                            this->insert_sh_pair(new_sh_pair2, nxt_shpair_set, nxt_sh_1st_elem_map, nxt_sh_2nd_elem_map);
                            // inference graph update
                            this->th->infer_graph->add_sh_rel_pair_locdata_eqclass(new_sh_pair2, sh_p1, sh_p2);
                        }
                    } else {
                        // do nothing, leave it to lia solving
                    }
                }
            }
        } 
        this->shpair_set = nxt_shpair_set;
        this->djpair_set = nxt_djpair_set;
        this->sh_pair_1st_elem_map = nxt_sh_1st_elem_map;
        this->sh_pair_2nd_elem_map = nxt_sh_2nd_elem_map;
        this->dj_pair_1st_elem_map = nxt_dj_1st_elem_map;
        this->dj_pair_2nd_elem_map = nxt_dj_2nd_elem_map;
        return new_sh_dj_found;
    }

    bool slhv_deducer::propagate_transitive_sh() {

        bool new_sh_found = false;
        std::set<std::pair<int, int>> nxt_shpair_set = this->shpair_set;
        std::map<int, std::set<std::pair<int, int>>> nxt_sh_1st_elem_map = this->sh_pair_1st_elem_map;
        std::map<int, std::set<std::pair<int, int>>> nxt_sh_2nd_elem_map = this->sh_pair_2nd_elem_map;
        for(auto sh_pair1 : this->shpair_set) {
            if(this->sh_pair_1st_elem_map.find(sh_pair1.second) == this->sh_pair_1st_elem_map.end()) {
                continue;
            }
            for(auto sh_pair2 : this->sh_pair_1st_elem_map[sh_pair1.second]) {
                if(this->shpair_set.find({sh_pair1.first, sh_pair2.second}) != this->shpair_set.end()) {
                    // do nothing
                } else {
                    std::pair<int, int> new_pair = {sh_pair1.first, sh_pair2.second};
                    new_sh_found = true;
                    #ifdef DED_INFO
                    std::cout << "new sh pair: " << new_pair.first << " << " << new_pair.second << std::endl;
                    #endif
                    // nxt_shpair_set.insert(new_pair);
                    this->insert_sh_pair(new_pair, nxt_shpair_set, nxt_sh_1st_elem_map, nxt_sh_2nd_elem_map);
                    // inference graph update
                    this->th->infer_graph->add_sh_rel_pair(new_pair, sh_pair1, sh_pair2);
                }
            }
        }

        this->shpair_set = nxt_shpair_set;
        this->sh_pair_1st_elem_map = nxt_sh_1st_elem_map;
        this->sh_pair_2nd_elem_map = nxt_sh_2nd_elem_map;
        return new_sh_found; 
    }

    bool slhv_deducer::propagate_transitive_dj() {
        bool new_dj_found = false;
        std::set<std::pair<int, int>> nxt_djpair_set = this->djpair_set;
        std::map<int, std::set<std::pair<int, int>>> nxt_dj_1st_elem_map = this->dj_pair_1st_elem_map;
        std::map<int, std::set<std::pair<int, int>>> nxt_dj_2nd_elem_map = this->dj_pair_2nd_elem_map;
        for(auto larger_dj_p : this->djpair_set) {
            if(this->sh_pair_2nd_elem_map.find(larger_dj_p.first) != this->sh_pair_2nd_elem_map.end() && 
               this->sh_pair_2nd_elem_map.find(larger_dj_p.second) != this->sh_pair_2nd_elem_map.end()) {
                for(auto sh_pair13 : this->sh_pair_2nd_elem_map[larger_dj_p.first]) {
                    if(this->is_emp(sh_pair13.first)) {
                        continue;
                    }
                    for(auto sh_pair24 : this->sh_pair_2nd_elem_map[larger_dj_p.second]) {
                        if(this->is_emp(sh_pair24.first) || this->has_dj_pair({sh_pair13.first, sh_pair24.first})) {
                            continue;
                            // do nothing
                        } else if(this->has_dj_pair({sh_pair13.second, sh_pair24.second})){
                            std::pair<int, int> new_dj_pair = {sh_pair13.first, sh_pair24.first};
                            std::pair<int, int> mirror_pair = {sh_pair24.first, sh_pair13.first};
                            new_dj_found = true;
                            // std::cout << "3new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                            // std::cout << "4new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                            #ifdef DED_INFO
                            std::cout << "3new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                            std::cout << "4new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                            #endif
                            // nxt_djpair_set.insert(new_dj_pair);
                            // nxt_djpair_set.insert(mirror_pair);
                            this->insert_dj_pair(new_dj_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
                            this->insert_dj_pair(mirror_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
                            // inference graph update
                            this->th->infer_graph->add_disj_rel_pair(new_dj_pair, sh_pair13, sh_pair24, {sh_pair13.second, sh_pair24.second});
                            this->th->infer_graph->add_disj_rel_pair(mirror_pair, sh_pair13, sh_pair24, {sh_pair13.second, sh_pair24.second});
                        } else {
                            // do nothing, premise not hold
                        }
                    }
                }
            }
        }
        // for(auto sh_pair13 : this->shpair_set) {
        //     for(auto sh_pair24 : this->shpair_set) {
        //         if(this->djpair_set.find({sh_pair13.second, sh_pair24.second}) != this->djpair_set.end()) {
        //             if(this->djpair_set.find({sh_pair13.first, sh_pair24.first}) != this->djpair_set.end() ||
        //             this->is_emp(sh_pair13.first) || 
        //             this->is_emp(sh_pair24.first)) {
        //                 // do nothing
        //             } else {
        //                 std::pair<int, int> new_dj_pair = {sh_pair13.first, sh_pair24.first};
        //                 std::pair<int, int> mirror_pair = {sh_pair24.first, sh_pair13.first};
        //                 new_dj_found = true;
        //                 // std::cout << "3new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
        //                 // std::cout << "4new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
        //                 #ifdef DED_INFO
        //                 std::cout << "3new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
        //                 std::cout << "4new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
        //                 #endif
        //                 // nxt_djpair_set.insert(new_dj_pair);
        //                 // nxt_djpair_set.insert(mirror_pair);
        //                 this->insert_dj_pair(new_dj_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
        //                 this->insert_dj_pair(mirror_pair, nxt_djpair_set, nxt_dj_1st_elem_map, nxt_dj_2nd_elem_map);
        //                 // inference graph update
        //                 this->th->infer_graph->add_disj_rel_pair(new_dj_pair, sh_pair13, sh_pair24, {sh_pair13.second, sh_pair24.second});
        //                 this->th->infer_graph->add_disj_rel_pair(mirror_pair, sh_pair13, sh_pair24, {sh_pair13.second, sh_pair24.second});
        //             }
        //         }
        //     }
        // }
        this->djpair_set = nxt_djpair_set;
        this->dj_pair_1st_elem_map = nxt_dj_1st_elem_map;
        this->dj_pair_2nd_elem_map = nxt_dj_2nd_elem_map;
        return new_dj_found;
    }

    bool slhv_deducer::add_ld_eq_vars(app* v1, app* v2) {
        #ifdef DED_INFO
        std::cout << "add eq vars: " << mk_ismt2_pp(v1, this->th->get_manager() ) << " == " <<mk_ismt2_pp(v2, this->th->get_manager()) << std::endl;
        #endif
        if((this->th->is_locvar(v1) || this->th->is_nil(v1)) &&
           (this->th->is_locvar(v2) || this->th->is_nil(v2))) {
            app* arg1 = v1;
            app* arg2 = v2;
            if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end() && this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                // merge
                app* new_root = this->ldvar2eqroot[arg1];
                app* replaced_root = this->ldvar2eqroot[arg2];
                if(new_root == replaced_root) { 
                    return false;
                }
                std::map<app*, app*> tmp_ldvar2eqroot = this->ldvar2eqroot;
                for(auto item : this->ldvar2eqroot) {
                    if(item.second == replaced_root) {
                        tmp_ldvar2eqroot[item.first] = new_root;
                    }
                }
                this->ldvar2eqroot = tmp_ldvar2eqroot;
            } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
            } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
            } else {
                app* new_root = arg1;
                this->ldvar2eqroot[arg1] = new_root;
                this->ldvar2eqroot[arg2] = new_root;
            }
        } else if(this->th->is_datavar(v1) && this->th->is_datavar(v2)) {
            app* arg1 = v1;
            app* arg2 = v2;
            if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end() && this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                // merge
                app* new_root = this->ldvar2eqroot[arg1];
                app* replaced_root = this->ldvar2eqroot[arg2];
                if(new_root == replaced_root) {
                    return false;
                }
                std::map<app*, app*> tmp_ldvar2eqroot = this->ldvar2eqroot;
                for(auto item : this->ldvar2eqroot) {
                    if(item.second == replaced_root) {
                        tmp_ldvar2eqroot[item.first] = new_root;
                    }
                }
                this->ldvar2eqroot = tmp_ldvar2eqroot;
            } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
            } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
            } else {
                app* new_root = arg1;
                this->ldvar2eqroot[arg1] = new_root;
                this->ldvar2eqroot[arg2] = new_root;
            }
        } else {
            // std::cout << "add eq var error: different sort OR not vars" << std::endl;
            // std::cout << mk_ismt2_pp(v1, this->th->get_manager()) << " " << mk_ismt2_pp(v2, this->th->get_manager()) << std::endl;
            SASSERT(false);
            return false;
        }
        return true;
    }   

    bool slhv_deducer::add_ld_neq_vars(app* v1, app* v2) {
        #ifdef DED_INFO
        std::cout << "add neq vars: " << mk_ismt2_pp(v1, this->th->get_manager() ) << " != " <<mk_ismt2_pp(v1, this->th->get_manager()) << std::endl;
        #endif
        bool is_new = false;
        if(this->th->is_locvar(v1) && this->th->is_locvar(v2)) {
            app* arg1 = v1;
            app* arg2 = v2;
            if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2)) {
                if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                    is_new = this->ldvar2neqvars[arg1].insert(arg2).second;
                } else {
                    std::set<app*> new_neq_set;
                    new_neq_set.insert(arg2);
                    this->ldvar2neqvars[arg1] = new_neq_set;
                    is_new = true;
                }
                if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                    is_new = this->ldvar2neqvars[arg2].insert(arg1).second;
                } else {
                    std::set<app*> new_neq_set;
                    new_neq_set.insert(arg1);
                    this->ldvar2neqvars[arg2] = new_neq_set;
                    is_new = true;
                }
            }
        } else if(this->th->is_datavar(v1) && this->th->is_datavar(v2)) {
            app* arg1 = v1;
            app* arg2 = v2;
            if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2)) {
                if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                    is_new = this->ldvar2neqvars[arg1].insert(arg2).second;
                } else {
                    std::set<app*> new_neq_set;
                    new_neq_set.insert(arg2);
                    this->ldvar2neqvars[arg1] = new_neq_set;
                    is_new = true;
                }
                if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                    is_new = this->ldvar2neqvars[arg2].insert(arg1).second;
                } else {
                    std::set<app*> new_neq_set;
                    new_neq_set.insert(arg1);
                    this->ldvar2neqvars[arg2] = new_neq_set;
                    is_new = true;
                }
            }
        } else {
            std::cout << "add neq var error: different sort OR not vars" << std::endl;
            SASSERT(false);
        }
        return is_new;
    }

    bool slhv_deducer::is_pt(int index) {
        SASSERT(this->index2ht.find(index) != this->index2ht.end());
        if(this->index2ht[index]->is_atom_pt()) {
            return true;
        }
        return false;
    }


    bool slhv_deducer::is_emp(int index){
        SASSERT(this->index2ht.find(index) != this->index2ht.end());
        if(this->index2ht[index]->is_emp()) {
           return true;
        }
        return false;
    }

    bool slhv_deducer::is_hvar(int index) {
        SASSERT(this->index2ht.find(index) != this->index2ht.end());
        if(this->index2ht[index]->is_atom_hvar()){
            return true;
        }
        return false;
    }


    bool slhv_deducer::has_dj_pair(std::pair<int, int> dj_p) {
        if(this->dj_pair_1st_elem_map.find(dj_p.first) == this->dj_pair_1st_elem_map.end()) {
            return false;
        } else {
            if(this->dj_pair_1st_elem_map[dj_p.first].find(dj_p) != this->dj_pair_1st_elem_map[dj_p.first].end()) {
                return true;
            } else {
                return false;
            }
        }
    }

    bool slhv_deducer::has_sh_pair(std::pair<int, int> sh_p) {
        if(this->sh_pair_1st_elem_map.find(sh_p.first) == this->sh_pair_1st_elem_map.end()) {
            return false;
        } else {
            if(this->sh_pair_1st_elem_map[sh_p.first].find(sh_p) != this->sh_pair_1st_elem_map[sh_p.first].end()) {
                return true;
            } else {
                return false;
            }
        }
    }

    void slhv_deducer::check_ldvars_consistency() {
        SASSERT(!this->unsat_found);
        for(auto item : this->ldvar2neqvars) {
            app* var1 = item.first;
            for(app* var2 : item.second) {
                if(this->ldvar2eqroot[var1] == this->ldvar2eqroot[var2]) {
                    this->unsat_found = true;
                    // inference graph record unsat
                    if(this->th->is_locvar(var1)) {
                        this->th->infer_graph->set_curr_loc_eqneq_unsat_node();
                    } else {
                        this->th->infer_graph->set_curr_data_eqneq_unsat_node();
                    }
                    return;
                }
            }
        }
        this->unsat_found = false;
    }

    void slhv_deducer::check_sh_of_emp() {
        SASSERT(!this->unsat_found);
        for(auto sh_pair : this->shpair_set) {
            if(this->is_pt(sh_pair.first) && this->is_emp(sh_pair.second)) {
                // inference graph record unsat
                this->th->infer_graph->set_sh_emp_unsat_node(sh_pair);
                this->unsat_found = true;
                return;
            }
        }
        this->unsat_found = false;
    }


    void check_pt_addr_nil();

    slhv_deducer::slhv_deducer(theory_slhv* th, formula_encoder* fec, bool is_disj){
        this->th = th;
        this->fec = fec;
        this->unsat_found = false;
        this->ht2index = this->fec->get_ht2index_map();
        this->index2ht = this->fec->get_index2ht();
        if(!is_disj) {
            this->initialize_shdj();
            this->initialize_ldeqneq();
        } else {
            this->initialize_shdj_disj();
            this->initialize_ldeqneq_disj();
        }
        this->check_ldvars_consistency();
    }
    

    void slhv_deducer::print_current(std::ostream& os) {
        os << "=============================== " << std::endl;
        os << "============== current eq" << std::endl;
        for(auto item : this->ldvar2eqroot){
            os << "var: " <<  mk_ismt2_pp(item.first, this->th->get_manager()) << " root: " << mk_ismt2_pp(item.second, this->th->get_manager()) << std::endl;
        }
        os << "============== current neqs" << std::endl;
        for(auto item : this->ldvar2neqvars) {
            os << "var: " << mk_ismt2_pp(item.first, this->th->get_manager()) << std::endl;
            os << "neq vars: {" << std::endl;
            for(app* neq_v : item.second) {
                os << mk_ismt2_pp(neq_v, this->th->get_manager()) << ",";
            }
            os << "}" <<  std::endl;
        }
        os << "============== current dj pairs" << std::endl;
        for(auto dj_p : this->djpair_set) {
            std::cout << "(" << dj_p.first << ", " << dj_p.second << ")" << std::endl;
        }
        os << "============== current sh pairs" << std::endl;
        for(auto sh_p : this->shpair_set) {
            std::cout << "(" << sh_p.first << ", " << sh_p.second << ")" << std::endl;
        }
        os << "=============================== " << std::endl;
    }

    bool slhv_deducer::deduce() {
        bool has_change = false;
        do
        {
            // std::cout << "deduce loop begin" << std::endl;
            has_change = false;
            // std::cout << "propagate transitive sh" << std::endl;
            has_change = has_change || this->propagate_transitive_sh();
            this->check_sh_of_emp();
            if(this->unsat_found) {
                return false;
            }
            // std::cout << "propagate transitive dj" << std::endl;
            has_change = has_change || this->propagate_transitive_dj();
            this->check_sh_of_emp();
            if(this->unsat_found) {
                return false;
            }
            // std::cout << "propagate shdj by eq neq" << std::endl;
            has_change = has_change || this->propagate_shdj_by_eq_neq();
            this->check_sh_of_emp();
            if(this->unsat_found) {
                return false;
            }
            // std::cout << "propagate eq neq" << std::endl;
            has_change = has_change || this->propagate_eq_neq();
            this->check_ldvars_consistency();
            if(this->unsat_found) {
                return false;
            }
            // std::cout << "deduce loop end" << std::endl;
        } while (has_change && !this->unsat_found);
        if(this->unsat_found) {
            return false;
        } else {
            return true;
        }
    }

    // inference graph node

    inf_node::inf_node(expr* outside) {
        this->reset_configs();
        this->is_outside_assignment = true;
        this->outside_assignment = outside;
    }

    inf_node::inf_node(expr* refined_assignment, std::set<inf_node*> premises) {
        this->reset_configs();
        this->is_refined_assignment = true;
        this->refined_assignment = refined_assignment;
        this->premises = premises;
    }

    inf_node::inf_node(std::pair<heap_term*, heap_term*> ht_eq_pair, std::set<inf_node*> premises) {
        this->reset_configs();
        this->is_ht_eq_pair = true;
        this->ht_eq_pair = ht_eq_pair;
        this->premises = premises;
    }


    inf_node::inf_node(std::pair<heap_term*, heap_term*> subht_disjht_p, bool is_subht, std::set<inf_node*> premises) {
        this->reset_configs();
        if(is_subht) {
            this->is_subht_pair = true;
            this->subht_pair = subht_disjht_p;
        } else {
            this->is_disjht_pair = true;
            this->disjht_pair = subht_disjht_p;
        }
    }

    inf_node::inf_node(heap_term* com_ht, std::set<inf_node*> premises) {
        this->reset_configs();
        this->is_compound_heap_term = true;
        this->compound_ht = com_ht;
        this->premises = premises;
    }

    inf_node::inf_node(std::pair<int, int> pair, bool is_dj, bool is_sh, std::set<inf_node*> premises) {
        this->reset_configs();
        SASSERT(is_dj && !is_sh || is_sh && !is_dj);
        if(is_dj) {
            this->is_dj_rel = true;
            this->dj_pair = pair;
        } else {
            this->is_sh_rel = true;
            this->sh_pair = pair;
        }
        this->premises = premises;
    }

    inf_node::inf_node(std::set<inf_node*> premises) {
        this->reset_configs();
        this->is_eq_class = true;
        this->premises = premises;
    }


    std::set<inf_node*> inf_node::get_conflict_sources() {
        SASSERT(this->is_conflict_node);
        std::set<inf_node*> sources;
        std::set<inf_node*> nodes_to_process;
        nodes_to_process.insert(this);
        int current_size = nodes_to_process.size();
        while(current_size > 0) {
            std::set<inf_node*> nxt_nodes_to_process;
            for(inf_node* n : nodes_to_process) {n->get_is_outside_assignment();
                if(n->get_is_outside_assignment()) {
                    sources.insert(n);
                } else {
                    for(inf_node* pn : n->get_premises()) {
                        if(pn != n) {
                            nxt_nodes_to_process.insert(pn);
                        }
                    }
                }
            }
            nodes_to_process = nxt_nodes_to_process;
            current_size = nodes_to_process.size();
        }
        return sources;
    }

    void inf_node::reset_configs() {
        this->is_outside_assignment = false;
        this->outside_assignment = nullptr;
        this->is_refined_assignment = false;
        this->refined_assignment = nullptr;
        this->is_compound_heap_term = false;
        this->compound_ht = nullptr;
        this->is_ht_eq_pair = false;
        this->ht_eq_pair = {nullptr, nullptr};
        this->is_dj_rel = false;
        this->dj_pair = {-1, -1};
        this->is_sh_rel = false;
        this->sh_pair = {-1, -1};
        this->is_eq_class = false;
        this->is_conflict_node = false;
    }
    // inference graph

    inference_graph::inference_graph(theory_slhv* th, std::set<expr*> initial_assignments){
        this->th = th;
        for(expr* init_ass : initial_assignments) {
            this->create_init_assignment_node(init_ass);
        }
    }


    inf_node* inference_graph::get_outside_assignment_premise(expr* out_assignment) {
        for(inf_node* n : this->outside_nodes) {
            if(n->get_outside_assignment() == out_assignment) {
                return n;
            }
        }
        #ifdef INF_GRAPH_DEBUG
        std::cout << "ERROR: out assign node not found" << std::endl;
        #endif
        return nullptr;
    }

    inf_node* inference_graph::get_refine_assignment_premise(expr* refine_assignment) {
        for(inf_node* n : this->refine_nodes) {
            if(n->get_refined_assignment() == refine_assignment) {
                return n;
            }
        }
        return nullptr;
    }

    inf_node* inference_graph::get_compound_ht_premise(heap_term* com_ht) {
        for(inf_node* n : this->compound_nodes) {
            if(n->get_compound_ht() == com_ht) {
                return n;
            }
        }
        #ifdef INF_GRAPH_DEBUG
        std::cout << "ERROR: com ht node not found" << std::endl;
        com_ht->print(std::cout);
        #endif
        return nullptr;
    }

    inf_node* inference_graph::get_ht_eq_pair_premise(std::pair<heap_term*, heap_term*> ht_p) {
        std::pair<heap_term*, heap_term*> mirror_pair = {ht_p.second, ht_p.first};
        for(inf_node* n : this->ht_eq_pair_nodes) {
            if(n->get_ht_eq_pair() == ht_p || n->get_ht_eq_pair() == mirror_pair) {
                return n;
            }
        }
        #ifdef INF_GRAPH_DEBUG
        std::cout << "ERROR: ht eq pair node not found" << std::endl;
        #endif
        return nullptr;

    }

    inf_node* inference_graph::get_subht_pair_premise(std::pair<heap_term*, heap_term*> ht_p) {
        for(inf_node* n : this->subht_pair_nodes) {
            if(n->get_subht_pair() == ht_p) {
                return n;
            }
        }
        return nullptr;
    }

    inf_node* inference_graph::get_disjht_pair_premise( std::pair<heap_term*, heap_term*> ht_p) {
        std::pair<heap_term*, heap_term*> mirror_pair = {ht_p.second, ht_p.first};
        for(inf_node* n : this->disjht_pair_nodes) {
            if(n->get_disjht_pair() == ht_p || n->get_disjht_pair() == mirror_pair) {
                return n;
            }
        }
        return nullptr;
    }

    inf_node* inference_graph::get_disj_rel_premise(std::pair<int, int> disj_p) {
        
        std::pair<int, int> mirror_pair = {disj_p.second, disj_p.first};
        for(inf_node* n : this->disj_rel_nodes) {
            if(n->get_dj_pair() == disj_p || n->get_dj_pair() == mirror_pair) {
                return n;
            }
        }
        #ifdef INF_GRAPH_DEBUG
        std::cout << "ERROR: disj rel node not found" << std::endl;
        #endif
        return nullptr;
    }
    inf_node* inference_graph::get_sh_rel_premise(std::pair<int, int> sh_p) {
        
        for(inf_node* n : this->sh_rel_nodes) {
            if(n->get_sh_pair() == sh_p) {
                return n;
            }
        }
        #ifdef INF_GRAPH_DEBUG
        std::cout << "ERROR: sh rel node not found" << std::endl;
        #endif
        return nullptr;
    }


    bool inference_graph::contain_dj_node(std::pair<int, int> dj_p){
        for(inf_node* n : this->disj_rel_nodes) {
            if(n->get_dj_pair() == dj_p) {
                return true;
            }
        }
        return false;
    }

    bool inference_graph::contain_sh_node(std::pair<int, int> sh_p){
        
        for(inf_node* n : this->sh_rel_nodes) {
            if(n->get_sh_pair() == sh_p) {
                return true;
            }
        }
        return false;
    }


    bool inference_graph::contain_comht_node(heap_term* com_ht) {
        for(inf_node* n : this->compound_nodes) {
            if(n->get_compound_ht() == com_ht) {
                return true;
            }
        }
        return false;
    }


    void inference_graph::create_init_assignment_node(expr* init_ass){
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "create init assignment node" << std::endl;
        #endif
        for(inf_node* in : this->outside_nodes) {
            if(in->get_is_outside_assignment()) {
                expr* existing_outside = in->get_outside_assignment();
                if(existing_outside == init_ass) {
                    return;
                }
            }
        }
        inf_node* outside_node = alloc(inf_node, init_ass);
        this->nodes.insert(outside_node);
        this->outside_nodes.insert(outside_node);
    }

    void inference_graph::add_refined_assignment_node(expr* new_assignment, expr* old_assignment) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add refined_assignment node" << std::endl;
        #endif
        for(inf_node* in : this->refine_nodes) {
            if(in->get_is_refined_assignment()) {
                expr* existing_refine = in->get_refined_assignment();
                if(existing_refine == new_assignment) {
                    return;
                }
            }
        }
        std::set<inf_node*> premises;
        inf_node* outside_node = this->get_outside_assignment_premise(old_assignment);
        inf_node* refined_node = this->get_refine_assignment_premise(old_assignment);
        if(outside_node != nullptr) {
            premises.insert(outside_node);
        } else if(refined_node != nullptr) {
            premises.insert(refined_node);
        } else {
            std::cout << "ERROR: assignment " << mk_ismt2_pp(old_assignment, this->th->get_manager()) << " does not exist in node" << std::endl;
        }
        inf_node* new_refine_node = alloc(inf_node, new_assignment, premises);
        this->nodes.insert(new_refine_node);
        this->refine_nodes.insert(new_refine_node);
    }

    void inference_graph::add_compound_ht_node(heap_term* com_ht, expr* refined_assignment) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add compound ht node" << std::endl;
        #endif
        for(inf_node* node : this->compound_nodes) {
            if(node->get_compound_ht() == com_ht) {
                return;
            }
        }
        std::set<inf_node*> premises;
        inf_node* pre_refined_assign_node = this->get_refine_assignment_premise(refined_assignment);
        if(pre_refined_assign_node != nullptr) {
            premises.insert(pre_refined_assign_node);
        } else {
            std::cout << "ERROR: ref assignment " << mk_ismt2_pp(refined_assignment, this->th->get_manager()) << " does not exist in node" << std::endl;
        }
        inf_node* com_ht_node = alloc(inf_node, com_ht, premises);
        this->nodes.insert(com_ht_node);
        this->compound_nodes.insert(com_ht_node);
    }

    void inference_graph::add_ht_eq_pair_node(std::pair<heap_term*, heap_term*> ht_eq_p, expr* refined_assignment) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  ht_eq_pair node" << std::endl;
        #endif
        std::pair<heap_term*, heap_term*> mirror_pair = {ht_eq_p.second, ht_eq_p.first};
        for(inf_node* eqp_n : this->ht_eq_pair_nodes) {
            if(eqp_n->get_ht_eq_pair() == ht_eq_p || eqp_n->get_ht_eq_pair() == mirror_pair) {
                return;
            }
        }
        std::set<inf_node*> premises;
        inf_node* pre_refine_assign_node = this->get_refine_assignment_premise(refined_assignment);
        if(pre_refine_assign_node != nullptr) {
            premises.insert(pre_refine_assign_node);
        } else {
            std::cout << "ERROR: ref assignment " << mk_ismt2_pp(refined_assignment, this->th->get_manager()) << " does not exist in node" << std::endl;
        }
        inf_node* ht_eq_pair_node = alloc(inf_node, ht_eq_p, premises);
        this->nodes.insert(ht_eq_pair_node);
        this->ht_eq_pair_nodes.insert(ht_eq_pair_node);
    }


    void inference_graph::add_subht_pair_node(std::pair<heap_term*, heap_term*> subht_p, expr* refined_assignment) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add disjht_pair node" << std::endl;
        #endif
        for(inf_node* sht_n : this->subht_pair_nodes) {
            if(sht_n->get_subht_pair() == subht_p) {
                return;
            }
        }
        std::set<inf_node*> premises;
        inf_node* pre_refine_assign_node = this->get_refine_assignment_premise(refined_assignment);
        if(pre_refine_assign_node != nullptr) {
            premises.insert(pre_refine_assign_node);
        } else {
            std::cout << "ERROR: ref assignment " << mk_ismt2_pp(refined_assignment, this->th->get_manager()) << " does not exist in node" << std::endl;
        }
        inf_node* subht_pair_node = alloc(inf_node, subht_p, true, premises);
        this->nodes.insert(subht_pair_node);
        this->subht_pair_nodes.insert(subht_pair_node);
    }

    void inference_graph::add_disjht_pair_node(std::pair<heap_term*, heap_term*> disjht_p, expr* refined_assignment) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add subht_pair node" << std::endl;
        #endif
        std::pair<heap_term*, heap_term*> mirror_pair = {disjht_p.second, disjht_p.first};
        for(inf_node* djht_n : this->disjht_pair_nodes) {
            if(djht_n->get_disjht_pair() == disjht_p || djht_n->get_disjht_pair() == mirror_pair) {
                return;
            }
        }
        std::set<inf_node*> premises;
        inf_node* pre_refine_assign_node = this->get_refine_assignment_premise(refined_assignment);
        if(pre_refine_assign_node != nullptr) {
            premises.insert(pre_refine_assign_node);
        } else {
            std::cout << "ERROR: ref assignment " << mk_ismt2_pp(refined_assignment, this->th->get_manager()) << " does not exist in node" << std::endl;
        }
        inf_node* disjht_pair_node = alloc(inf_node, disjht_p, false, premises);
        this->nodes.insert(disjht_pair_node);
        this->disjht_pair_nodes.insert(disjht_pair_node);
    }


    void inference_graph::add_loc_eqclass_node(std::set<app*> loc_eq_constr) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  loc_eqclass node" << std::endl;
        #endif
        
        std::set<inf_node*> premises;
        for(app* loc_eq : loc_eq_constr) {
            inf_node* temp_node = this->get_refine_assignment_premise(loc_eq);
            if(temp_node != nullptr) {
                premises.insert(temp_node);
            } else {
                std::cout << "ERROR: ref assignment " << mk_ismt2_pp(loc_eq, this->th->get_manager()) << " does not exist in node" << std::endl;
            }
        }
        inf_node* first_loc_eq_node = alloc(inf_node, premises);
        this->nodes.insert(first_loc_eq_node);
        this->newest_loc_eq_node = first_loc_eq_node;
    }

    void inference_graph::add_data_eqclass_node(std::set<app*> data_eq_constr) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  data_eqclass node" << std::endl;
        #endif
        std::set<inf_node*> premises;
        for(app* data_eq : data_eq_constr) {
            inf_node* temp_node = this->get_refine_assignment_premise(data_eq);
            if(temp_node != nullptr) {
                premises.insert(temp_node);
            } else {
                std::cout << "ERROR: ref assignment " << mk_ismt2_pp(data_eq, this->th->get_manager()) << " does not exist in node" << std::endl;
            }
        }
        inf_node* first_data_eq_node = alloc(inf_node, premises);
        this->nodes.insert(first_data_eq_node);
        this->newest_data_eq_node = first_data_eq_node;
    }

    void inference_graph::add_loc_neqclass_node(std::set<app*> loc_neq_constr){
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  loc_neqclass node" << std::endl;
        #endif
        std::set<inf_node*> premises;
        for(app* loc_neq : loc_neq_constr) {
            inf_node* temp_node = this->get_refine_assignment_premise(loc_neq);
            if(temp_node != nullptr) {
                premises.insert(temp_node);
            } else {
                std::cout << "ERROR: ref assignment " << mk_ismt2_pp(loc_neq, this->th->get_manager()) << " does not exist in node" << std::endl;
            }
        }
        inf_node* first_loc_neq_node = alloc(inf_node, premises);
        this->nodes.insert(first_loc_neq_node);
        this->newest_loc_neq_node = first_loc_neq_node;
    }

    void inference_graph::add_data_neqclass_node(std::set<app*> data_neq_constr) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  data_neqclass node" << std::endl;
        #endif
        std::set<inf_node*> premises;
        for(app* data_neq : data_neq_constr) {
            inf_node* temp_node = this->get_refine_assignment_premise(data_neq);
            if(temp_node != nullptr) {
                premises.insert(temp_node);
            } else {
                std::cout << "ERROR: ref assignment " << mk_ismt2_pp(data_neq, this->th->get_manager()) << " does not exist in node" << std::endl;
            }
        }
        inf_node* first_data_neq_node = alloc(inf_node, premises);
        this->nodes.insert(first_data_neq_node);
        this->newest_data_neq_node = first_data_neq_node;
    }
    
    void inference_graph::add_data_neqclass_node(std::pair<int, int> dj_pair){
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  data_neqclass node dj pair" << std::endl;
        #endif
        std::set<inf_node*> premises;
        if(this->newest_data_eq_node != nullptr) {
            premises.insert(this->newest_data_eq_node);
        } else {
            std::cout << "ERROR: data eq node does not exist" << std::endl;
        }
        if(this->newest_data_neq_node != nullptr) {
            premises.insert(this->newest_data_neq_node);
        } else {
            std::cout << "ERROR: data neq node does not exist" << std::endl;
        }
        
        inf_node* dj_pair_node = this->get_disj_rel_premise(dj_pair);
        premises.insert(dj_pair_node);
        inf_node* next_data_neq_node = alloc(inf_node, premises);
        this->nodes.insert(next_data_neq_node);
        this->newest_data_neq_node = next_data_neq_node;
    }

    void inference_graph::add_loc_neqclass_node(std::pair<int, int> dj_pair){
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  loc_neqclass node dj pair" << std::endl;
        #endif
        std::set<inf_node*> premises;
        if(this->newest_loc_eq_node != nullptr) {
            premises.insert(this->newest_loc_eq_node);
        } else {
            std::cout << "ERROR: data eq node does not exist" << std::endl;
        }
        if(this->newest_loc_neq_node != nullptr) {
            premises.insert(this->newest_loc_neq_node);
        } else {
            std::cout << "ERROR: data neq node does not exist" << std::endl;
        }
        inf_node* dj_pair_node = this->get_disj_rel_premise(dj_pair);
        premises.insert(dj_pair_node);
        inf_node* next_loc_neq_node = alloc(inf_node, premises);
        this->nodes.insert(next_loc_neq_node);
        this->newest_loc_neq_node = next_loc_neq_node;
    }
    void inference_graph::add_data_eqclass_node(std::pair<int, int> sh_pair) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  data_eqclass node sh pair" << std::endl;
        #endif
        std::set<inf_node*> premises;
        if(this->newest_data_eq_node != nullptr) {
            premises.insert(this->newest_data_eq_node);
        } else {
            std::cout << "ERROR: data eq node does not exist" << std::endl;
        }
        if(this->newest_data_neq_node != nullptr) {
            premises.insert(this->newest_data_neq_node);
        } else {
            std::cout << "ERROR: data neq node does not exist" << std::endl;
        }
        inf_node* sh_pair_node = this->get_sh_rel_premise(sh_pair);
        premises.insert(sh_pair_node);
        inf_node* next_data_eq_node = alloc(inf_node, premises);
        this->nodes.insert(next_data_eq_node);
        this->newest_data_eq_node = next_data_eq_node;
    }
    void inference_graph::add_loc_eqclass_node(std::pair<int, int> sh_pair) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  loc_eqclass node sh pair" << std::endl;
        #endif
        std::set<inf_node*> premises;
        if(this->newest_loc_eq_node != nullptr) {
            premises.insert(this->newest_loc_eq_node);
        } else {
            std::cout << "ERROR: data eq node does not exist" << std::endl;
        }
        if(this->newest_loc_neq_node != nullptr) {
            premises.insert(this->newest_loc_neq_node);
        } else {
            std::cout << "ERROR: data neq node does not exist" << std::endl;
        }
        inf_node* sh_pair_node = this->get_sh_rel_premise(sh_pair);
        premises.insert(sh_pair_node);
        inf_node* next_loc_neq_node = alloc(inf_node, premises);
        this->nodes.insert(next_loc_neq_node);
        this->newest_loc_neq_node = next_loc_neq_node;
    }
    void inference_graph::add_disj_rel_pair(std::pair<int, int> dj_p, heap_term* com_ht) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  disj_rel_pair comht" << std::endl;
        #endif
        std::set<inf_node*> premises;
        inf_node* com_ht_node = this->get_compound_ht_premise(com_ht);
        premises.insert(com_ht_node);
        inf_node* new_dj_node = alloc(inf_node, dj_p, true, false, premises);
        this->nodes.insert(new_dj_node);
        this->disj_rel_nodes.insert(new_dj_node);
    }
    void inference_graph::add_disj_rel_pair_locdata_neqclass(std::pair<int, int> dj_p, std::pair<int, int> pt1InHt, std::pair<int, int> pt2InHt) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  disj_rel_pair two pt" << std::endl;
        #endif
        std::set<inf_node*> premises;
        if(this->newest_data_neq_node != nullptr) {
            premises.insert(this->newest_data_neq_node);
        } else {
            std::cout << "ERROR: data eq node does not exist" << std::endl;
        }
        if(this->newest_loc_neq_node != nullptr) {
            premises.insert(this->newest_loc_neq_node);
        } else {
            std::cout << "ERROR: data neq node does not exist" << std::endl;
        }
        inf_node* pt1node = this->get_sh_rel_premise(pt1InHt);
        inf_node* pt2node = this->get_sh_rel_premise(pt2InHt);
        premises.insert(pt1node);
        premises.insert(pt2node);
        inf_node* new_dj_node = alloc(inf_node, dj_p, true, false, premises);
        this->nodes.insert(new_dj_node);
        this->disj_rel_nodes.insert(new_dj_node);
    }

    void inference_graph::add_disj_rel_pair(std::pair<int, int> dj_p, std::pair<int, int> ht1InHt3, std::pair<int, int> ht2InHt4, std::pair<int, int> ht3DjHt4) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  disj_rel_pair ht1ht3 ht2ht4" << std::endl;
        #endif
        std::set<inf_node*> premises;
        inf_node* ht1InHt3_node = this->get_sh_rel_premise(ht1InHt3);
        inf_node* ht2InHt4_node = this->get_sh_rel_premise(ht2InHt4);
        inf_node* ht3DjHt4_node = this->get_disj_rel_premise(ht3DjHt4);
        premises.insert(ht1InHt3_node);
        premises.insert(ht2InHt4_node);
        premises.insert(ht3DjHt4_node);
        inf_node* new_dj_node = alloc(inf_node, dj_p, true, false, premises);
        this->nodes.insert(new_dj_node);
        this->disj_rel_nodes.insert(new_dj_node);
    }


    void inference_graph::add_disj_rel_pair_disjht(std::pair<int, int> dj_p, std::pair<heap_term*, heap_term*> disjht) {
        std::set<inf_node*> premises;
        inf_node* disjht_node = this->get_disjht_pair_premise(disjht);
        premises.insert(disjht_node);
        inf_node* new_dj_node = alloc(inf_node, dj_p, true, false, premises);
        this->nodes.insert(new_dj_node);
        this->disj_rel_nodes.insert(new_dj_node);
    }

    void inference_graph::add_sh_rel_pair(std::pair<int, int> sh_p, heap_term* com_ht) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  sh_rel_pair com_ht" << std::endl;
        #endif
        std::set<inf_node*> premises;
        premises.insert(this->get_compound_ht_premise(com_ht));
        inf_node* new_sh_pair = alloc(inf_node, sh_p, false, true, premises);
        this->nodes.insert(new_sh_pair);
        this->sh_rel_nodes.insert(new_sh_pair);
    }

    void inference_graph::add_sh_rel_pair(std::pair<int, int> sh_p, std::pair<heap_term*, heap_term*> ht_eq_p) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  sh_rel_pair ht_eq_p" << std::endl;
        #endif
        std::set<inf_node*> premises;
        premises.insert(this->get_ht_eq_pair_premise(ht_eq_p));
        inf_node* new_sh_node = alloc(inf_node, sh_p, false, true, premises);
        this->nodes.insert(new_sh_node);
        this->sh_rel_nodes.insert(new_sh_node);
    }

    void inference_graph::add_sh_rel_pair_locdata_eqclass(std::pair<int, int> sh_p, std::pair<int, int> pt1InHt, std::pair<int, int> pt2InHt) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  sh_rel_pair locdata_eqclass" << std::endl;
        #endif
        std::set<inf_node*> premises;
        inf_node* pt1_sh_node = this->get_sh_rel_premise(pt1InHt);
        inf_node* pt2_sh_node = this->get_sh_rel_premise(pt2InHt);
        premises.insert(pt1_sh_node);
        premises.insert(pt2_sh_node);
        if(this->newest_data_eq_node != nullptr) {
            premises.insert(this->newest_data_eq_node);
        } else {
            std::cout << "ERROR: data eq node does not exist" << std::endl;
        }
        if(this->newest_loc_eq_node != nullptr) {
            premises.insert(this->newest_loc_eq_node);
        } else {
            std::cout << "ERROR: data neq node does not exist" << std::endl;
        }
        inf_node* new_sh_node = alloc(inf_node, sh_p, false, true, premises);
        this->nodes.insert(new_sh_node);
        this->sh_rel_nodes.insert(new_sh_node);
    }

    void inference_graph::add_isolated_sh_rel_pair(std::pair<int, int> sh_p) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  sh_rel_pair isolated" << std::endl;
        #endif
        std::set<inf_node*> premises;
        inf_node* iso_node = alloc(inf_node, sh_p, false, true, premises);
        this->nodes.insert(iso_node);
        this->sh_rel_nodes.insert(iso_node);
    }

    void inference_graph::add_sh_rel_pair(std::pair<int, int> sh_p, std::pair<int, int> ht1InHt2, std::pair<int, int> ht2InHt3) {
        #ifdef SLHV_UNSAT_CORE_DEBUG
        std::cout << "add  sh_rel_pair transitive" << std::endl;
        #endif
        std::set<inf_node*> premises;
        inf_node* ht1InHt2_node = this->get_sh_rel_premise(ht1InHt2);
        inf_node* ht2InHt3_node = this->get_sh_rel_premise(ht2InHt3);
        premises.insert(ht1InHt2_node);
        premises.insert(ht2InHt3_node);
        inf_node* new_sh_node = alloc(inf_node, sh_p, false, true, premises);
        this->nodes.insert(new_sh_node);
        this->sh_rel_nodes.insert(new_sh_node);
    }

    void inference_graph::add_sh_rel_pair_subht(std::pair<int, int> sh_p, std::pair<heap_term*, heap_term*> subht) {
        std::set<inf_node*> premises;
        inf_node* subht_node = this->get_subht_pair_premise(subht);
        premises.insert(subht_node);
        inf_node* new_sh_node = alloc(inf_node, sh_p, false, true, premises);
        this->nodes.insert(new_sh_node);
        this->sh_rel_nodes.insert(new_sh_node);
    }

    void inference_graph::set_curr_loc_eqneq_unsat_node() {
        this->newest_loc_eq_node->set_conflict();
        this->newest_loc_neq_node->set_conflict();
        this->conflict_nodes.insert(newest_loc_eq_node);
        this->conflict_nodes.insert(newest_loc_neq_node);
    }

    void inference_graph::set_curr_data_eqneq_unsat_node() {
        this->newest_data_eq_node->set_conflict();
        this->newest_data_neq_node->set_conflict();
        this->conflict_nodes.insert(this->newest_data_eq_node);
        this->conflict_nodes.insert(this->newest_data_neq_node);
    }

    void inference_graph::set_sh_emp_unsat_node(std::pair<int, int> sh_emp_p) {
        inf_node* sh_emp_p_node = this->get_sh_rel_premise(sh_emp_p);
        sh_emp_p_node->set_conflict();
        this->conflict_nodes.insert(sh_emp_p_node); 
    }


    void inference_graph::set_dj_unsat_node(std::pair<int, int> dj_pair){
        for(inf_node* n : this->disj_rel_nodes) {
            if(n->get_dj_pair() == dj_pair) {
                n->set_conflict();
                this->conflict_nodes.insert(n);
                return;
            } 
        }
        std::cout << "ERROR: set dj unsat node failed" << std::endl;
    }

    void inference_graph::set_sh_unsat_node(std::pair<int, int> sh_pair){
        for(inf_node* n : this->sh_rel_nodes) {
            if(n->get_sh_pair() == sh_pair) {
                n->set_conflict();
                this->conflict_nodes.insert(n);
                return;
            }
        }
        std::cout << "ERROR: set sh unsat node failed" << std::endl;
    }


    std::set<expr*> inference_graph::compute_unsat_core_expressions() {
        SASSERT(this->conflict_nodes.size() > 0);
        std::set<expr*> result;
        std::set<inf_node*> unsat_core_outside_nodes;
        for(inf_node* n : this->conflict_nodes) {
            unsat_core_outside_nodes = slhv_util::setUnion(
                unsat_core_outside_nodes,
                n->get_conflict_sources()
            );
        }
        for(inf_node* n : unsat_core_outside_nodes) {
            SASSERT(n->get_is_outside_assignment());
            result.insert(n->get_outside_assignment());
        }
        this->unsat_core = result;
        return result;
    }

    // syntax maker

    slhv_syntax_maker::slhv_syntax_maker(theory_slhv* th, memsafe_wrapper* msw) {
        this->th = th;
        this->fv_maker = alloc(slhv_fresh_var_maker, th);
        this->msw = msw;
        this->slhv_decl_plug = (slhv_decl_plugin*) this->th->get_manager().get_plugin(this->th->get_family_id());
    }

    // fresh var making
    void slhv_syntax_maker::reset_fv_maker() {
        this->fv_maker->reset();
    }

    app* slhv_syntax_maker::mk_fresh_datavar() {
        app* fdv = this->fv_maker->mk_fresh_datavar();
        this->th->get_context().internalize(fdv, false);
        return fdv;
    }

    app* slhv_syntax_maker::mk_lia_intvar(std::string name) {
        arith_util a(this->th->get_manager());
        family_id arith_family_id = this->th->get_manager().mk_family_id("arith");
        sort* range_sort = a.mk_int();
        unsigned num_args = 0;
        arith_decl_plugin* arith_plug = (arith_decl_plugin*)this->th->get_manager().get_plugin(arith_family_id);
        app* lia_intvar = this->th->get_manager().mk_const(name, range_sort);
        #ifdef SLHV_PRINT
        std::cout << "lia intvar made: " << name << std::endl;
        #endif
        this->th->get_context().internalize(lia_intvar, false);
        return lia_intvar;
    }

    app* slhv_syntax_maker::mk_lia_intconst(int constval) {
        arith_util a(this->th->get_manager());
        app* fint = a.mk_int(constval);
        this->th->get_context().internalize(fint, false);
        return fint;
    }

    app* slhv_syntax_maker::mk_boolvar(std::string name) {
        sort* bool_sort = this->th->get_manager().mk_bool_sort();
        app* boolvar = this->th->get_manager().mk_const(name, bool_sort);
        return boolvar;
    }

    app* slhv_syntax_maker::mk_fresh_hvar() {
        app* fhv = this->fv_maker->mk_fresh_hvar();
        this->th->get_context().internalize(fhv, false);
        return fhv;
    }

    app* slhv_syntax_maker::mk_fresh_boolvar() {
        app* fbv = this->fv_maker->mk_fresh_boolvar();
        return fbv;
    }

    app* slhv_syntax_maker::mk_fresh_locvar() {
        app* flv = this->fv_maker->mk_fresh_locvar();
        this->th->get_context().internalize(flv, false);
        return flv;
    }

    // connection making
    app* slhv_syntax_maker::mk_and(expr* lhs, expr* rhs) {
        return this->msw->use_mk_and(lhs, rhs);
    }
    app* slhv_syntax_maker::mk_implies(expr* lhs, expr* rhs) {
        return this->msw->use_mk_implies(lhs, rhs);
    }
    app* slhv_syntax_maker::mk_not(expr* inner) {
        return this->msw->use_mk_not(inner);
    }
    app* slhv_syntax_maker::mk_and(expr* arg1, expr* arg2, expr* arg3){
        return this->msw->use_mk_and(arg1, arg2, arg3);
    }
    app* slhv_syntax_maker::mk_and(int num_args, expr* const* args) {
        return this->msw->use_mk_and(num_args, args);
    }
    app* slhv_syntax_maker::mk_simplify_and(expr* f1, expr* f2) {
        if(this->th->get_manager().is_false(f1) || this->th->get_manager().is_false(f2)) {
            return this->th->get_manager().mk_false();
        }
        if(this->th->get_manager().is_true(f1) && !this->th->get_manager().is_true(f2)) {
            return to_app(f2);
        } else if (!this->th->get_manager().is_true(f1) && this->th->get_manager().is_true(f2)) {
            return to_app(f1);
        } else if(!this->th->get_manager().is_true(f1) && !this->th->get_manager().is_true(f2)){
            return this->msw->use_mk_and(f1, f2);
        } else {
            return this->th->get_manager().mk_true();
        }
    }
    app* slhv_syntax_maker::mk_or(expr* lhs, expr* rhs){
        return this->msw->use_mk_or(lhs, rhs);
    }
    app* slhv_syntax_maker::mk_or(expr* arg1, expr* arg2, expr* arg3){
        return this->msw->use_mk_or(arg1, arg2, arg3);
    }
    app* slhv_syntax_maker::mk_or(int num_args, expr* const* args){
        return this->msw->use_mk_or(num_args, args);
    }
    app* slhv_syntax_maker::mk_eq(expr* lhs, expr* rhs) {
        return this->msw->use_mk_eq(lhs, rhs);
    }
    app* slhv_syntax_maker::mk_distinct(expr* lhs, expr* rhs) {
        return this->msw->use_mk_distinct(lhs, rhs);
    }



    app* slhv_syntax_maker::mk_read_formula(app* from_hvar, app* read_addr, app* read_data) {
        SASSERT(this->th->is_hvar(from_hvar));
        app* fresh_hvar = this->mk_fresh_hvar();
        app* new_eq_left = from_hvar;
        int right_arg_num = 2;
        std::vector<app*> right_args;
        right_args.push_back(fresh_hvar);
        right_args.push_back(this->mk_points_to(read_addr, read_data));
        app* new_eq_right = this->mk_uplus_app(right_arg_num, right_args);
        // includes internalize:
        // literal result = this->th->mk_eq(new_eq_left, new_eq_right, false);

        // this->th->get_manager().inc_ref(new_eq_left);
        // this->th->get_manager().inc_ref(new_eq_right);
        // app_ref result(this->th->get_context().mk_eq_atom(new_eq_left, new_eq_right), this->th->get_manager());

        app* result = this->mk_eq(new_eq_left, new_eq_right);
        
        // this->th->get_context().internalize(result, false);
        return result;
    }

    app* slhv_syntax_maker::mk_read_formula_new(app* from_hvar, app* read_addr, int read_field, app* read_item) {
        // get the only record type out
        if(this->slhv_decl_plug->pt_record_map.size() != 1) {
            return nullptr;
        }
        int pt_locfield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_loc_num();
        int pt_datafield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_data_num();

        bool is_read_loc = false;
        if(read_field + 1 - pt_locfield_num>= 0) {
            is_read_loc = true;
        }
        int read_index = is_read_loc ? read_field : read_field - pt_locfield_num;
        if(is_read_loc) {
            app* fresh_hvar = this->mk_fresh_hvar();
            app* eq_lhs = from_hvar;
            std::vector<app*> locvars_vec;
            std::vector<app*> datavars_vec;
            for(int i = 0; i < pt_locfield_num; i ++) {
                if(i == read_index) {
                    locvars_vec.push_back(read_item);
                } else {
                    locvars_vec.push_back(this->mk_fresh_locvar());
                }
            }
            for(int i = 0; i < pt_datafield_num; i ++) {
                datavars_vec.push_back(this->mk_fresh_datavar());
            }
            SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
            pt_record* only_record = this->slhv_decl_plug->get_first_record();  
            app* rhs_record = this->mk_record(only_record, locvars_vec, datavars_vec);
            app* rhs_points_to = this->mk_points_to_new(read_addr, rhs_record);
            std::vector<app*> rhs_uplus_args;
            rhs_uplus_args.push_back(fresh_hvar);
            rhs_uplus_args.push_back(rhs_points_to);
            app* eq_rhs = this->mk_uplus_app(2, rhs_uplus_args);

            // this->th->get_manager().inc_ref(eq_lhs);
            // this->th->get_manager().inc_ref(eq_rhs);
            // app_ref result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());

            app* result = this->mk_eq(eq_lhs, eq_rhs);

            // this->th->get_context().internalize(result, false);
            return result;
        } else {
            app* fresh_hvar = this->mk_fresh_hvar();
            app* eq_lhs = from_hvar;
            std::vector<app*> locvars_vec;
            std::vector<app*> datavars_vec;
            for(int i = 0; i < pt_locfield_num; i ++) {
                locvars_vec.push_back(this->mk_fresh_locvar());
            }
            for(int i = 0; i < pt_datafield_num; i ++) {
                if(i == read_index) {
                    datavars_vec.push_back(read_item);
                } else {
                    app* temp_fv = this->mk_fresh_datavar();
                    datavars_vec.push_back(temp_fv);
                }
            }
            SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
            pt_record* only_record = this->slhv_decl_plug->get_first_record();
            app* rhs_record = this->mk_record(only_record, locvars_vec, datavars_vec);
            app* rhs_points_to = this->mk_points_to_new(read_addr, rhs_record);
            std::vector<app*> rhs_uplus_args;
            rhs_uplus_args.push_back(fresh_hvar);
            rhs_uplus_args.push_back(rhs_points_to);
            app* eq_rhs = this->mk_uplus_app(2, rhs_uplus_args);

            // this->th->get_manager().inc_ref(eq_lhs);
            // this->th->get_manager().inc_ref(eq_rhs);
            // app_ref result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());


            app* result = this->mk_eq(eq_lhs, eq_rhs);

            // this->th->get_context().internalize(result, false);
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
        app* first_eq_right = this->mk_uplus_app(2, first_uplus_args);
        // app* first_eq = this->th->mk_eq(first_eq_left, first_eq_right, false);
        
        // this->th->get_manager().inc_ref(first_eq_left);
        // this->th->get_manager().inc_ref(first_eq_right);
        
        // app_ref first_eq(this->th->get_context().mk_eq_atom(first_eq_left, first_eq_right), this->th->get_manager());

        app* first_eq = this->mk_eq(first_eq_left, first_eq_right);
        // this->th->get_context().internalize(first_eq, false);

        app* second_eq_left = writed_hvar;
        app* second_eq_right_pt = this->mk_points_to(write_addr, write_data);
        std::vector<app*> second_uplus_args;
        second_uplus_args.push_back(fresh_hvar);
        second_uplus_args.push_back(second_eq_right_pt);
        app* second_eq_right = this->mk_uplus_app(2, second_uplus_args);
        // app* second_eq = this->th->mk_eq(second_eq_left, second_eq_right, false);

        // this->th->get_manager().inc_ref(second_eq_left);
        // this->th->get_manager().inc_ref(second_eq_right);

        // app_ref second_eq(this->th->get_context().mk_eq_atom(second_eq_left, second_eq_right), this->th->get_manager());
        // this->th->get_context().internalize(second_eq, false);

        app* second_eq = this->mk_eq(second_eq_left, second_eq_right);
        app* final_result = this->mk_and(first_eq, second_eq);
        // the ast made by manager should be internalize manually
        // this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_write_formula_new(app* orig_hvar, app* writed_hvar, app* write_addr, int write_field, app* write_item) {
        if(this->slhv_decl_plug->pt_record_map.size() != 1) {
            return nullptr;
        }
        int pt_locfield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_loc_num();
        int pt_datafield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_data_num();
        bool is_write_loc = false;
        if(write_field + 1 - pt_locfield_num >= 0) {
            is_write_loc = true;
        }
        int write_index = is_write_loc ? write_field : write_field - pt_locfield_num;
            
        app* fresh_hvar = this->mk_fresh_hvar();
        std::vector<app*> first_locvars_vec;
        std::vector<app*> first_datavars_vec;
        for(int i = 0; i < pt_locfield_num; i ++) {
            first_locvars_vec.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < pt_datafield_num; i ++) {
            first_datavars_vec.push_back(this->mk_fresh_datavar());
        }

        app* first_eq_lhs = orig_hvar;
        
        SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
        pt_record* only_record = this->slhv_decl_plug->get_first_record();
        
        app* first_eq_rhs_record = this->mk_record(only_record, first_locvars_vec, first_datavars_vec);

        app* first_eq_rhs_pt = this->mk_points_to_new(write_addr, first_eq_rhs_record);
        std::vector<app*> first_eq_rhs_uplus_args;
        first_eq_rhs_uplus_args.push_back(fresh_hvar);
        first_eq_rhs_uplus_args.push_back(first_eq_rhs_pt);
        app* first_eq_rhs = this->mk_uplus_app(2, first_eq_rhs_uplus_args);


        // this->th->get_manager().inc_ref(first_eq_lhs);
        // this->th->get_manager().inc_ref(first_eq_rhs);
        
        // app_ref first_eq(this->th->get_context().mk_eq_atom(first_eq_lhs, first_eq_rhs), this->th->get_manager());

        app* first_eq = this->mk_eq(first_eq_lhs, first_eq_rhs);

        app* second_eq_lhs = writed_hvar;
        std::vector<app*> second_locvars_vec = first_locvars_vec;
        std::vector<app*> second_datavars_vec = first_datavars_vec;

        if(is_write_loc) {
            second_locvars_vec[write_index] = write_item;
        } else {
            second_datavars_vec[write_index] = write_item;
        }

        app* second_eq_rhs_record = this->mk_record(only_record, second_locvars_vec, second_datavars_vec);

        app* second_eq_rhs_pt = this->mk_points_to_new(write_addr, second_eq_rhs_record);

        std::vector<app*> second_eq_rhs_uplus_args;
        second_eq_rhs_uplus_args.push_back(second_eq_rhs_pt);
        second_eq_rhs_uplus_args.push_back(fresh_hvar);
        app* second_eq_rhs = this->mk_uplus_app(2, second_eq_rhs_uplus_args);

        // app_ref second_eq(this->th->get_context().mk_eq_atom(second_eq_lhs, second_eq_rhs), this->th->get_manager());
        
        app* second_eq = this->mk_eq(second_eq_lhs, second_eq_rhs);

        app* final_result = this->mk_and(first_eq, second_eq);
        // this->th->get_context().internalize(final_result, false);
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
        app* eq_rhs_uplus = this->mk_uplus_app(2, rhs_uplus_args);

        // this->th->get_manager().inc_ref(eq_lhs);
        // this->th->get_manager().inc_ref(eq_rhs_uplus);

        // app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs_uplus), this->th->get_manager());
        
        app* final_result = this->mk_eq(eq_lhs, eq_rhs_uplus);
        // this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_addr_in_hterm_new(app* hterm, app* addr) {
        if(this->slhv_decl_plug->pt_record_map.size() != 1) {
            return nullptr;
        }
        int pt_locfield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_loc_num();
        int pt_datafield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_data_num();

        app* fresh_unrelated_h = this->mk_fresh_hvar();
        std::vector<app*> record_fresh_locvars;
        std::vector<app*> record_fresh_datavars;
        for(int i = 0; i < pt_locfield_num; i ++) {
            record_fresh_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < pt_datafield_num; i ++) {
            record_fresh_datavars.push_back(this->mk_fresh_datavar());
        }
        SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
        pt_record* only_record = this->slhv_decl_plug->get_first_record();
        
        app* addr_pt_record = this->mk_record(only_record, record_fresh_locvars, record_fresh_datavars);

        app* rhs_pt = this->mk_points_to_new(addr, addr_pt_record);
        std::vector<app*> rhs_uplus_args;
        rhs_uplus_args.push_back(fresh_unrelated_h);
        rhs_uplus_args.push_back(rhs_pt);
        app* eq_lhs = hterm;
        app* eq_rhs_uplus = this->mk_uplus_app(2, rhs_uplus_args);
        
        // this->th->get_manager().inc_ref(eq_lhs);
        // this->th->get_manager().inc_ref(eq_rhs_uplus);
        
        // app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs_uplus), this->th->get_manager());
        app* final_result = this->mk_eq(eq_lhs, eq_rhs_uplus);
        // this->th->get_context().internalize(final_result, false);
        return final_result;
    }


    std::vector<app*> slhv_syntax_maker::mk_addr_in_hterm_multi(app* hterm, app* addr) {
        app* unrelated_h = this->mk_fresh_hvar();
        std::vector<app*> result;
        for(pt_record* r : this->slhv_decl_plug->get_all_pt_records()) {
            int curr_pt_loc_num = r->get_loc_num();
            int curr_pt_data_num = r->get_data_num();
            app* curr_eq_lhs = hterm;
            std::vector<app*> curr_eq_rhs_uplus_args;
            curr_eq_rhs_uplus_args.push_back(unrelated_h);
            std::vector<app*> fresh_locvars;
            std::vector<app*> fresh_datavars;
            for(int i = 0; i < curr_pt_loc_num; i ++) {
                fresh_locvars.push_back(this->mk_fresh_locvar());
            }
            for(int i = 0; i < curr_pt_data_num; i ++) {
                fresh_datavars.push_back(this->mk_fresh_datavar());
            }

            app* rhs_pt_record = this->mk_record(r, fresh_locvars, fresh_datavars);
            app* rhs_pt = this->mk_points_to_multi(addr, rhs_pt_record);
            curr_eq_rhs_uplus_args.push_back(rhs_pt);
            app* curr_eq_rhs = this->mk_uplus_app(2, curr_eq_rhs_uplus_args);

            // this->th->get_manager().inc_ref(curr_eq_lhs);
            // this->th->get_manager().inc_ref(curr_eq_rhs);

            // app* temp_result = this->th->get_manager().mk_eq(curr_eq_lhs, curr_eq_rhs);
            app* temp_result = this->mk_eq(curr_eq_lhs, curr_eq_rhs);
            // this->th->get_context().internalize(temp_result, false);
            result.push_back(temp_result);
        }
        return result;
    }

    app* slhv_syntax_maker::mk_addr_notin_hterm(app* hterm, app* addr) {
        app* fresh_whole_h = this->mk_fresh_hvar();
        app* fresh_data = this->mk_fresh_locvar();
        app* eq_lhs = fresh_whole_h;
        app* rhs_points_to = this->mk_points_to(addr, fresh_data);
        std::vector<app*> uplus_args;
        uplus_args.push_back(hterm);
        uplus_args.push_back(rhs_points_to);
        app* eq_rhs = this->mk_uplus_app(2, uplus_args);

        // this->th->get_manager().inc_ref(eq_lhs);
        // this->th->get_manager().inc_ref(eq_rhs);

        // app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());
        app* final_result = this->mk_eq(eq_lhs, eq_rhs);
        // this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_addr_notin_hterm_new(app* hterm, app* addr) {
        if(this->slhv_decl_plug->pt_record_map.size() != 1) {
            return nullptr;
        }
        int pt_locfield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_loc_num();
        int pt_datafield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_data_num();
        app* fresh_whole_h = this->mk_fresh_hvar();
        std::vector<app*> record_fresh_datavars;
        std::vector<app*> record_fresh_locvars;
        for(int i = 0; i < pt_locfield_num; i ++) {
            record_fresh_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < pt_datafield_num; i ++) {
            record_fresh_datavars.push_back(this->mk_fresh_datavar());
        }
        SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
        pt_record* only_record = this->slhv_decl_plug->get_first_record();
        app* rhs_record = this->mk_record(only_record, record_fresh_locvars, record_fresh_datavars);
        app* rhs_points_to = this->mk_points_to_new(addr, rhs_record);
        app* eq_lhs = fresh_whole_h;
        std::vector<app*> uplus_args;
        uplus_args.push_back(hterm);
        uplus_args.push_back(rhs_points_to);
        app* eq_rhs = this->mk_uplus_app(2, uplus_args);

        // this->th->get_manager().inc_ref(eq_lhs);
        // this->th->get_manager().inc_ref(eq_rhs);
        
        // app_ref final_result(this->th->get_context().mk_eq_atom(eq_lhs, eq_rhs), this->th->get_manager());
        app* final_result = this->mk_eq(eq_lhs, eq_rhs);
        // this->th->get_context().internalize(final_result, false);
        return final_result;
    }

    app* slhv_syntax_maker::mk_addr_notin_hterm_multi(app* hterm, app* addr) {
        app* fresh_whole_hvar = this->mk_fresh_hvar();
        pt_record* simplies_rec = this->slhv_decl_plug->get_simplies_record();
        app* eq_lhs = fresh_whole_hvar;
        std::vector<app*> eq_rhs_uplus_args;
        
        std::vector<app*> record_fresh_datavars;
        std::vector<app*> record_fresh_locvars;
        for(int i = 0; i < simplies_rec->get_loc_num(); i ++) {
            record_fresh_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < simplies_rec->get_data_num(); i ++) {
            record_fresh_datavars.push_back(this->mk_fresh_datavar());
        }
        app* rhs_record = this->mk_record(simplies_rec, record_fresh_locvars, record_fresh_datavars);
        app* rhs_pt = this->mk_points_to_multi(addr, rhs_record);
        eq_rhs_uplus_args.push_back(hterm);
        eq_rhs_uplus_args.push_back(rhs_pt);
        app* eq_rhs = this->mk_uplus_app(2, eq_rhs_uplus_args);

        app* result = this->mk_eq(eq_lhs, eq_rhs);
        
        // this->th->get_context().internalize(result, false);
        return result;
    }

   std::vector<std::vector<app*>> slhv_syntax_maker::mk_hterm_disequality(app* lhs_hterm, app* rhs_hterm) {
        #ifdef SLHV_PRINT
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


        app* ht1_to_hvar_eq = this->mk_eq(ht1_hvar, lhs_hterm);
        app* ht2_to_hvar_eq = this->mk_eq(ht2_hvar, rhs_hterm);
        // this->th->get_context().internalize(ht1_to_hvar_eq, false);
        // this->th->get_context().internalize(ht2_to_hvar_eq, false);


        // first disjunct
        app* first_conj_eq_lhs = ht1_hvar;
        std::vector<app*> first_conj_eq_rhs_uplus_args;
        app* first_eq_rhs_pt = this->mk_points_to(x, y);
        #ifdef SLHV_PRINT
        std::cout << " uplus rhs: " << mk_pp(h, this->th->get_manager()) << " " << h->get_sort()->get_name() << std::endl;
        std::cout << " uplus rhs: " << mk_pp(first_eq_rhs_pt, this->th->get_manager()) << " " << h->get_sort()->get_name() <<std::endl;
        first_eq_rhs_pt->get_sort();
        #endif
        first_conj_eq_rhs_uplus_args.push_back(h);
        first_conj_eq_rhs_uplus_args.push_back(first_eq_rhs_pt);
        app* first_conj_eq_rhs = this->mk_uplus_app(first_conj_eq_rhs_uplus_args.size(), first_conj_eq_rhs_uplus_args);

        // this->th->get_manager().inc_ref(first_conj_eq_lhs);
        // this->th->get_manager().inc_ref(first_conj_eq_rhs);

        // app_ref first_conj_eq(this->th->get_context().mk_eq_atom(first_conj_eq_lhs, first_conj_eq_rhs), this->th->get_manager());
        // this->th->get_context().internalize(first_conj_eq, false);
        app* first_conj_eq = this->mk_eq(first_conj_eq_lhs, first_conj_eq_rhs);
        app* second_conj_eq_lhs = ht2_hvar;
        app* second_conj_eq_rhs_pt = this->mk_points_to(x, z);
        std::vector<app*> second_conj_eq_rhs_uplus_args;
        second_conj_eq_rhs_uplus_args.push_back(h_prime);
        second_conj_eq_rhs_uplus_args.push_back(second_conj_eq_rhs_pt);
        app* second_conj_eq_rhs = this->mk_uplus_app(second_conj_eq_rhs_uplus_args.size(), second_conj_eq_rhs_uplus_args);

        // this->th->get_manager().inc_ref(second_conj_eq_lhs);
        // this->th->get_manager().inc_ref(second_conj_eq_rhs);

        // app_ref second_conj_eq(this->th->get_context().mk_eq_atom(second_conj_eq_lhs, second_conj_eq_rhs), this->th->get_manager());
        // this->th->get_context().internalize(second_conj_eq, false);


        app* second_conj_eq = this->mk_eq(second_conj_eq_lhs, second_conj_eq_rhs);

        app* third_conj_diseq = this->mk_distinct(y,z);

        
        // this->th->get_context().internalize(third_conj_diseq, false);


        std::vector<app*> first_disj;
        first_disj.push_back(first_conj_eq);
        first_disj.push_back(second_conj_eq);
        first_disj.push_back(third_conj_diseq);
        first_disj.push_back(ht1_to_hvar_eq);
        first_disj.push_back(ht2_to_hvar_eq);
        
        final_result.push_back(first_disj);

        // second disjunct
        #ifdef SLHV_PRINT
        std::cout << "second disjunct" << std::endl;
        #endif
        app* x_in_ht1 = this->mk_addr_in_hterm(ht1_hvar, x);
        app* x_notin_ht2 = this->mk_addr_notin_hterm(ht2_hvar, x);
        std::vector<app*> second_disj;
        second_disj.push_back(x_in_ht1);
        second_disj.push_back(x_notin_ht2);
        second_disj.push_back(ht1_to_hvar_eq);
        second_disj.push_back(ht2_to_hvar_eq);
        // this->th->get_context().internalize(x_in_ht1, false);
        // this->th->get_context().internalize(x_notin_ht2, false);
        final_result.push_back(second_disj);

        // third_disjunct

        #ifdef SLHV_PRINT
        std::cout << "third disjunct" << std::endl;
        #endif
        app* x_in_ht2 = this->mk_addr_in_hterm(ht2_hvar, x);
        app* x_notin_ht1 = this->mk_addr_notin_hterm(ht1_hvar, x);
        std::vector<app*> third_disj;
        third_disj.push_back(x_in_ht2);
        third_disj.push_back(x_notin_ht1);
        third_disj.push_back(ht1_to_hvar_eq);
        third_disj.push_back(ht2_to_hvar_eq);
        // this->th->get_context().internalize(x_in_ht2, false);
        // this->th->get_context().internalize(x_notin_ht1, false);
        final_result.push_back(third_disj);
        return final_result;
    }

    std::vector<std::vector<app*>> slhv_syntax_maker::mk_hterm_disequality_new(app* lhs, app* rhs) {
        if(this->slhv_decl_plug->pt_record_map.size() != 1) {
            SASSERT(false);
        }
        int pt_locfield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_loc_num();
        int pt_datafield_num = (*slhv_decl_plug->pt_record_map.begin()).second->get_data_num();

        SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
        pt_record* only_record = this->slhv_decl_plug->get_first_record();
        std::vector<std::vector<app*>> final_result;

        #ifdef SLHV_PRINT
        std::cout << "mk hterm disequality new" << std::endl;
        #endif

        app* ht1_hvar = this->mk_fresh_hvar();
        app* ht2_hvar = this->mk_fresh_hvar();


        app* ht1_to_hvar_eq = this->mk_eq(ht1_hvar, lhs);
        app* ht2_to_hvar_eq = this->mk_eq(ht2_hvar, rhs);
        // this->th->get_context().internalize(ht1_to_hvar_eq, false);
        // this->th->get_context().internalize(ht2_to_hvar_eq, false);
        // first disjunction batch
        app* h = this->mk_fresh_hvar();
        app* hp = this->mk_fresh_hvar();
        app* x = this->mk_fresh_locvar();

        std::vector<app*> ht1_pt_locvars;
        std::vector<app*> ht1_pt_datavars;
        std::vector<app*> ht2_pt_locvars;
        std::vector<app*> ht2_pt_datavars;

        for(int i = 0; i < pt_locfield_num; i ++) {
            ht1_pt_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < pt_datafield_num; i ++) {
            ht1_pt_datavars.push_back(this->mk_fresh_datavar());
        }
        for(int i = 0; i < pt_locfield_num; i ++) {
            ht2_pt_locvars.push_back(this->mk_fresh_locvar());
        }
        for(int i = 0; i < pt_datafield_num; i ++) {
            ht2_pt_datavars.push_back(this->mk_fresh_datavar());
        }

        app* ht1_eq_lhs = ht1_hvar;
        app* ht2_eq_lhs = ht2_hvar;

        app* ht1_eq_rhs_record = this->mk_record(only_record, ht1_pt_locvars, ht1_pt_datavars);
        app* ht2_eq_rhs_record = this->mk_record(only_record, ht2_pt_locvars, ht2_pt_datavars);

        app* ht1_eq_rhs_pt = this->mk_points_to_new(x, ht1_eq_rhs_record);
        app* ht2_eq_rhs_pt = this->mk_points_to_new(x, ht2_eq_rhs_record);

        std::vector<app*> ht1_eq_rhs_uplus_args;
        std::vector<app*> ht2_eq_rhs_uplus_args;

        ht1_eq_rhs_uplus_args.push_back(h);
        ht1_eq_rhs_uplus_args.push_back(ht1_eq_rhs_pt);

        ht2_eq_rhs_uplus_args.push_back(hp);
        ht2_eq_rhs_uplus_args.push_back(ht2_eq_rhs_pt);

        app* ht1_eq_rhs = this->mk_uplus_app(2, ht1_eq_rhs_uplus_args);
        app* ht2_eq_rhs = this->mk_uplus_app(2, ht2_eq_rhs_uplus_args);


        // this->th->get_manager().inc_ref(ht1_eq_lhs);
        // this->th->get_manager().inc_ref(ht1_eq_rhs);
        // this->th->get_manager().inc_ref(ht2_eq_lhs);
        // this->th->get_manager().inc_ref(ht2_eq_rhs);

        // app_ref ht1_eq(this->th->get_context().mk_eq_atom(ht1_eq_lhs, ht1_eq_rhs), this->th->get_manager());
        // app_ref ht2_eq(this->th->get_context().mk_eq_atom(ht2_eq_lhs, ht2_eq_rhs), this->th->get_manager());

        app* ht1_eq = this->mk_eq(ht1_eq_lhs, ht1_eq_rhs);
        app* ht2_eq = this->mk_eq(ht2_eq_lhs, ht2_eq_rhs);

        std::vector<expr*> one_field_distinct;
        for(int i = 0; i < pt_locfield_num; i ++) {            
            app* e = this->mk_distinct(ht1_pt_locvars[i], ht2_pt_locvars[i]);
            // this->th->get_context().internalize(e, false);
            one_field_distinct.push_back(e);
        }
        for(int i = 0; i < pt_datafield_num; i ++) {
            app* e = this->mk_distinct(ht1_pt_datavars[i], ht2_pt_datavars[i]);
            // this->th->get_context().internalize(e, false);
            one_field_distinct.push_back(e);
        }
        for(expr* e : one_field_distinct) {
            std::vector<app*> first_disj;
            first_disj.push_back(ht1_eq);
            first_disj.push_back(ht2_eq);
            first_disj.push_back(to_app(e));
            first_disj.push_back(ht1_to_hvar_eq);
            first_disj.push_back(ht2_to_hvar_eq);
            // this->th->get_context().internalize(ht1_eq, false);
            // this->th->get_context().internalize(ht2_eq, false);
            final_result.push_back(first_disj);
        } 
        // second disjunct
        #ifdef SLHV_PRINT
        std::cout << "second disjunct" << std::endl;
        #endif
        app* x_in_ht1 = this->mk_addr_in_hterm_new(ht1_hvar, x);
        app* x_notin_ht2 = this->mk_addr_notin_hterm_new(ht2_hvar, x);
        std::vector<app*> second_disj;
        second_disj.push_back(x_in_ht1);
        second_disj.push_back(x_notin_ht2);
        second_disj.push_back(ht1_to_hvar_eq);
        second_disj.push_back(ht2_to_hvar_eq);
        // this->th->get_context().internalize(x_in_ht1, false);
        // this->th->get_context().internalize(x_notin_ht2, false);
        final_result.push_back(second_disj);

        // third_disjunct

        #ifdef SLHV_PRINT
        std::cout << "third disjunct" << std::endl;
        #endif
        app* x_in_ht2 = this->mk_addr_in_hterm_new(ht2_hvar, x);
        app* x_notin_ht1 = this->mk_addr_notin_hterm_new(ht1_hvar, x);
        std::vector<app*> third_disj;
        third_disj.push_back(x_in_ht2);
        third_disj.push_back(x_notin_ht1);
        third_disj.push_back(ht1_to_hvar_eq);
        third_disj.push_back(ht2_to_hvar_eq);
        // this->th->get_context().internalize(x_in_ht2, false);
        // this->th->get_context().internalize(x_notin_ht1, false);
        final_result.push_back(third_disj);
        return final_result;
    }

    std::vector<std::vector<app*>> slhv_syntax_maker::mk_hterm_disequality_multi(app* lhs, app* rhs) {
        SASSERT(this->th->is_hvar(lhs));
        std::vector<std::vector<app*>> final_result;

        app* lhs_fresh_hvar = this->mk_fresh_hvar();
        app* rhs_fresh_hvar = this->mk_fresh_hvar();
        app* common_addr = this->mk_fresh_locvar();

        // all records are currently set to only data record
        
        // std::set<pt_record*> all_records = this->slhv_decl_plug->get_all_pt_records();
        std::set<pt_record*> all_records;
        for(pt_record* rc : this->slhv_decl_plug->get_all_pt_records()) {
            if(!rc->get_pt_record_name().compare("pt_record_1")) {
                all_records.insert(rc);
            }
        }

        bool rhs_is_hvar = (this->th->is_hvar(rhs));
        app* second_eq_lhs = nullptr;
        if(rhs_is_hvar) {
            second_eq_lhs = rhs;
        } else {
            app* second_eq_lhs_fhvar = this->mk_fresh_hvar();
            second_eq_lhs = second_eq_lhs_fhvar;
        }

        #ifdef SLHV_PRINT
        std::cout << "begin negation elimnation encoding" << std::endl;
        #endif
        for(pt_record* r1 : all_records) {
            for(pt_record* r2: all_records) {
                std::vector<app*> lhs_fresh_locvars;
                std::vector<app*> lhs_fresh_datavars;
                std::vector<app*> rhs_fresh_locvars;
                std::vector<app*> rhs_fresh_datavars;
                
                int r1_loc_num = r1->get_loc_num();
                int r1_data_num = r1->get_data_num();
                int r2_loc_num = r2->get_loc_num();
                int r2_data_num = r2->get_data_num();

                for(int i = 0; i < r1_loc_num; i ++) {
                    lhs_fresh_locvars.push_back(this->mk_fresh_locvar());
                }
                for(int i = 0; i < r2_loc_num; i ++) {
                    rhs_fresh_locvars.push_back(this->mk_fresh_locvar());
                }
                for(int i = 0; i < r1_data_num; i ++) {
                    lhs_fresh_datavars.push_back(this->mk_fresh_datavar());
                }
                for(int i = 0; i < r2_data_num; i ++) {
                    rhs_fresh_datavars.push_back(this->mk_fresh_datavar());
                }

                app* lhs_hterm_record = this->mk_record(r1, lhs_fresh_locvars, lhs_fresh_datavars);
                app* rhs_hterm_record = this->mk_record(r2, rhs_fresh_locvars, rhs_fresh_datavars);
                #ifdef SLHV_PRINT
                std::cout << "first equality" << std::endl;
                #endif
                // first equality
                app* first_eq_lhs = lhs;
                std::vector<app*> first_eq_rhs_uplus_args;
                first_eq_rhs_uplus_args.push_back(lhs_fresh_hvar);
                app* first_eq_rhs_pt = this->mk_points_to_multi(common_addr, lhs_hterm_record);
                first_eq_rhs_uplus_args.push_back(first_eq_rhs_pt);
                app* first_eq_rhs = this->mk_uplus_app(2, first_eq_rhs_uplus_args);

                app* first_eq = this->mk_eq(first_eq_lhs, first_eq_rhs);
                // this->th->get_context().internalize(first_eq, false);
                #ifdef SLHV_PRINT
                std::cout << "second equality" << std::endl;
                #endif
                // second equality
                
                std::vector<app*> second_eq_rhs_uplus_args;
                second_eq_rhs_uplus_args.push_back(rhs_fresh_hvar);
                app* second_eq_rhs_pt = this->mk_points_to_multi(common_addr, rhs_hterm_record);
                second_eq_rhs_uplus_args.push_back(second_eq_rhs_pt);
                app* second_eq_rhs = this->mk_uplus_app(2, second_eq_rhs_uplus_args);
                app* second_eq = this->mk_eq(second_eq_lhs, second_eq_rhs);
                // this->th->get_context().internalize(second_eq, false);
                if(r1 == r2) {
                    SASSERT(r1_data_num == r2_data_num && r1_loc_num == r2_loc_num);
                    // at least one field distinct
                    std::set<app*> all_possible_nequal;
                    for(int i = 0; i < r1_loc_num; i ++){
                        app* curr_ne = this->mk_distinct(lhs_fresh_locvars[i], rhs_fresh_locvars[i]);
                        // this->th->get_context().internalize(curr_ne, false);
                        all_possible_nequal.insert(curr_ne);
                    }
                    for(int i = 0; i < r1_data_num; i ++) {
                        app* curr_ne = this->mk_distinct(lhs_fresh_datavars[i], rhs_fresh_datavars[i]);
                        // this->th->get_context().internalize(curr_ne, false);
                        all_possible_nequal.insert(curr_ne);
                    }
                    for(app* nequal_form : all_possible_nequal) {
                        std::vector<app*> result;
                        if(!rhs_is_hvar) {

                            app* rhs_replace_eq = this->mk_eq(to_expr(second_eq_lhs), to_expr(rhs));
                            // this->th->get_context().internalize(rhs_replace_eq, false);
                            result.push_back(rhs_replace_eq);
                        }
                        result.push_back(first_eq);
                        result.push_back(second_eq);
                        result.push_back(nequal_form);
                        final_result.push_back(result);
                    }
                } else { 
                    std::vector<app*> result;
                    if(!rhs_is_hvar) {

                        app* rhs_replace_eq = this->mk_eq(to_expr(second_eq_lhs), to_expr(rhs));
                        // this->th->get_context().internalize(rhs_replace_eq, false);
                        result.push_back(rhs_replace_eq);
                    }
                    result.push_back(first_eq);
                    result.push_back(second_eq);
                    final_result.push_back(result);
                }
            }
        }

        #ifdef SLHV_PRINT
        std::cout << "lhs does not have common addr" << std::endl;
        #endif
        // lhs does not have common addr
        app* rhs_no_common_addr_hvar = second_eq_lhs;
        std::vector<app*> common_addr_in_lhs = this->mk_addr_in_hterm_multi(lhs, common_addr);
        app* common_notin_rhs = this->mk_addr_notin_hterm_multi(rhs_no_common_addr_hvar, common_addr);
        for(app* in_nequal : common_addr_in_lhs) {
            std::vector<app*> result;
            result.push_back(in_nequal);
            result.push_back(common_notin_rhs);
            final_result.push_back(result);
            if(!rhs_is_hvar) {

                app* rhs_replace_eq = this->mk_eq(to_expr(rhs_no_common_addr_hvar), to_expr(rhs));
                result.push_back(rhs_replace_eq);
            }
        }


        #ifdef SLHV_PRINT
        std::cout << "rhs does not have common addr" << std::endl;
        #endif
        // rhs does not have common addr
        std::vector<app*> common_addr_in_rhs = this->mk_addr_in_hterm_multi(rhs_no_common_addr_hvar, common_addr);
        app* common_notin_lhs = this->mk_addr_notin_hterm_multi(lhs, common_addr);
        for(app* in_nequal : common_addr_in_rhs) {
            std::vector<app*> result;
            result.push_back(in_nequal);
            result.push_back(common_notin_lhs);
            if(!rhs_is_hvar) {

                app* rhs_replace_eq = this->mk_eq(to_expr(rhs_no_common_addr_hvar), to_expr(rhs));
                result.push_back(rhs_replace_eq);
            }
            final_result.push_back(result);
        }
        return final_result;
    }

    app* slhv_syntax_maker::mk_uplus_app(int num_arg, std::vector<app*> hterm_args) {
        SASSERT(num_arg == hterm_args.size());
        for(app* t : hterm_args) {
            SASSERT(this->th->is_heapterm(t));
        }
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : hterm_args) {
            args_vec.push_back(arg);
            this->th->get_manager().inc_ref(arg);
        }
        sort* e_ref_sort = this->slhv_decl_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        sort_ref_vector sorts_vec(this->th->get_manager());
        for(int i = 0; i < num_arg; i ++) {
            sorts_vec.push_back(e_ref_sort);
        }
        // sort* e_ref_sort = this->th->get_manager().mk_sort(symbol(INTHEAP_SORT_STR), sort_info(this->th->get_id(), INTHEAP_SORT));
        func_decl* uplus_decl = this->slhv_decl_plug->mk_func_decl(OP_HEAP_DISJUNION, 0, nullptr, num_arg, sorts_vec.data(), e_ref_sort);
        app* result = this->th->get_manager().mk_app(uplus_decl, args_vec.data());
        this->th->get_context().internalize(result, false);
        return result;
    }

    app* slhv_syntax_maker::mk_points_to(app* addr_loc, app* data_loc) {
        SASSERT(this->th->is_locterm(addr_loc) && this->th->is_locterm(data_loc));
        
        std::vector<app*> args = {addr_loc, data_loc};
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : args) {
            this->th->get_manager().inc_ref(addr_loc);
            this->th->get_manager().inc_ref(data_loc);
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
        this->th->get_context().internalize(result, false);
        return result;
    }


    app* slhv_syntax_maker::mk_points_to_new(app* addr_loc, app* record_loc) {

        SASSERT(this->slhv_decl_plug->pt_record_decls.size() == 1);
        pt_record* only_record = this->slhv_decl_plug->get_first_record();
        func_decl* only_pt_r_decl = this->slhv_decl_plug->pt_record_decls[only_record->get_pt_record_name()];
        SASSERT(this->th->is_locterm(addr_loc));
        SASSERT(this->th->is_recordterm(record_loc));
        std::vector<app*> args = {addr_loc, record_loc};
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : args) {
            this->th->get_manager().inc_ref(arg);
            args_vec.push_back(arg);
        }
        sort* loc_sort = this->slhv_decl_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        sort* record_sort = only_pt_r_decl->get_range();
        sort_ref_vector sorts_vec(this->th->get_manager()); 
        sorts_vec.push_back(loc_sort);
        sorts_vec.push_back(record_sort);
        sort* e_ref_sort = this->slhv_decl_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        func_decl* pt_decl = this->slhv_decl_plug->mk_func_decl(OP_POINTS_TO, 0, nullptr, 2, sorts_vec.data(), e_ref_sort);
        app* result = this->th->get_manager().mk_app(pt_decl, args_vec);
        this->th->get_context().internalize(result, false);
        return result;
    }

    app* slhv_syntax_maker::mk_points_to_multi(app* addr_loc, app* record) {
        pt_record* record_template = this->th->analyze_pt_record_type(record);
        func_decl* curr_pt_r_decl = this->slhv_decl_plug->pt_record_decls[record_template->get_pt_record_name()];
        SASSERT(this->th->is_locterm(addr_loc));
        SASSERT(this->th->is_recordterm(record));
        std::vector<app*> args = {addr_loc, record};
        expr_ref_vector args_vec(this->th->get_manager());
        for(app* arg : args) {
            this->th->get_manager().inc_ref(arg);
            args_vec.push_back(arg);
        }
        sort* loc_sort = this->slhv_decl_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        sort* record_sort = curr_pt_r_decl->get_range();
        sort_ref_vector sorts_vec(this->th->get_manager());
        sorts_vec.push_back(loc_sort);
        sorts_vec.push_back(record_sort);
        sort* e_ref_sort = this->slhv_decl_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        func_decl* pt_decl = this->slhv_decl_plug->mk_func_decl(OP_POINTS_TO, 0, nullptr, 2, sorts_vec.data(), e_ref_sort);
        app* result = this->th->get_manager().mk_app(pt_decl, args_vec);
        this->th->get_context().internalize(result, false);
        return result;
    }


    app* slhv_syntax_maker::mk_record(pt_record* r, std::vector<app*> locvars, std::vector<app*> datavars) {
        int pt_locfield_num = r->get_loc_num();
        int pt_datafield_num = r->get_data_num();

        SASSERT(locvars.size() == pt_locfield_num);
        SASSERT(datavars.size() == pt_datafield_num);
        std::vector<app*> args;
        sort* loc_sort = this->slhv_decl_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        arith_util a(this->th->get_manager());
        sort* data_sort = a.mk_int();
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
            this->th->get_manager().inc_ref(arg);
            args_vec.push_back(arg);
        }
        func_decl* record_decl = this->slhv_decl_plug->pt_record_decls[r->get_pt_record_name()];
        #ifdef SLHV_PRINT
        std::cout << "make record " << record_decl->get_name() << " sort: " << std::endl;
        
        #endif
        app* result = this->th->get_manager().mk_app(record_decl, args_vec);
        #ifdef SLHV_PRINT
        std::cout << "record made: " << mk_ismt2_pp(result, this->th->get_manager()) << std::endl;
        #endif
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
        this->curr_boolvar_id = 0;
        locvar_map.clear();
        hvar_map.clear();
        datavar_map.clear();
        boolvar_map.clear();
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
        arith_util a(this->th->get_manager());
        std::string name = "f_th_datavar" + std::to_string(this->curr_datavar_id);
        family_id arith_family_id = this->th->get_manager().mk_family_id("arith");
        sort* range_sort = a.mk_int();
        unsigned num_args = 0;
        arith_decl_plugin* arith_plug = (arith_decl_plugin*)this->th->get_manager().get_plugin(arith_family_id);
        app* fresh_datavar = this->th->get_manager().mk_const(name, range_sort);
        curr_datavar_id ++;
        #ifdef SLHV_PRINT
        std::cout << "fresh datavar made: " << name << std::endl;
        #endif
        return fresh_datavar;
    }


    app* slhv_fresh_var_maker::mk_fresh_boolvar() {
        std::string name = "f_th_boolvar" + std::to_string(this->curr_boolvar_id);
        sort* boolsort = this->th->get_manager().mk_bool_sort();
        app* fresh_boolvar = this->th->get_manager().mk_const(name, boolsort);
        curr_boolvar_id++;
        return fresh_boolvar;
    }



    // model generation


    void theory_slhv::init_model(model_generator & mg)  {
        std::cout << "init model for slhv: arith factory, locvar_factory and heap factory" << std::endl;

        this->data_factory = alloc(arith_factory, this->m);
        // this->loc_factory = alloc(locvar_factory, this->m, this->get_family_id());

    }


    model_value_proc * theory_slhv::mk_value(enode * n, model_generator & mg) {
        // TODO READWRITE: add dependency here later
        theory_var v = n->get_th_var(get_id());
        expr* o = n->get_expr();
        #ifdef MODEL_GEN_INFO
        std::cout << "mk_value for " << mk_ismt2_pp(o, this->m) << std::endl;
        #endif
        arith_util a(this->m);
        app* oapp = to_app(o);
        if(this->is_heapterm(oapp)) {
            if(this->is_points_to(oapp)) {
                #ifdef MODEL_GEN_INFO
                std::cout << "is points to" << std::endl;
                #endif
                heap_value_proc* pt_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                enode* addr_enode = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* data_enode = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                pt_proc->add_dependency(model_value_dependency(addr_enode));
                pt_proc->add_dependency(model_value_dependency(data_enode));
                SASSERT(this->pt2proc.find(oapp) == this->pt2proc.end());
                enode* curr_enode = this->ctx.get_enode(oapp)->get_root();
                SASSERT(this->enode2proc.find(curr_enode) == this->enode2proc.end());
                this->enode2proc[curr_enode] = pt_proc;
                return pt_proc;
            } else if(this->is_hvar(oapp)) {
                #ifdef MODEL_GEN_INFO
                std::cout << "is hvar" << std::endl;
                #endif
                heap_value_proc* hvar_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                std::set<enode*> depended_nodes;
                for(app* dp_pt : this->hvar2ptset[oapp]) {
                    depended_nodes.insert(
                        this->ctx.get_enode(dp_pt)->get_root()
                    );
                }
                for(enode* dpn : depended_nodes ){
                    hvar_proc->add_dependency(model_value_dependency(dpn));
                }
                enode* curr_enode = this->ctx.get_enode(oapp)->get_root();
                SASSERT(this->enode2proc.find(curr_enode) == this->enode2proc.end());
                this->enode2proc[curr_enode] = hvar_proc;
                return hvar_proc;
            } else if(this->is_emp(oapp)) {
                
                #ifdef MODEL_GEN_INFO
                std::cout << "is emp" << std::endl;
                #endif
                heap_value_proc* emp_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                
                enode* curr_enode = this->ctx.get_enode(oapp)->get_root();
                SASSERT(this->enode2proc.find(curr_enode) == this->enode2proc.end());
                this->enode2proc[curr_enode] = emp_proc;
                return emp_proc;
            }
            else if(this->is_uplus(oapp)){
                #ifdef MODEL_GEN_INFO
                std::cout << "is uplus" << std::endl;
                #endif
                heap_value_proc* uplus_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                enode* curr_enode = this->ctx.get_enode(oapp)->get_root();
                SASSERT(this->enode2proc.find(curr_enode) == this->enode2proc.end());
                this->enode2proc[curr_enode] = uplus_proc;
                return uplus_proc;
            } else if(this->is_writedata(oapp)) {
                heap_value_proc* write_data_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                enode* written_heap_node = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* written_addr_node = this->ctx.get_enode(oapp->get_arg(1))->get_root();
                enode* written_data_node = this->ctx.get_enode(oapp->get_arg(2))->get_root();
                write_data_proc->add_dependency(model_value_dependency(written_heap_node));
                write_data_proc->add_dependency(model_value_dependency(written_addr_node));
                write_data_proc->add_dependency(model_value_dependency(written_data_node));
                return write_data_proc;
            } else if(this->is_writeloc(oapp)) {
                heap_value_proc* write_loc_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                enode* written_heap_node = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* written_addr_node = this->ctx.get_enode(oapp->get_arg(1))->get_root();
                enode* written_loc_node = this->ctx.get_enode(oapp->get_arg(2))->get_root();
                write_loc_proc->add_dependency(model_value_dependency(written_heap_node));
                write_loc_proc->add_dependency(model_value_dependency(written_addr_node));
                write_loc_proc->add_dependency(model_value_dependency(written_loc_node ));
                return write_loc_proc;
            } else {
                std::cout << "ERROR: mk heap value should not come here" << std::endl;
            }
        } else if(this->is_locterm(oapp)) {
            if(this->is_locvar(oapp)) {
                #ifdef MODEL_GEN_INFO
                std::cout << "is locvar" << std::endl;
                #endif
                std::string locvar_name = oapp->get_name().str();
                int int_val = this->model_loc_data_var_val_info[locvar_name];
                app* val_expr = data_factory->mk_num_value(rational(int_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else if(this->is_nil(oapp)){
                #ifdef MODEL_GEN_INFO
                std::cout << "is nil" << std::endl;
                #endif
                int nil_val = this->model_loc_data_var_val_info["nil"];
                app* val_expr = data_factory->mk_num_value(rational(nil_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else if(this->is_locadd(oapp)){
                
                SASSERT(this->is_locadd(oapp));
                #ifdef MODEL_GEN_INFO
                std::cout << "is locadd" << std::endl;
                #endif
                heap_value_proc* locadd_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTLOC_SORT, 0, nullptr));
                enode* left_enode = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* right_enode = this->ctx.get_enode(oapp->get_arg(1))->get_root();
                locadd_proc->add_dependency(model_value_dependency(left_enode));
                locadd_proc->add_dependency(model_value_dependency(right_enode));
                return locadd_proc;
            } else if(this->is_readloc(oapp)) {
                // TODO: add mk value for new functions
                heap_value_proc* readloc_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTLOC_SORT, 0, nullptr));
                enode* read_heap_node = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* read_addr_node = this->ctx.get_enode(oapp->get_arg(1))->get_root();
                readloc_proc->add_dependency(model_value_dependency(read_heap_node));
                readloc_proc->add_dependency(model_value_dependency(read_addr_node));
                return readloc_proc;
            } else if(this->is_int2loc(oapp)){
                heap_value_proc* int2loc_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTLOC_SORT, 0, nullptr));
                // buggy temp setting, should change to actual value later
                int int_val = 0;
                app* val_expr = data_factory->mk_num_value(rational(int_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else {
                std::cout << "should not come here in mk value: loc sort" << std::endl;
                return nullptr;
            }
        } else if(this->is_dataterm(oapp)) {
            if(this->is_datavar(oapp)) {
                #ifdef MODEL_GEN_INFO
                std::cout << "is datavar" << std::endl;
                #endif
                int data_var_val = this->model_loc_data_var_val_info[oapp->get_name().str()];
                app* val_expr = data_factory->mk_num_value(rational(data_var_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else if(this->is_loc2int(oapp)) {
                app* arg1 = to_app(oapp->get_arg(0));
                if(!this->is_locvar(arg1)) {
                    std::cout << "ERROR: loc2int inner not locvar" << std::endl;
                    return nullptr;
                }
                std::string locvar_name = arg1->get_name().str();
                int int_val = this->model_loc_data_var_val_info[locvar_name];
                app* val_expr = data_factory->mk_num_value(rational(int_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else if(this->is_readdata(oapp)) {
                heap_value_proc* readdata_proc = alloc(heap_value_proc, this->get_id(), this->get_manager().mk_sort(arith_family_id, INT_SORT));
                enode* read_heap_node = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* read_addr_node = this->ctx.get_enode(oapp->get_arg(1))->get_root();
                readdata_proc->add_dependency(model_value_dependency(read_heap_node));
                readdata_proc->add_dependency(model_value_dependency(read_addr_node));
                return readdata_proc;
            }
            else {
                #ifdef MODEL_GEN_INFO
                std::cout << "is arith term" << std::endl;
                #endif
                return alloc(expr_wrapper_proc, oapp);
            }
        } else {
            SASSERT(false);
        }
        return nullptr;
    }

    // statistics

    int theory_slhv::calculate_atomic_proposition(app* encoded_form) {
        int result = 0;
        if(encoded_form->is_app_of(basic_family_id, OP_EQ) ||  encoded_form->get_num_args() <= 1) {
            return 1;
        } else {
            for(int i = 0 ;i < encoded_form->get_num_args(); i ++) {
                result += this->calculate_atomic_proposition(to_app(encoded_form->get_arg(i)));
            }
            return result;
        }
    }


    

    app* memsafe_wrapper::use_mk_and(expr* lhs, expr* rhs) {
        // this->th->get_manager().inc_ref(lhs);
        // this->th->get_manager().inc_ref(rhs);
        app* result = this->th->get_manager().mk_and(lhs, rhs);
        return result;
    }

    app* memsafe_wrapper::use_mk_and(expr* arg1, expr* arg2, expr* arg3) {
        // this->th->get_manager().inc_ref(arg1);
        // this->th->get_manager().inc_ref(arg2);
        // this->th->get_manager().inc_ref(arg3);
        app* result =this->th->get_manager().mk_and(arg1, arg2, arg3);
        return result;
    }


    app* memsafe_wrapper::use_mk_and(unsigned num_args, expr * const * args) {
        // for(int i = 0; i < num_args; i ++) {
        //     this->th->get_manager().inc_ref(args[i]);
        // }
        app* result = this->th->get_manager().mk_and(num_args, args);
        return result;
    }

    app* memsafe_wrapper::use_mk_or(expr* lhs, expr* rhs){
        // this->th->get_manager().inc_ref(lhs);
        // this->th->get_manager().inc_ref(rhs);
        app* result = this->th->get_manager().mk_or(lhs, rhs);
        return result;
    }
    app* memsafe_wrapper::use_mk_or(expr* arg1, expr* arg2, expr* arg3) {
        // this->th->get_manager().inc_ref(arg1);
        // this->th->get_manager().inc_ref(arg2);
        // this->th->get_manager().inc_ref(arg3);
        app* result = this->th->get_manager().mk_or(arg1, arg2, arg3);
        return result;
    }

    app* memsafe_wrapper::use_mk_or(unsigned num_args, expr * const * args) {
        // for(int i = 0; i < num_args; i ++) {
        //     this->th->get_manager().inc_ref(args[i]);
        // }
        app* result = this->th->get_manager().mk_or(num_args, args);
        return result;
    }

    app* memsafe_wrapper::use_mk_implies(expr* premise, expr* conclusion) {
        // this->th->get_manager().inc_ref(premise);
        // this->th->get_manager().inc_ref(conclusion);
        app* result = this->th->get_manager().mk_implies(premise, conclusion);
        return result;
    }

    app* memsafe_wrapper::use_mk_not(expr* inner) {
        // this->th->get_manager().inc_ref(inner);
        app* result = this->th->get_manager().mk_not(inner);
        return result;
    }


    app* memsafe_wrapper::use_mk_eq(expr* lhs, expr* rhs) {
        // this->th->get_manager().inc_ref(lhs);
        // this->th->get_manager().inc_ref(rhs);
        app* result = this->th->get_manager().mk_eq(lhs, rhs);
        return result;
    }

    app* memsafe_wrapper::use_mk_distinct(expr* lhs, expr* rhs) {
        // this->th->get_manager().inc_ref(lhs);
        // this->th->get_manager().inc_ref(rhs);
        expr_ref_vector exprs(this->th->get_manager());
        exprs.push_back(lhs);
        exprs.push_back(rhs);
        app* result = this->th->get_manager().mk_distinct(2, exprs.data());
        return result;
    }

}