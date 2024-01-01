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
        #ifdef SLHV_DEBUG
        std::cout << "SLHV theory plugin created" << std::endl;
        #endif
        this->mem_mng = alloc(mem_management, this);
        this->msw = alloc(memsafe_wrapper, this);
        this->syntax_maker = alloc(slhv_syntax_maker, this, this->msw);

        this->global_emp = nullptr;
        this->global_nil = nullptr;
        this->reset_outside_configs();
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
        if(!is_uplus(term) && !is_points_to(term) && !is_locvar(term) && !is_hvar(term) && !is_nil(term) && !is_emp(term) && !is_locadd(term)) {
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
            #ifdef SLHV_DEBUG
            std::cout << "mk_theory_var for " << mk_ismt2_pp(term, m) << std::endl;
            #endif
            mk_var(e);
            #ifdef SLHV_DEBUG
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


    app* theory_slhv::mk_simplify_and(expr* f1, expr* f2) {
        if(this->get_manager().is_false(f1) || this->get_manager().is_false(f2)) {
            return this->get_manager().mk_false();
        }
        if(this->get_manager().is_true(f1) && !this->get_manager().is_true(f2)) {
            return to_app(f2);
        } else if (!this->get_manager().is_true(f1) && this->get_manager().is_true(f2)) {
            return to_app(f1);
        } else if(!this->get_manager().is_true(f1) && !this->get_manager().is_true(f2)){
            return this->msw->use_mk_and(f1, f2);
        } else {
            return this->get_manager().mk_true();
        }
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
        
        this->reset_outside_configs();
        // obtain outside assignments
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        // print outside assignments
        #if true
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
                refined_assignments.push_back(refined_e[0]);
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
                        refined_assignments.push_back(re);
                    }
                }
            }
        }
        // eliminate outside assignments that are of the form (uplus (uplus ..)..)
        // print refined assignments
        #if true
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
        #ifdef SLHV_DEBUG
        for(auto item : this->slhv_plug->pt_record_map) {
            std::cout << "record type name: " << item.first << std::endl;
            item.second->print(std::cout);
        }
        #endif

        #ifdef FRONTEND_NO_HEAP_NEQ
        std::vector<expr_ref_vector> elim_enums = this->remove_heap_eqaulity_negation_in_assignments(refined_assignments);
        #else
        //  enumerate all possible situations for negation imposed on hterm equalities
        std::vector<expr_ref_vector> elim_enums = this->eliminate_heap_equality_negation_in_assignments(refined_assignments);
        #endif

        #ifdef SLHV_DEBUG
        std::cout << "number of assignments after negations elimination: " << elim_enums.size() << std::endl;
        #endif
        
        // TODO implement inner CDCL framework here
        int elim_num = 0;
        for(expr_ref_vector curr_assignments : elim_enums) { 
            std::cout << "elim_num: " << elim_num++  << " of " << elim_enums.size()<< std::endl;
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
            #if true
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
            this->reset_inside_configs();
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
            numeral_solver->inc_ref();
            for(expr* e: numeral_cnstr_assignments) {
                numeral_solver->assert_expr(e);
            }
            lbool result =  numeral_solver->check_sat();
            #if true
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
                this->set_conflict_slhv(true);
                return false;
            } else if(result == l_true){
                model_ref nmd;
                numeral_solver->get_model(nmd);
                std::cout << "translated model: " << std::endl;
                model_smt2_pp(std::cout, this->m, *nmd, 0);
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
            // TODO: add reduction and solving
            std::pair<std::set<std::pair<heap_term*, heap_term*>> ,std::set<heap_term*> > all_hterms = extract_all_hterms();
            #if true
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

            // REDUCTION ENCODING
            expr* encoded_form  = fec->encode();

            #if true
            std::ofstream debug_formula("debug_encoded.txt", std::ios::out);
            debug_formula << mk_ismt2_pp(encoded_form, this->m);
            #endif
            // std::cout << "encoded form size: " ;
            // std::cout << this->calculate_atomic_proposition(to_app(encoded_form)) << std::endl;
            // expr* encoded_form = this->get_manager().mk_false();

            this->get_manager().inc_ref(encoded_form);
            std::cout << "encoded form ref count: " << encoded_form->get_ref_count() << std::endl;
            #if true
            std::cout << "============= encoded formula ========== " << std::endl;
            // std::cout << mk_ismt2_pp(encoded_form, this->m) << std::endl;
            std::cout << "======================================== " << std::endl;
            #endif
            
            solver* final_sovler = mk_smt_solver(this->m, params_ref(), symbol("QF_LIA"));
            final_sovler->inc_ref();
            for(expr* e: numeral_cnstr_assignments) {
                final_sovler->assert_expr(e);
            }
            final_sovler->assert_expr(encoded_form);
            lbool final_result = final_sovler->check_sat();
            std::cout << "XXXXXXXXXXXXXXXXX translated constraint result XXXXXXXXXXXXXXXXXXX" << std::endl;
            if(final_result == l_true) {
                std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET SAT XXXXXXXXXXXXXXXXXXXX" << std::endl;
                std::cout << " translated SAT " << std::endl;
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
                final_sovler->get_model(md);
                std::cout << "translated model: " << std::endl;
                // model_smt2_pp(std::cout, this->m, *md, 0);
                model_core& mdc = *md;
                for(int i = 0; i < mdc.get_num_constants(); i ++) {
                    expr_ref temp_val(this->m);
                    mdc.eval(mdc.get_constant(i), temp_val);
                    // #ifdef SLHV_DEBUG
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
                final_sovler->dec_ref();
                numeral_solver->dec_ref();
                this->m.dec_ref(encoded_form);

                for(expr* e : curr_assignments) {
                    this->get_manager().dec_ref(e);
                }
                this->mem_mng->dealloc_all();
                return true;
            } else if(final_result == l_false) { 
                std::cout << " translated UNSAT " << std::endl;
            } else {    
                std::cout << " translated UNKNOWN " << std::endl;
            }
            this->set_conflict_slhv(true);
            final_sovler->dec_ref();
            numeral_solver->dec_ref();
            this->m.dec_ref(encoded_form);

            this->mem_mng->dealloc_all();
            std::cout << "encoded form ref count after: " << encoded_form->get_ref_count() << std::endl;

            for(expr* e : curr_assignments) {
                this->get_manager().dec_ref(e);
            }
        }

        std::cout << "XXXXXXXXXXXXXXXXXXXX FINAL CHECK SET UNSAT XXXXXXXXXXXXXXXXXXXX" << std::endl;

        std::ofstream output2file("./outmodel.txt", std::ios::out);
        output2file << "UNSAT" << std::endl;
        this->check_status = slhv_unsat;
        // this->set_conflict_slhv(true, heap_cnstr_core);
        this->set_conflict_slhv(true);

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

    app* theory_slhv::eliminate_uplus_uplus_hterm(app* hterm) {
        if(this->is_uplus(hterm)) {
            bool has_iter = false;
            std::vector<app*> new_args;
            for(int i = 0; i < hterm->get_num_args(); i ++) {
                if(this->is_uplus(to_app(hterm->get_arg(i)))) {
                    has_iter = true;
                    app* uplus_i = this->eliminate_uplus_uplus_hterm(to_app(hterm->get_arg(i)));
                    for(int j = 0; j < uplus_i->get_num_args(); j ++) {
                        new_args.push_back(to_app(uplus_i->get_arg(j)));
                    }
                } else {
                    new_args.push_back(to_app(hterm->get_arg(i)));
                }
            }
            if(has_iter) {
                app* new_uplus = this->syntax_maker->mk_uplus_app(new_args.size(), new_args);   
                return new_uplus;
            } else {
                return hterm;
            }
        } else {
            return hterm;
        }
    }

    void theory_slhv::preprocessing(expr_ref_vector assigned_literals) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv preprocessing" << std::endl;
        #endif
        this->collect_and_analyze_assignments(assigned_literals);
        // collect different types of constraints
        this->collect_loc_heap_and_data_cnstr_in_assignments(assigned_literals);
        #ifdef SLHV_DEBUG
        std::cout << "slhv preprocessing end" << std::endl;
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

    std::vector<expr_ref_vector> theory_slhv::remove_heap_eqaulity_negation_in_assignments(expr_ref_vector assigned_literals) {
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
        for(app* pt : this->curr_pts) {
            this->curr_atomic_hterms.push_back(pt);
        }
        for(app* hv : this->curr_hvars ) {
            this->curr_atomic_hterms.push_back(hv);
        }
        this->curr_atomic_hterms.push_back(this->global_emp);
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
                        SASSERT(!to_app(e)->is_app_of(basic_family_id, OP_DISTINCT));
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


    void theory_slhv::reset_outside_configs() {
        std::cout << "reset configs for slhv theory" << std::endl;
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
        std::cout << "reset configs for slhv theory inner elim loop" << std::endl;
        
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
        #ifdef SLHV_DEBUG
        std::cout << "begin extract all hterms" << std::endl;
        #endif
        std::set<heap_term*> eq_hterms;
        std::set<std::pair<heap_term*, heap_term*>> eq_pair_hterms;
        for(app* eq : this->curr_heap_cnstr) {
            heap_term* eq_lhs = nullptr;
            heap_term* eq_rhs = nullptr;

            #if true
            std::cout << "extract for " << mk_ismt2_pp(eq, this->m) << std::endl;
            #endif
            SASSERT(eq != nullptr);
            SASSERT(eq->is_app_of(basic_family_id, OP_EQ));
            app* lhs_hterm = to_app(eq->get_arg(0));
            app* rhs_hterm = to_app(eq->get_arg(1));
            #ifdef SLHV_DEBUG
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
                }
            }
            #ifdef SLHV_DEBUG
            std::cout << "extract lhs hterm end" << std::endl;
            #endif
            #ifdef SLHV_DEBUG
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
                }
            }

            eq_pair_hterms.insert({eq_lhs, eq_rhs});
            #ifdef SLHV_DEBUG
            std::cout << "extract rhs hterm end" << std::endl;
            #endif
        }

        #ifdef SLHV_DEBUG
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

        #ifdef SLHV_DEBUG
        std::cout << " begin all heap term allocation" << std::endl;
        #endif
        for(std::vector<int> vec : next_all_counts) {
            heap_term* atom = alloc(heap_term, this, atomics, vec);
            all_hterms.insert(atom);
        }

        #ifdef SLHV_DEBUG
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


        #ifdef SLHV_DEBUG
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
        // #ifdef SLHV_DEBUG
        //     std::cout << "origin name: " << name << std::endl;
        // #endif
            if(name.find("ish") != name.npos) {
        // #ifdef SLHV_DEBUG
        //         std::cout << "deal with sh" << std::endl;
        // #endif
                std::vector<std::string> tokens = slhv_util::str_split(name, "_");
                SASSERT(tokens[0].compare("ish") == 0);
                int subsumed_id = atoi(tokens[1].data());
                int parent_id = atoi(tokens[2].data());
        // #ifdef SLHV_DEBUG
        //         std::cout << "subsumed id: " << subsumed_id << " parent id: " << parent_id << std::endl;
        // #endif
                subparent_pairs.insert({enc->get_ht_by_id(subsumed_id), enc->get_ht_by_id(parent_id)});
            } else if(name.find("idj") != name.npos) {
        // #ifdef SLHV_DEBUG
        //         std::cout << "deal with dj" << std::endl;
        // #endif
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
        // #ifdef SLHV_DEBUG
        // std::cout << "result size: " << result.size() << std::endl;
        // #endif
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
        int i = 0;
        for(heap_term* ht : all_hterms) {
            this->ht2index_map[ht] = i;
            this->index2ht.push_back(ht);
            i ++;
        }
        this->hts = all_hterms;
        this->eq_ht_pairs = eq_hterm_pairs;
        for(heap_term* ht : this->hts) {
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
        #ifdef SLHV_DEBUG
        std::cout << "formula encoder created" << std::endl;
        #endif

        this->ded = alloc(slhv_deducer, th, this);
        ded->deduce();
        ded->print_current(std::cout);
        std::cout << "deduce unsat: " << ded->get_is_unsat() << std::endl;
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
        } else {
            std::cout << "UNRESOLVED FORMULA: " << mk_ismt2_pp(formula, this->th->get_manager()) << std::endl;
            return formula;
        }
    }

    expr* formula_encoder::generate_deduced_premises() {
        std::cout << "generate deduce premises" << std::endl;
        if(this->ded->get_is_unsat()) {
            return this->th->get_manager().mk_false();
        }
        expr* result = this->th->get_manager().mk_true();
        for(auto p : this->ded->get_dj_pair_set()) {
            result = this->th->get_manager().mk_and(result, this->djrel_var_map[p]);
        }
        for(auto p : this->ded->get_sh_pair_set()) {
            result = this->th->get_manager().mk_and(result, this->shrel_var_map[p]);
        }
        return result;
    }

    expr* formula_encoder::generate_ld_formula() {
        std::cout << "generate ld formula" << std::endl;
        expr* result = this->th->get_manager().mk_true();
        for(app* loc_constraint : this->th->curr_loc_cnstr) {
            result = this->th->mk_simplify_and(result, this->translate_locdata_formula(loc_constraint));
        }
        for(app* data_constraint : this->th->curr_data_cnstr) {
            result = this->th->mk_simplify_and(result, this->translate_locdata_formula(data_constraint));
        }
        return result;
    }

    expr* formula_encoder::generate_init_formula() {
        std::cout << "generate init formula" << std::endl;
        expr* disj_form = this->th->get_manager().mk_true();
        for(heap_term* uplus_ht : this->hts) {
            if(uplus_ht->is_uplus_hterm()) {
                for(auto vec_pair : uplus_ht->get_all_distinct_atomic_pairs()) {
                    std::pair<heap_term*, heap_term*> htp = this->get_ht_pair_by_vec_pair(vec_pair);
                    if(!htp.first->is_emp() && !htp.second->is_emp()) {
                        disj_form = this->th->mk_simplify_and(disj_form, this->get_djrel_boolvar(htp.first, htp.second));
                    }

                }
            }
        }
        
        expr* emp_subsume_form = this->th->get_manager().mk_true();
        for(heap_term* ht : this->hts) {
            emp_subsume_form = this->th->mk_simplify_and(emp_subsume_form, this->get_shrel_boolvar(this->emp_ht, ht));
        }

        expr* sub_ht_form = this->th->get_manager().mk_true();
        for(heap_term* ht1 : this->hts) {
            for(heap_term* ht2 : this->hts) {
                if(!(ht1->is_emp() || ht2->is_emp()) && ht1->is_subhterm_of(ht2)) {
                    sub_ht_form = this->th->mk_simplify_and(sub_ht_form, this->get_shrel_boolvar(ht1, ht2));
                }
            }
        }

        expr* eq_induced_subht_form = this->th->get_manager().mk_true();
        for(std::pair<heap_term*, heap_term*> p : this->eq_ht_pairs) {
            eq_induced_subht_form = this->syntax_maker->mk_and(
                eq_induced_subht_form,
                this->get_shrel_boolvar(p.first, p.second),
                this->get_shrel_boolvar(p.second, p.first)
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

    expr* formula_encoder::generate_pto_formula() {
        std::cout << "generate pto formula" << std::endl;
        expr* first_conj = this->th->get_manager().mk_true();
        expr* second_conj = this->th->get_manager().mk_true();
        for(heap_term* pt : this->pt_hts) {
            for(heap_term* ptp : this->pt_hts) {
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
                    this->th->mk_simplify_and(
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

                for(heap_term* ht : this->hts) {
                    second_conj = this->th->mk_simplify_and(
                        second_conj,
                        this->syntax_maker->mk_implies(
                            this->th->mk_simplify_and(
                                this->get_shrel_boolvar(pt, ht),
                                this->get_shrel_boolvar(ptp, ht)
                            ),
                            this->syntax_maker->mk_or(
                                this->get_shrel_boolvar(pt, ptp),
                                this->get_djrel_boolvar(pt, ptp)
                            )
                        )
                    );
                }
            }
        }
        expr* result = this->th->mk_simplify_and(first_conj, second_conj);

        
        return result;
    }

    expr* formula_encoder::generate_iso_formula() {
        std::cout << "generate iso formula" << std::endl;
        expr* first_conj = this->th->get_manager().mk_true();
        expr* second_conj = this->th->get_manager().mk_true();
        expr* third_conj = this->th->get_manager().mk_true();

        for(heap_term* pt : this->pt_hts) {
            for(heap_term* ht : this->hts) {
                if(ht != this->emp_ht) {
                    expr* first_conj_ipl_lhs = this->get_shrel_boolvar(pt, ht);
                    expr* first_conj_ipl_rhs = this->th->get_manager().mk_false();
                    for(heap_term* a : this->get_sub_atom_hts(ht)) {
                        first_conj_ipl_rhs = this->syntax_maker->mk_or(first_conj_ipl_rhs, this->get_shrel_boolvar(pt, a));
                    }
                    first_conj = this->th->mk_simplify_and(
                        first_conj,
                        this->syntax_maker->mk_implies(first_conj_ipl_lhs, first_conj_ipl_rhs)
                    );
                }
            }
        }

        for(heap_term* ht1 : this->pt_hts) {
            for(heap_term* ht2 : this->hts) {
                for(heap_term* ht3 : this->hts) {
                    expr* second_conj_ipl_lhs = this->th->mk_simplify_and(
                        this->get_shrel_boolvar(ht1, ht2),
                        this->get_shrel_boolvar(ht2, ht3)
                    );
                    expr* second_conj_ipl_rhs =  this->get_shrel_boolvar(ht1, ht3);
                    second_conj = this->th->mk_simplify_and(
                        second_conj, 
                        this->syntax_maker->mk_implies(second_conj_ipl_lhs, second_conj_ipl_rhs)
                    );
                }
            }
        }

        // for(heap_term* compound_ht1 : this->hts) {
        //     for(heap_term* compound_ht2 : this->hts) {
        //         if(compound_ht1 != this->emp_ht && compound_ht2 != this->emp_ht) {
        //             std::set<std::pair<std::vector<int>, std::vector<int>>> compound_ht1_split_counts = compound_ht1->get_splitted_subpairs();
        //             std::set<std::pair<std::vector<int>, std::vector<int>>> compound_ht2_split_counts = compound_ht2->get_splitted_subpairs();
        //             for(auto ht1ht2_vec : compound_ht1_split_counts) {
        //                 auto ht1ht2 = this->get_ht_pair_by_vec_pair(ht1ht2_vec);
        //                 if(ht1ht2.first != this->emp_ht && ht1ht2.second != this->emp_ht) {
        //                     for(auto ht1pht2p_vec : compound_ht2_split_counts) {
        //                         auto ht1pht2p = this->get_ht_pair_by_vec_pair(ht1pht2p_vec);
        //                         if(ht1pht2p.first != this->emp_ht && ht1pht2p.first != this->emp_ht) {
        //                             expr* third_conj_impl_lhs = this->th->mk_simplify_and(
        //                                 this->get_shrel_boolvar(ht1ht2.first, ht1pht2p.first),
        //                                 this->get_shrel_boolvar(ht1ht2.second, ht1pht2p.second)
        //                             );
        //                             expr* third_conj_impl_rhs =  this->get_shrel_boolvar(compound_ht1, compound_ht2);
        //                             third_conj = this->th->mk_simplify_and(
        //                                 third_conj,
        //                                 this->syntax_maker->mk_implies(third_conj_impl_lhs, third_conj_impl_rhs)
        //                             );
        //                         }
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }

        // expr* result = this->syntax_maker->mk_and(first_conj, second_conj, third_conj);

        expr* result = this->syntax_maker->mk_and(first_conj, second_conj);
        return result;
    }

    expr* formula_encoder::generate_idj_formula() {

        std::cout << "generate idj formula" << std::endl;

        expr* result = this->th->get_manager().mk_true();
        for(heap_term* ht1 : this->pt_hts) {
            if(ht1 == this->emp_ht) {break;}
            for(heap_term* ht2 : this->pt_hts) {
                if(ht2 == this->emp_ht) {break;}
                for(heap_term* ht3 : this->hts) {
                    if(ht3 == this->emp_ht) {break;}
                    for(heap_term* ht4 : this->hts) {
                        if(ht4 == this->emp_ht) {break;}
                        expr* impl_lhs = this->syntax_maker->mk_and(
                            this->get_shrel_boolvar(ht1, ht3),
                            this->get_shrel_boolvar(ht2, ht4),
                            this->get_djrel_boolvar(ht3, ht4)
                        );
                        expr* impl_rhs = this->get_djrel_boolvar(ht1, ht2);
                        result = this->th->mk_simplify_and(
                            result,
                            this->syntax_maker->mk_implies(impl_lhs, impl_rhs)
                        );
                    }
                }
            }
        }

        return result;
    }

    expr* formula_encoder::generate_final_formula() {


        std::cout << "generate final formula" << std::endl;

        expr* result = this->th->get_manager().mk_true();
        for(heap_term* pt : this->pt_hts) {
            result = this->th->mk_simplify_and(
                result,
                this->syntax_maker->mk_not(this->get_shrel_boolvar(pt, this->emp_ht))
            );
        }

        return result;
    }

    expr* formula_encoder::generate_loc_var_constraints() {
        // generate locvar constraints
        std::cout << "generate loc var constraints" << std::endl;
        expr* result = this->th->get_manager().mk_true();
        arith_util a(this->th->get_manager());
        for(auto item : this->locvar2intvar_map) {
            SASSERT(this->th->is_locvar(item.first));
            if(this->th->is_nil(item.first)) {
                result = this->th->mk_simplify_and(
                    result,
                    a.mk_eq(item.second, a.mk_int(0))
                );
            } else {
                result = this->th->mk_simplify_and(
                    result,
                    a.mk_ge(item.second, a.mk_int(0))
                );
            }
        }
        for(app* curr_pt : this->th->curr_pts) {
            app* addr = to_app(curr_pt->get_arg(0));
            SASSERT(this->th->is_locvar(addr));
            result = this->th->mk_simplify_and(
                result,
                this->syntax_maker->mk_distinct(this->locvar2intvar(addr), a.mk_int(0))
            );
        }
        return result;
    }

    expr* formula_encoder:: encode() {
        std::cout << "==== begin encode" << std::endl;
        expr_ref_vector all_conj(this->th->get_manager());

        all_conj.push_back(this->generate_deduced_premises());
        all_conj.push_back(this->generate_ld_formula());
        all_conj.push_back(this->generate_init_formula());
        all_conj.push_back(this->generate_pto_formula());
        all_conj.push_back(this->generate_iso_formula());
        all_conj.push_back(this->generate_idj_formula());
        all_conj.push_back(this->generate_final_formula());
        all_conj.push_back(this->generate_loc_var_constraints());
        expr* result = this->syntax_maker->mk_and(
            all_conj.size(),
            all_conj.data()
        );
        std::cout << "==== end encode" << std::endl;
        return result;
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

    void slhv_deducer::initialize_shdj() {
        // RULE P2 and P3
        SASSERT(fec != nullptr);
        std::set<heap_term*> all_hterms = this->fec->get_all_hterms();
        std::set<std::pair<heap_term*, heap_term*>> all_eq_pairs = this->fec->get_eq_ht_pairs();
        heap_term* emp_ht = this->fec->get_emp_ht();
        for(heap_term* ht : all_hterms) {
            this->shpair_set.insert({this->ht2index[emp_ht], this->ht2index[ht]});
        }
        for(heap_term* ht1 : all_hterms) {
            for(heap_term* ht2 : all_hterms) {
                if(ht1->is_subhterm_of(ht2)) {
                    this->shpair_set.insert({this->ht2index[ht1], this->ht2index[ht2]});
                }
            }
        }
        for(heap_term* ht : all_hterms) {
            if(!(ht->is_atom_hvar() || ht->is_atom_pt())) {
                auto pset = ht->get_all_distinct_atomic_pairs();
                for(auto pair : pset) {
                    auto ht_pair = this->fec->get_ht_pair_by_vec_pair(pair);
                    if(!ht_pair.first->is_emp() && !ht_pair.second->is_emp()) {   
                        this->djpair_set.insert({this->ht2index[ht_pair.first], this->ht2index[ht_pair.second]});
                        this->djpair_set.insert({this->ht2index[ht_pair.second], this->ht2index[ht_pair.first]});
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
                    } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
                    } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
                    } else {
                        app* new_root = arg1;
                        this->ldvar2eqroot[arg1] = new_root;
                        this->ldvar2eqroot[arg2] = new_root;
                    }
                }
            } else if(dc->is_app_of(basic_family_id, OP_DISTINCT)) {
                app* arg1 = to_app(dc->get_arg(0));
                app* arg2 = to_app(dc->get_arg(1));
                if(this->th->is_datavar(arg1) && this->th->is_datavar(arg2))  {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                    }
                }
            } else if(dc->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(dc->get_arg(0));
                if(inner->is_app_of(basic_family_id, OP_EQ)) {
                    app* arg1 = to_app(inner->get_arg(0));
                    app* arg2 = to_app(inner->get_arg(1));
                    if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2))  {
                        if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg1].insert(arg2);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg2);
                            this->ldvar2neqvars[arg1] = new_neq_set;
                        }
                        if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg2].insert(arg1);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg1);
                            this->ldvar2neqvars[arg2] = new_neq_set;
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
                if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2)) {
                    #if true
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
                    } else if(this->ldvar2eqroot.find(arg1) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg2] = this->ldvar2eqroot[arg1];
                    } else if(this->ldvar2eqroot.find(arg2) != this->ldvar2eqroot.end()) {
                        this->ldvar2eqroot[arg1] = this->ldvar2eqroot[arg2];
                    } else {
                        app* new_root = arg1;
                        this->ldvar2eqroot[arg1] = new_root;
                        this->ldvar2eqroot[arg2] = new_root;
                    }
                }
            } else if(lc->is_app_of(basic_family_id, OP_DISTINCT)) {
                app* arg1 = to_app(lc->get_arg(0));
                app* arg2 = to_app(lc->get_arg(1));
                if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2)) {
                    if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg1].insert(arg2);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg2);
                        this->ldvar2neqvars[arg1] = new_neq_set;
                    }
                    if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                        this->ldvar2neqvars[arg2].insert(arg1);
                    } else {
                        std::set<app*> new_neq_set;
                        new_neq_set.insert(arg1);
                        this->ldvar2neqvars[arg2] = new_neq_set;
                    }
                }
            } else if(lc->is_app_of(basic_family_id, OP_NOT)) {
                app* inner = to_app(lc->get_arg(0));
                SASSERT(inner->is_app_of(basic_family_id, OP_EQ));
                app* arg1 = to_app(inner->get_arg(0));
                app* arg2 = to_app(inner->get_arg(1));
                if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2)) {
                    if(this->th->is_locvar(arg1) && this->th->is_locvar(arg2)) {
                        if(this->ldvar2neqvars.find(arg1) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg1].insert(arg2);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg2);
                            this->ldvar2neqvars[arg1] = new_neq_set;
                        }
                        if(this->ldvar2neqvars.find(arg2) != this->ldvar2neqvars.end()) {
                            this->ldvar2neqvars[arg2].insert(arg1);
                        } else {
                            std::set<app*> new_neq_set;
                            new_neq_set.insert(arg1);
                            this->ldvar2neqvars[arg2] = new_neq_set;
                        }
                    }
                }
            } else {
                std::cout << "unsupported loc constraint operation" << std::endl;
                SASSERT(false);
            }
        }
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
                has_new = has_new || this->add_ld_neq_vars(first_addr, second_addr);
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
                has_new = has_new || this->add_ld_eq_vars(first_addr, second_addr);
                has_new = has_new || this->add_ld_eq_vars(first_content, second_content);
            }
        }
        return has_new;
    }

    bool slhv_deducer::propagate_shdj_by_eq_neq() {
        // RULE P7
        bool new_sh_dj_found = false;
        std::set<std::pair<int, int>> nxt_shpair_set = this->shpair_set;
        std::set<std::pair<int, int>> nxt_djpair_set = this->djpair_set;
        for(auto sh_p1 : this->shpair_set) {
            for(auto sh_p2 : this->shpair_set) {
                if(sh_p1 != sh_p2 && sh_p1.second == sh_p2.second && 
                   this->is_pt(sh_p1.first) && this->is_pt(sh_p2.first)) {
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
                            #if true
                            std::cout << "5new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                            std::cout << "6new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                            #endif
                            nxt_djpair_set.insert(new_dj_pair);
                            nxt_djpair_set.insert(mirror_pair);
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
                            std::pair<int, int> new_dj_pair = {sh_p1.first, sh_p2.first};
                            std::pair<int, int> mirror_pair = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #if true
                            std::cout << "1new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                            std::cout << "2new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                            #endif
                            nxt_djpair_set.insert(new_dj_pair);
                            nxt_djpair_set.insert(mirror_pair);
                        }
                    } else if(this->ldvar2eqroot[first_addr_var] == this->ldvar2eqroot[second_addr_var]){
                        if(this->shpair_set.find({sh_p1.first, sh_p2.first}) != this->shpair_set.end()) {
                            // pair exists, do nothing
                        } else {
                            std::pair<int, int> new_sh_pair1 = {sh_p1.first, sh_p2.first};
                            std::pair<int, int> new_sh_pair2 = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #if true
                            std::cout << "new sh pair: " << new_sh_pair1.first << " << " << new_sh_pair1.second << std::endl;
                            #endif
                            nxt_shpair_set.insert(new_sh_pair1);
                        }
                        if(this->shpair_set.find({sh_p2.first, sh_p1.first}) != this->shpair_set.end()) {
                            // pair exists, do nothing
                        } else {
                            std::pair<int, int> new_sh_pair1 = {sh_p1.first, sh_p2.first};
                            std::pair<int, int> new_sh_pair2 = {sh_p2.first, sh_p1.first};
                            new_sh_dj_found = true;
                            #if true
                            std::cout << "new sh pair: " << new_sh_pair2.first << " << " << new_sh_pair2.second << std::endl;
                            #endif
                            nxt_shpair_set.insert(new_sh_pair2);
                        }
                    } else {
                        // do nothing, leave it to lia solving
                    }
                }
            }
        } 
        this->shpair_set = nxt_shpair_set;
        this->djpair_set = nxt_djpair_set;
        return new_sh_dj_found;
    }

    bool slhv_deducer::propagate_transitive_sh() {

        bool new_sh_found = false;
        std::set<std::pair<int, int>> nxt_shpair_set = this->shpair_set;
        for(auto sh_pair1 : this->shpair_set) {
            for(auto sh_pair2 : this->shpair_set) {
                if(sh_pair1.second == sh_pair2.first) {
                    if(this->shpair_set.find({sh_pair1.first, sh_pair2.second}) != this->shpair_set.end()) {
                        // do nothing
                    } else {
                        std::pair<int, int> new_pair = {sh_pair1.first, sh_pair2.second};
                        new_sh_found = true;
                        #if true
                        std::cout << "new sh pair: " << new_pair.first << " << " << new_pair.second << std::endl;
                        #endif
                        nxt_shpair_set.insert(new_pair);
                    }
                }
            }
        }

        this->shpair_set = nxt_shpair_set;
        return new_sh_found; 
    }

    bool slhv_deducer::propagate_transitive_dj() {
        bool new_dj_found = false;
        for(auto sh_pair13 : this->shpair_set) {
            for(auto sh_pair24 : this->shpair_set) {

                std::set<std::pair<int, int>> nxt_djpair_set = this->djpair_set;
                if(this->djpair_set.find({sh_pair13.second, sh_pair24.second}) != this->djpair_set.end()) {
                    if(this->djpair_set.find({sh_pair13.first, sh_pair24.first}) != this->djpair_set.end() ||
                    this->is_emp(sh_pair13.first) || 
                    this->is_emp(sh_pair24.first)) {
                        // do nothing
                    } else {
                        std::pair<int, int> new_dj_pair = {sh_pair13.first, sh_pair24.first};
                        std::pair<int, int> mirror_pair = {sh_pair24.first, sh_pair13.first};
                        new_dj_found = true;
                        #if true
                        std::cout << "3new dj pair: " << new_dj_pair.first << " # " << new_dj_pair.second << std::endl;
                        std::cout << "4new dj pair: " << mirror_pair.first << " # " << mirror_pair.second << std::endl;
                        #endif
                        nxt_djpair_set.insert(new_dj_pair);
                        nxt_djpair_set.insert(mirror_pair);
                    }
                }

                this->djpair_set = nxt_djpair_set;
            }
        }
        return new_dj_found;
    }

    bool slhv_deducer::add_ld_eq_vars(app* v1, app* v2) {
        #if true
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
                    std::cout << "eq root" << std::endl;
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
            std::cout << "add eq var error: different sort OR not vars" << std::endl;
            std::cout << mk_ismt2_pp(v1, this->th->get_manager()) << " " << mk_ismt2_pp(v2, this->th->get_manager()) << std::endl;
            SASSERT(false);
            return false;
        }
        return true;
    }   

    bool slhv_deducer::add_ld_neq_vars(app* v1, app* v2) {
        #if true
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

    void slhv_deducer::check_ldvars_consistency() {
        SASSERT(!this->unsat_found);
        for(auto item : this->ldvar2neqvars) {
            app* var1 = item.first;
            for(app* var2 : item.second) {
                if(this->ldvar2eqroot[var1] == this->ldvar2eqroot[var2]) {
                    this->unsat_found = true;
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
                this->unsat_found = true;
                return;
            }
        }
        this->unsat_found = false;
    }


    void check_pt_addr_nil();

    slhv_deducer::slhv_deducer(theory_slhv* th, formula_encoder* fec) {
        this->th = th;
        this->fec = fec;
        this->ht2index = this->fec->get_ht2index_map();
        this->index2ht = this->fec->get_index2ht();
        this->initialize_shdj();
        this->initialize_ldeqneq();
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
            has_change = false;
            std::cout << "propagate transitive sh" << std::endl;
            has_change = has_change || this->propagate_transitive_sh();
            this->check_sh_of_emp();
            if(this->unsat_found) {
                return false;
            }
            std::cout << "propagate transitive dj" << std::endl;
            has_change = has_change || this->propagate_transitive_dj();
            this->check_sh_of_emp();
            if(this->unsat_found) {
                return false;
            }
            std::cout << "propagate shdj by eq neq" << std::endl;
            has_change = has_change || this->propagate_shdj_by_eq_neq();
            this->check_sh_of_emp();
            if(this->unsat_found) {
                return false;
            }
            std::cout << "propagate eq neq" << std::endl;
            has_change = has_change || this->propagate_eq_neq();
            this->check_ldvars_consistency();
            if(this->unsat_found) {
                return false;
            }
        } while (has_change && !this->unsat_found);
        if(this->unsat_found) {
            return false;
        } else {
            return true;
        }
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
        #ifdef SLHV_DEBUG
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
        this->th->get_context().internalize(boolvar, false);
        return boolvar;
    }

    app* slhv_syntax_maker::mk_fresh_hvar() {
        app* fhv = this->fv_maker->mk_fresh_hvar();
        this->th->get_context().internalize(fhv, false);
        return fhv;
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
        app* final_result = this->th->mk_simplify_and(first_eq, second_eq);
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

        app* final_result = this->th->mk_simplify_and(first_eq, second_eq);
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


        app* ht1_to_hvar_eq = this->mk_eq(ht1_hvar, lhs_hterm);
        app* ht2_to_hvar_eq = this->mk_eq(ht2_hvar, rhs_hterm);
        // this->th->get_context().internalize(ht1_to_hvar_eq, false);
        // this->th->get_context().internalize(ht2_to_hvar_eq, false);


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
        // this->th->get_context().internalize(x_in_ht1, false);
        // this->th->get_context().internalize(x_notin_ht2, false);
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

        #ifdef SLHV_DEBUG
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
        #ifdef SLHV_DEBUG
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

        #ifdef SLHV_DEBUG
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

        #ifdef SLHV_DEBUG
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
                #ifdef SLHV_DEBUG
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
                #ifdef SLHV_DEBUG
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

        #ifdef SLHV_DEBUG
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


        #ifdef SLHV_DEBUG
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
        #ifdef SLHV_DEBUG
        std::cout << "make record " << record_decl->get_name() << " sort: " << std::endl;
        
        #endif
        app* result = this->th->get_manager().mk_app(record_decl, args_vec);
        #ifdef SLHV_DEBUG
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
        locvar_map.clear();
        hvar_map.clear();
        datavar_map.clear();
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
        #ifdef SLHV_DEBUG
        std::cout << "fresh datavar made: " << name << std::endl;
        #endif
        return fresh_datavar;
    }



    // model generation


    void theory_slhv::init_model(model_generator & mg)  {
        std::cout << "init model for slhv: arith factory, locvar_factory and heap factory" << std::endl;

        this->data_factory = alloc(arith_factory, this->m);
        // this->loc_factory = alloc(locvar_factory, this->m, this->get_family_id());

    }


    model_value_proc * theory_slhv::mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        expr* o = n->get_expr();
        #if true
        std::cout << "mk_value for " << mk_ismt2_pp(o, this->m) << std::endl;
        #endif
        arith_util a(this->m);
        app* oapp = to_app(o);
        if(this->is_heapterm(oapp)) {
            if(this->is_points_to(oapp)) {
                #if true
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
                // TODO: add dependency here later
                #if true
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
                
                #if true
                std::cout << "is emp" << std::endl;
                #endif
                heap_value_proc* emp_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                
                enode* curr_enode = this->ctx.get_enode(oapp)->get_root();
                SASSERT(this->enode2proc.find(curr_enode) == this->enode2proc.end());
                this->enode2proc[curr_enode] = emp_proc;
                return emp_proc;
            }
            else {
                SASSERT(this->is_uplus(oapp));
                #if true
                std::cout << "is uplus" << std::endl;
                #endif
                heap_value_proc* uplus_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTHEAP_SORT, 0, nullptr));
                enode* curr_enode = this->ctx.get_enode(oapp)->get_root();
                SASSERT(this->enode2proc.find(curr_enode) == this->enode2proc.end());
                this->enode2proc[curr_enode] = uplus_proc;
                return uplus_proc;
            }
        } else if(this->is_locterm(oapp)) {
            if(this->is_locvar(oapp)) {
                #if true
                std::cout << "is locvar" << std::endl;
                #endif
                std::string locvar_name = oapp->get_name().str();
                int int_val = this->model_loc_data_var_val_info[locvar_name];
                app* val_expr = data_factory->mk_num_value(rational(int_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else if(this->is_nil(oapp)){
                #if true
                std::cout << "is nil" << std::endl;
                #endif
                int nil_val = this->model_loc_data_var_val_info["nil"];
                app* val_expr = data_factory->mk_num_value(rational(nil_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else {
                SASSERT(this->is_locadd(oapp));
                #if true
                std::cout << "is locadd" << std::endl;
                #endif
                
                heap_value_proc* locadd_proc = alloc(heap_value_proc, this->get_id(), this->slhv_plug->mk_sort(INTLOC_SORT, 0, nullptr));
                enode* left_enode = this->ctx.get_enode(oapp->get_arg(0))->get_root();
                enode* right_enode = this->ctx.get_enode(oapp->get_arg(1))->get_root();
                locadd_proc->add_dependency(model_value_dependency(left_enode));
                locadd_proc->add_dependency(model_value_dependency(right_enode));
                return locadd_proc;
            }
        } else if(this->is_dataterm(oapp)) {
            if(this->is_datavar(oapp)) {
                #if true
                std::cout << "is datavar" << std::endl;
                #endif
                int data_var_val = this->model_loc_data_var_val_info[oapp->get_name().str()];
                app* val_expr = data_factory->mk_num_value(rational(data_var_val), true);
                return alloc(expr_wrapper_proc, val_expr);
            } else {
                #if true
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