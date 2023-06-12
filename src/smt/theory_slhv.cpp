#include "ast/ast_ll_pp.h"
#include "ast/slhv_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/theory_slhv.h"
namespace smt {

    // theory-slhv --------------------------------


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

            theory_var arg0_var = arg0_node->get_th_var(get_id());
            theory_var arg1_var = arg1_node->get_th_var(get_id());
            SASSERT(arg0_var != -1 && arg1_var != -1);
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

    bool theory_slhv::final_check() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv final_check()" << std::endl;
        std::cout << "current assignment: " << std::endl;
        #endif
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        // reset collected hvars, locvars and 
        this->reset_configs();

        //  enumerate all possible situations for negation imposed on hterm equalities
        std::vector<expr_ref_vector> evs = this->eliminate_heap_equality_negation_in_assignments(assignments);
        for(expr_ref_vector curr_assignments) {
            // reset info from previous curr_assignments
            this->reset_configs();

            // preprocessing
            this->preprocessing(assignments);

            // enumerate all possible loc eqs
            std::vector<std::map<enode*, std::set<app*>>> loc_eqs_raw = this->get_feasbible_locvars_eq();
            for(auto e : assignments) {
                /*-------------- learning enode -----------*/
                #ifdef SLHV_DEBUG
                std::cout << "current expr: " << mk_ismt2_pp(e, m) << std::endl;
                #endif
                // SASSERT(is_app_of(e, basic_family_id, OP_EQ) || is_app_of(e,     basic_family_id, OP_NOT));
                // app* equality = to_app(e);
                // expr* lhsExpr = std::get<0>(equality->args2());
                // expr* rhsExpr = std::get<1>(equality->args2());
                // theory_var lhsVar = get_th_var(lhsExpr);
                // theory_var rhsVar = get_th_var(rhsExpr);
                // std::cout << "lhsVar: " << lhsVar << std::endl;
                // std::cout << "rhsVar: " << rhsVar << std::endl;
                // enode* lhsNode = get_enode(lhsVar);
                // enode* rhsNode = get_enode(rhsVar);
                // #ifdef SLHV_DEBUG
                // std::cout << "lhsVar: " << lhsVar << std::endl;
                // std::cout << "lhsEnode: " << std::endl;
                // std::cout << mk_ismt2_pp(lhsNode->get_expr(), m) << " " <<   mk_ismt2_pp(lhsNode->get_root()->get_expr(), m) << std::endl;
                // enode* curr = lhsNode->get_root();
                // enode* head = curr;
                // std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
                // curr = curr->get_next();
                // while(curr != head) {
                //     std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
                //     curr = curr->get_next();
                // }
                // std::cout << std::endl;
                // std::cout << "rhsVar: " << rhsVar << std::endl;
                // std::cout << "rhsEnode: " << std::endl;
                // std::cout << mk_ismt2_pp(rhsNode->get_expr(), m) << " " <<   mk_ismt2_pp(rhsNode->get_root()->get_expr(), m) << std::endl;
                // curr = rhsNode->get_root();
                // head = curr;
                // std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
                // curr = curr->get_next();
                // while(curr != head) {
                //     std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
                //     curr = curr->get_next();
                // }
                // std::cout << std::endl;
                // #endif

                // SASSERT(is_app_of(lhsExpr, ctx.get_manager().mk_family_id("slhv"),   OP_HVAR_CONST));
                // if(!is_app_of(rhsExpr, ctx.get_manager().mk_family_id("slhv"),   OP_HEAP_DISJUNION)) {
                //     ctx.set_conflict(
                //         ctx.mk_justification(
                //         ext_theory_conflict_justification(
                //             get_id(), ctx, 0, nullptr, 0, nullptr, 0, nullptr
                //         ))
                //     );
                //     return false;
                // }
                }
            }
        
        return true;
    }

    void theory_slhv::set_conflict_slhv() {
        ctx.set_conflict(
            ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx, 0, nullptr, 0, nullptr, 0, nullptr
            ))
        );
    }

    void theory_slhv::preprocessing(expr_ref_vector assigned_literals) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv preprocessing" << std::endl;
        #endif
        this->collect_and_analyze_assignments(assigned_literals);
        this->record_distinct_locterms_in_assignments(assigned_literals);
        this->infer_distinct_locterms_in_assignments(assigned_literals);
        this->infer_distinct_heapterms_in_assignments(assigned_literals);
        this->infer_emp_hterms();
        // TODO: add the equivalence checking of nil
        #ifdef SLHV_DEBUG
        std::cout << "slhv preprocessing end" << std::endl;
        #endif
    }

    std::vector<expr_ref_vector> theory_slhv::elminate_heap_equality_negation_in_assignments(expr_ref_vector assigned_literals) {
        std::vector<std::vector<expr>> last_result;
        for(auto e : this->assigned_literals) {
            std::vector<std::vector<expr>> temp_result = this->eliminate_heap_equality_negation(last_result, e);
            last_result = temp_result;
        }
        std::vector<expr_ref_vector> final_result;
        for(std::vector<expr> ev : last_result) {
            expr_ref_vector ref_v(m);
            for(expr e : ev) {
                ref_v.append(e);
            }
            final_result.push_back(ref_v);
        }
        return last_result;
    }

    std::vector<std::vector<expr>> theory_slhv::eliminate_heap_equality_negation(std::vector<std::vector<expr>> eliminated_neg_vec, expr curr_neg_lit) {
        app* curr_lit = to_app(curr_neg_lit);
        if(is_app_of(curr_lit, basic_family_id, OP_NOT) || is_app_of(curr_lit, basic_family_id, OP_DISTINCT)) {
            if(curr_lit->is_app_of(basic_family_id, OP_NOT)) {
                app* equality = curr_lit->get_arg(0);
                SASSERT(equality->is_app_of(basic_family_id, OP_EQ));
                app* left_expr = equality->get_arg(0);
                app* right_expr = equality->get_arg(1);
                SASSERT(this->is_heapterm(left_expr) && this->is_heapterm   (right_expr));
                SASSERT(this->is_hvar(left_expr));
                std::vector<app*> three_disjuncts_after_elim = this->syntax_maker.mk_hterm_disequality(left_expr, right_expr);
                std::vector<std::vector<expr>> final_result;
                if(eliminated_neg_vec.size() != 0) {
                    for(std::vector<expr> ev : eliminated_neg_vec) {
                        for(app* disj : three_disjuncts_after_elim) {
                            std::vector<expr> result = ev;
                            result.push_back(disj);
                            final_result.push_back(result);
                        }
                    }
                } else {
                    for(app* disj : three_disjuncts_after_elim) {
                        std::vector<expr> result;
                        result.push_back(disj);
                        final_result.push_back(result);
                    }
                }
                return final_result;
            } else {
                std::cout << "eliminate heap equality negation: this should not   happen" << std::endl;
                SASSERT(false);
                return nullptr;
            }
        } else {
            std::vector<std::vector<expr>> final_result;
            for(std::vector<expr> v : eliminated_neg_vec) {
                std::vector<expr> result = v;
                result.push_back(curr_neg_lit);
                final_result.push_back(result);
            }
            return final_result;
        }
    }

    void theory_slhv::collect_and_analyze_assignments(expr_ref_vector assigned_literals) {
        #ifdef SLHV_DEBUG
        std::cout << "slhv collect and analze assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            #ifdef SLHV_DEBUG
            std::cout << "collect expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            app* app_e = to_app(e);
            auto collected_vars = this->collect_vars(app_e);
            this->curr_locvars = slhv_util::setUnion(this->curr_locvars, collected_vars.first);
            this->curr_hvars = slhv_util::setUnion(this->curr_hvars, collected_vars.second);            
            this->curr_disj_unions = slhv_util::setUnion(this->curr_disj_unions, this->collect_disj_unions(app_e));
            this->curr_pts = slhv_util::setUnion(this->curr_pts, this->collect_points_tos(app_e));
        }
        // if "emp" or "nil" does not appear in the literals, add and internalize them manually:
        slhv_decl_plugin* slhv_plugin = this->m.get_plugin(get_id());
        if(!this->curr_hvars_contain_emp()) {
            this->internalize_term(slhv_plugin->global_emp);
            this->curr_hvars.insert(slhv_plugin->global_emp);
            this->global_emp = slhv_plugin->global_emp;
        } else {
            SASSERT(this->global_emp == slhv_plugin->global_emp);
        }

        if(!this->curr_locvars_contain_nil()) {
            this->internalize_term(slhv_plugin->global_nil);
            this->curr_locvars.insert(slhv_plugin->global_nil);
            this->global_nil = slhv_plugin->global_nil;
        } else {
            SASSERT(this->global_nil == slhv_plugin->global_nil);
        }

    }

    std::pair<std::set<app* >, std::set<app *>> 
    theory_slhv::collect_vars(app* expression) {
        // collect all locvars and hvars appeared recursively.
        std::set<app*> collected_locvars;
        std::set<app*> collected_hvars;
        
        if(is_hvar(expression) ) {
            collected_hvars.insert(expression);
            return {collected_locvars, collected_hvars};
        } else if (is_emp(expression)){
            collected_hvars.insert(expression);
            this->global_emp = expression;
            return {collected_locvars, collected_hvars};
        } else if(is_locvar(expression)) {
            collected_locvars.insert(expression);
            return {collected_locvars, collected_hvars};
        } else if(is_nil(expression)) {
            collected_locvars.insert(expression);
            this->global_nil = expression;
            return {collected_locvars, collected_hvars};
        } else {
            for(int i = 0; i < expression->get_num_args(); i ++) {
                auto temp_result_pair = this->collect_vars(to_app(expression->get_arg(i)));
                collected_locvars = slhv_util::setUnion(collected_locvars, temp_result_pair.first);
                collected_hvars = slhv_util::setUnion(collected_hvars, temp_result_pair.second);
            }
            return {collected_locvars, collected_hvars};
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

    void theory_slhv::record_distinct_locterms_in_assignments(expr_ref_vector assigned_literals) {

        #ifdef SLHV_DEBUG
        std::cout << "record distinct locterms in assignments" << std::endl;
        #endif
        for(auto e : assigned_literals) {
            this->record_distinct_locterms(to_app(e));
        }
    }

    void theory_slhv::record_distinct_locterms(app* atom) {
        // record all locterm enode that are distinct 
        #ifdef SLHV_DEBUG
        std::cout << "record distinct locvars: " << mk_ismt2_pp(atom, m) << std::endl;
        #endif
        if(atom->is_app_of(basic_family_id, OP_DISTINCT)) {
            expr* lhs_expr = atom->get_arg(0);
            expr* rhs_expr = atom->get_arg(1);
            SASSERT(lhs_expr->get_sort()->get_name() == rhs_expr->get_sort()->get_name());
            if(this->is_locterm(to_app(lhs_expr))) {
                theory_var lhsVar = get_th_var(lhs_expr);
                theory_var rhsVar = get_th_var(rhs_expr);
                enode* lhs_node = get_enode(lhsVar);
                enode* rhs_node = get_enode(rhsVar);
                this->curr_distinct_locterm_pairs.insert({lhs_node->get_root(), rhs_node->get_root()});
            }
            
        } else if(atom->is_app_of(basic_family_id, OP_NOT)) {
            expr* negated = atom->get_arg(0);
            SASSERT(to_app(negated)->is_app_of(basic_family_id, OP_EQ));
            expr* lhs_expr = to_app(negated)->get_arg(0);
            expr* rhs_expr = to_app(negated)->get_arg(1);
            SASSERT(lhs_expr->get_sort()->get_name() == rhs_expr->get_sort()->get_name());
            if(this->is_locterm(to_app(lhs_expr))) {
                theory_var lhsVar = get_th_var(lhs_expr);
                theory_var rhsVar = get_th_var(rhs_expr);
                enode* lhs_node = get_enode(lhsVar);
                enode* rhs_node = get_enode(rhsVar);
                this->curr_distinct_locterm_pairs.insert({lhs_node->get_root(), rhs_node->get_root()});
            }
        } 
    }

    
    void theory_slhv::collect_loc_and_heap_cnstr_in_assignments(expr_ref_vector assigned_literals){
        // collect all constrainst imposed on heap and loc
        for(auto e : assigned_literals) {
            if(to_app(e)->is_app_of(basic_family_id, OP_NOT)) {
                expr* negated = to_app(e)->get_arg(0);
                expr* negated_arg0 = to_app(e)->get_arg(0);
                if(is_heapterm(to_app(negated_arg0))) {
                    this->curr_heap_cnstr.insert(to_app(e));
                } else if(is_locterm(to_app(negated_arg0))) {
                    this->curr_loc_cnstr.insert(to_app(e));
                } else {
                    SASSERT(false);
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
                        SASSERT(false);
                        // this should not happen
                    }
                }
            }
        }
    }


    void theory_slhv::reset_configs() {
        this->curr_pts.clear();
        this->curr_disj_unions.clear();
        this->curr_hvars.clear();
        this->curr_locvars.clear();

        this->curr_distinct_locterm_pairs.clear();
        this->curr_loc_cnstr.clear();
        this->curr_heap_cnstr.clear();

        this->curr_distinct_locterm_pairs.clear();
        this->curr_emp_hterm_enodes.clear();
        this->curr_notnil_locterms_enodes.clear();
    }

    // check_logic

    std::map<enode*, std::set<app*>> theory_slhv::get_coarse_locvar_eq() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv get_coarse_locvar_eq" << std::endl;
        #endif
        std::map<enode*, std::set<app*>> unique_node_map;
        for(app* locvar : this->curr_locvars) {
            theory_var lv = get_th_var(locvar);
            enode* lnode = get_enode(lv)->get_root();
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
                result.push_back({nodes[i], nodes[j]});
            }
        }
        return result;
    }


    std::map<enode*, std::set<app*>> theory_slhv::get_fine_locvar_eq(std::set<enode_pair> &assigned_pairs){
        #ifdef SLHV_DEBUG
        std::cout << "slhv get_fine_locvar_eq" << std::endl;
        #endif
        auto unique_node_map = std::move(this->get_coarse_locvar_eq());


        std::map<enode*, std::set<app*>> result = unique_node_map;
        for(enode_pair p : assigned_pairs) {
            if(!slhv_util::setEqual(result[p.first->get_root()], result[p.second->get_root()])) {
                std::set<app*> firstSet = result[p.first];
                std::set<app*> secondSet = result[p.second];
                std::set<app*> mergedSet = slhv_util::setUnion(firstSet, secondSet);
                result[p.first] = mergedSet;
                result[p.second] = mergedSet;
            }
        }

        return result;
    }

    std::vector<std::map<enode*, std::set<app*>>> theory_slhv::get_feasbible_locvars_eq() {
        #ifdef SLHV_DEBUG
        std::cout << "slhv get_feasible_locvars_eq" << std::endl;
        #endif
        // enumerate all feasible assignment to assignable locvar enode pairs
        // the result is a vector of map, where each map represents a way to do the partition of locvar eq
        std::vector<enode_pair> unassigned_pairs = this->get_unassigned_locvar_pairs();
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
        // TODO: should be optimized here
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
        for(auto e : all_assigned_situations) {
            result_maps.push_back(this->get_fine_locvar_eq(e));
        }
        return result_maps;
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
                            this->set_conflict_slhv();
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
                    expr* addr_i = disj_pts[i]->get_arg(0);
                    expr* addr_j = disj_pts[j]->get_arg(0);
                    enode* node_addr_i = ctx.get_enode(addr_i);
                    enode* node_addr_j = ctx.get_enode(addr_j);
                    enode* nil_root = this->ctx.get_enode(this->global_nil)->get_root();
                    if(node_addr_i->get_root() == node_addr_j->get_root() ||
                       node_addr_i->get_root() == nil_root || 
                       node_addr_j->get_root() == nil_root) {
                        // UNSAT
                        // reason: two identical addr in one disj_union term
                        // or one of them is equal to nil
                        this->check_status = slhv_unsat;
                        this->set_conflict_slhv();
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
        std::cout << "slhv infer_distinct_locterms: " << mk_ismt2_pp(expr, m) << std::endl;
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
        for(app * atom : assigned_hcnstrs) {
            this->infer_distinct_heapterms(app);
        }
    };

    void theory_slhv::infer_distinct_heapterms(app* atom){
        SASSERT(atom->is_app_of(basic_family_id, OP_EQ));
        app* left_var = atom->get_arg(0);
        SASSERT(this->is_hvar(left_var));
        app* right_expr = atom->get_arg(1);
        if(this->is_uplus(right_expr)) {
            enode* emp_root = this->ctx.get_enode(this->global_emp)->get_root();
            enode* left_var_root_node = this->ctx.get_enode(left_var)->get_root();
            bool contain_points_to = false;
            for(app* arg : right_expr->get_args()) {
                if(this->is_points_to(arg)) {
                    contain_points_to = true;
                    break;
                }
            }
            this->curr_distinct_hterm_pairs.insert({emp_root, left_var_root_node});
            for(app* arg : right_expr->get_args()) {
                if(this->is_hvar(arg)) {
                    enode* rhs_var_root_node = this->ctx.get_enode(arg)->get_root();
                    this->curr_distinct_hterm_pairs.insert({left_var_root_node, rhs_var_root_node});
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

    locvar_eq::locvar_eq(theory_slhv& t, std::map<enode*, std::set<app*>>& fine_d) {
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
        if(this->fine_data[th.get_context().get_enode(loc1)->get_root()] == 
           this->fine_data[th.get_context().get_enode(loc2)->get_root()]) {
                return true;
           } else {
                return false;
           }
    }

    app* locvar_eq::get_leader_locvar(app* loc) {
        if(this->is_nil(loc)) {
            return this->th.global_nil;
        } else {
            return this->fine_data[th.get_context().get_enode(loc)->get_root()][0];
        }
    }

    bool locvar_eq::is_nil(app* loc) {
        enode* loc_root = this->th.get_context().get_enode(loc)->get_root();
        for(app* l : this->fine_data[loc_root]) {
            if(l == this->th.global_nil) {
                return true;
            }
        }
        return false;
    }


    std::vector<app*> locvar_eq::get_leader_locvars() {
        std::vector<app*> result;
        result.push_back(this->th.global_nil);
        for(auto pair : fine_data) {
            if(this->is_nil(pair.second[0])) {
                
            } else {
                result.push_back(pair.second[0]);
            }
        }
        return result;
    }

    coarse_hvar_eq::coarse_hvar_eq(theory_slhv& t) {
        this->th = t;
        for(app* hvar : this->th.curr_hvars) {
            enode* hvar_enode_root = this->th.get_context().get_enode(hvar)->get_root();
            if(coarse_data[hvar_enode_root]) {
                coarse_data[hvar_enode_root].push_back(hvar);
            } else {
                std::vector<app*> varsvec;
                varsvec.push_back(hvar);
                coarse_data[hvar_enode_root] = varsvec;
            }
        }
    }

    int coarse_hvar_eq::is_in_same_class(app* hvar1, app* hvar2) {
        enode* hvar1_root_node = this->th.get_context().get_enode(hvar1)->get_root();
        enode* hvar2_root_node = this->th.get_context().get_enode(hvar2)->get_root();
        if(hvar1_root_node == hvar2_root_node) {
            return 1;
        } else  {
            return -1;
        }
    }


    app* coarse_hvar_eq::get_leader_hvar(app* hvar) {
        enode* hvar_root_node = this->th.get_context().get_enode(hvar)->get_root();
        if(this->is_emp_hvar(hvar)) {
            return this->th.global_emp;
        } else {
            return this->coarse_data[hvar_root_node][0];
        }
    }

    int coarse_hvar_eq::is_emp_hvar(app* hvar) {
        enode* hvar_root_node = this->th.get_context().get_enode(hvar)->get_root();
        if(this->th.curr_emp_hterm_enodes.find(hvar_root_node) != this->th.curr_emp_hterm_enodes.end() || 
           this->th.get_context().get_enode(this->th.global_emp)->get_root() == hvar_root_node) {
            return 1;
        } else {
            return -1;
        }
    }


    std::vector<app*> coarse_hvar_eq::get_leader_hvars() {
        std::vector<app*> result;
        result.push_back(this->th.global_emp);
        for(auto pair : this->coarse_data) {
            bool pair_is_emp = false;
            for(app* temp_hvar : pair.second) {
                if(this->is_emp_hvar(temp_hvar)) {
                    pair_is_emp = true;
                    break;
                }
            }
            if(!pair_is_emp) {
                result.push_back(pair.second[0]);
            }
        }
        return result;
    }


    edge_labelled_dgraph::edge_labelled_dgraph(theory_slhv& t, locvar_eq& l, coarse_hvar_eq& h) {
        this->th = t;
        this->loc_eq = l;
        this->hvar_eq = h;
        this->construct_graph_from_theory();
    }

    void edge_labelled_dgraph::construct_graph_from_theory() {
        // construct nodes
        
        std::map<app*, dgraph_node*> node_map;
        std::vector<app*> leader_hvars = this->hvar_eq.get_leader_hvars();
        for(int i = 0; i < leader_hvars.size; i ++) {
            SASSERT(!node_map[leader_hvars[i]]);
            dgraph_node* new_node = alloc(hvar_dgraph_node, *this, leader_hvars[i]);
            node_map[leader_hvars[i]] = new_node;
            this->nodes.push_back(new_node);
        }
        std::set<std::pair<app*, app*>> addr_data_pairs;
        
        for(app* pt : this->th.curr_pts) {
            app* addr_loc_leader = this->loc_eq.get_leader_locvar(pt->get_arg(0));
            app* data_loc_leader = this->loc_eq.get_leader_locvar(pt->get_arg(1));
            addr_data_pairs.insert({addr_loc_leader, data_loc_leader});
        }
        for(auto pair : addr_data_pairs) {
            dgraph_node* new_node = alloc(pt_dgraph_node, *this, pair.first, pair.second);
            this->nodes.push_back(new_node);
        }

        // construct edges
        for(app* heap_equality : this->th.curr_heap_cnstr) {
            SASSERT(is_app_of(heap_equality, basic_family_id, OP_EQ));
            app* left_hvar = heap_equality->get_arg(0);
            dgraph_node* from_dgraph_node = this->get_hvar_node(left_hvar);
            app* label = heap_equality->get_arg(1);
            if(this->th.is_uplus(label)) {
                // add edge if rhs of the equality is a uplus, since otherwise 
                // the equivalent class of hvar has already dealed with it
                for(int i = 0; i < label->get_num_args(); i ++) {
                    app* dst = label->get_arg(i);
                    dgraph_node* temp_to_dgraph_node = nullptr;
                    if(this->th.is_hvar(dst) || this->th.is_emp(dst)) {
                        temp_to_dgraph_node = this->get_hvar_node(dst);
                    } else if(this->th.is_points_to(dst)){
                        temp_to_dgraph_node = this->get_pt_node(dst);
                    } else {
                        SASSERT(false);
                        std::cout << "create dgraph edge: Currently unsupport !!" << std::endl;
                    }

                    dgraph_edge* new_edge = alloc(dgraph_edge, from_dgraph_node, temp_to_dgraph_node, label);
                    if(!this->has_edge(new_edge)) {
                        this->edges.push_back(new_edge);
                    }
                }
            }
        }
    }


    hvar_dgraph_node* edge_labelled_dgraph::get_hvar_node(app* orig_hvar){
        app* leader_hvar = this->hvar_eq.get_leader_hvar(orig_hvar);
        for(dgraph_node* n : nodes) {
            if(n->is_hvar()) {
                if(((hvar_dgraph_node *) n)->get_hvar_label() == leader_hvar) {
                    return n;
                }
            }
        }
        std::cout << "get_hvar_dgraph_node error!!" << std::endl;
        return nullptr;
    }

    pt_dgraph_node* edge_labelled_dgraph::get_pt_node(app* orig_pt){
        app* orig_addr_loc = orig_pt->get_arg(0);
        app* orig_data_loc = orig_pt->get_arg(1);
        app* leader_addr_loc = this->loc_eq.get_leader_locvar(orig_addr_loc);
        app* leader_data_loc = this->loc_eq.get_leader_locvar(orig_data_loc);
        for(dgraph_node* n : nodes) {
            if(n->is_points_to()) {
                if(((pt_dgraph_node*)n)->get_pt_pair_label().first == leader_addr_loc &&
                   ((pt_dgraph_node*)n)->get_pt_pair_label().second == leader_data_loc) {
                    return n;
                }
            }
        }
        std::cout << "get_pt_dgraph_node error!!" << std::endl;
        return nullptr;
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

    dgraph_node::dgraph_node(edge_labelled_dgraph& g) {
        this->dgraph = g;
    }


    hvar_dgraph_node::hvar_dgraph_node(edge_labelled_dgraph& g, app* hvar) {
        dgraph_node(g);
        this->leader_hvar = hvar;
    }

    pt_dgraph_node::pt_dgraph_node(edge_labelled_dgraph& g, app* pt_addr, app* pt_data) {
        dgraph_node(g);
        this->pt_addr_leader = pt_addr;
        this->pt_data_leader = pt_data;
    }

    // syntax maker

    slhv_syntax_maker::slhv_syntax_maker(theory_slhv& th) {
        this->th = th;
    }

    void slhv_syntax_maker::reset_fv_num() {
        this->fv_maker.reset();
    }

    app* slhv_syntax_maker::mk_fresh_hvar() {
        return this->fv_maker.mk_fresh_hvar();
    }

    app* slhv_syntax_maker::mk_fresh_locvar() {
        return this->fv_maker.mk_fresh_locvar();
    }

    app* slhv_syntax_maker::mk_read_formula(app* from_hvar, app* read_addr, app* read_data) {
        SASSERT(this->th.is_hvar(from_hvar));
        app* fresh_hvar = this->mk_fresh_hvar();
        app* new_eq_left = from_hvar();
        int right_arg_num = 2;
        std::vector<app*> right_args;
        right_args.push_back(fresh_hvar);
        right_args.push_back(this->mk_points_to(read_addr, read_data));
        app* new_eq_right = this->mk_uplus(right_arg_num, right_args);
        // includes internalize:
        literal* result = this->th.mk_eq(new_eq_left, new_eq_right, false);
        return to_app(result);
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
        app* first_eq = this->th.mk_eq(first_eq_left, first_eq_right, false);

        app* second_eq_left = writed_hvar;
        app* second_eq_right_pt = this->mk_points_to(write_addr, write_data);
        std::vector<app*> second_uplus_args;
        second_uplus_args.push_back(fresh_hvar);
        second_uplus_args.push_back(second_eq_right_pt);
        app* second_eq_right = this->mk_uplus(2, second_uplus_args);
        app* second_eq = this->th.mk_eq(seoncd_eq_left, second_eq_right, false);

        std::vector<app*> literals;
        literals.push_back(first_eq);
        literals.push_back(second_eq);
        app* final_result = this->th.get_manager().mk_and(2, literals);
        // the ast made by manager should be internalize manually
        this->th.ctx.internalize(final_result, false);
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
        app* final_result = this->th.mk_eq(eq_lhs, eq_rhs_uplus);
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
        app* final_result = this->th.mk_eq(eq_lhs, eq_rhs);
        return final_result;
    }

    std::vector<app*> slhv_syntax_maker::mk_hterm_disequality(app* lhs_hterm, app* rhs_hterm) {
        app* h = this->mk_fresh_hvar();
        app* h_prime = this->mk_fresh_hvar();
        app* x = this->mk_fresh_locvar();
        app* y = this->mk_fresh_locvar();
        app* z = this->mk_freappsh_locvar();
        std::vector<app*> final_result;

        // first disjunct
        app* first_conj_eq_lhs = lhs_hterm;
        std::vector<app*> first_conj_eq_rhs_uplus_args;
        app* first_eq_rhs_pt = this->mk_points_to(x, y);
        first_conj_eq_rhs_uplus_args.push_back(h);
        fisrt_conj_eq_rhs_uplus_args.push_back(first_eq_rhs_pt);
        app* first_conj_eq_rhs = this->mk_uplus(first_conj_eq_rhs_uplus_args.size(), first_conj_eq_rhs_uplus_args);
        app* first_conj_eq = this->th.mk_eq(first_conj_eq_lhs, first_conj_eq_rhs);
        
        app* second_conj_eq_lhs = rhs_hterm;
        app* second_conj_eq_rhs_pt = this->mk_points_to(x, z);
        std::vector<app*> second_conj_eq_rhs_uplus_args;
        second_conj_eq_rhs_uplus_args.push_back(h_prime);
        second_conj_eq_rhs_uplus_args.push_back(second_conj_eq_rhs_pt);
        app* second_conj_eq_rhs = this->mk_uplus(second_conj_eq_rhs_uplus_args.size(), second_conj_eq_rhs_uplus_args);
        app* second_conj_eq = this->th.mk_eq(second_conj_eq_lhs, second_conj_eq_rhs);

        expr_ref_vector distinct_pair(this->th.m);
        distinct_pair.append(y);
        distinct_pair.append(z);
        app* third_conj_diseq = this->th.get_manager().mk_distinct(2, distinct_pair.data());
        this->th.get_context().internalize(third_conj_diseq);


        std::vector<app*> first_disjunct_literals;
        first_disjunct_literals.push_back(first_conj_eq);
        first_disjunct_literals.push_back(second_conj_eq);
        first_disjunct_literals.push_back(third_conj_diseq);
        app* first_disj = this->th.get_manager().mk_and(3, first_disjunct_literals);
        this->th.get_context().internalize(first_disj);
        final_result.push_back(first_disj);

        // second disjunct
        app* x_in_ht1 = this->mk_addr_in_hterm(lhs_hterm, x);
        app* x_notin_ht2 = this->mk_addr_notin_hterm(rhs_hterm, x);
        std::vector<app*> second_disjunct_literals;
        second_disjunct_literals.push_back(x_in_ht1);
        second_disjunct_literals.push_back(x_notin_ht2);
        app* second_disj = this->th.get_manager().mk_and(2, second_disjunct_literals);
        this->th.get_context().internalize(second_disj);
        final_result.push_back(second_disj);

        // third_disjunct
        app* x_in_ht2 = this->mk_addr_in_hterm(rhs_hterm, x);
        app* x_notin_ht1 = this->mk_addr_notin_hterm(lhs_hterm, x);
        std::vector<app*> third_disjunct_literals;
        third_disjunct_literals.push_back(x_notin_ht1);
        third_disjunct_literals.push_back(x_in_ht2);
        app* third_disj = this->th.get_manager().mk_and(2, third_disjunct_literals);
        this->th.get_context().internalize(third_disj);
        final_result.push_back(third_disj);
        return final_result;
    }

    app* slhv_syntax_maker::mk_uplus(int num_arg, std::vector<app*> hterm_args) {
        SASSERT(num_arg == hterm_args.size());
        for(app* t : hterm_args) {
            SASSERT(this->th.is_heapterm(t));
        }
        expr_ref e_ref(this->th.m);
        this->th.m.mk_app(symbol("uplus"), num_arg, hterm_args, nullptr, nullptr, e_ref);
        return e_ref.get();
    }

    app* slhv_syntax_maker::mk_points_to(app* addr_loc, app* data_loc) {
        SASSERT(this->th.is_locterm(addr_loc) && this->th.is_locterm(data_loc));
        std::vector<app*> args = {addr_loc, data_loc};
        expr_ref e_ref(this->th.m);
        this->th.m.mk_app(symbol("pt"), 2, args, 0, nullptr, nullptr, e_ref);
        return e_ref.get();
    }
    // fresh var maker

    slhv_fresh_var_maker::slhv_fresh_var_maker(theory_slhv& t) {
        this->th = t;
        slhv_decl_plugin* slhv_plugin = this->th.m.get_plugin(get_id());
        this->fe_plug = slhv_plugin;
    }

    slhv_fresh_var_maker::reset() {
        this->curr_locvar_id = 0;
        this->curr_hvar_id = 0;
        locvar_map.clear();
        hvar_map.clear();
    }

    app* slhv_fresh_var_maker::mk_fresh_hvar() {
        std::string name = "f_th_hvar" + std::to_string(this->curr_hvar_id);
        sort* range_sort = this->fe_plug->mk_sort(INTHEAP_SORT, 0, nullptr);
        app* fresh_hvar = this->fe_plug->mk_const_hvar(range_sort, 0, nullptr);
        this->hvar_map[curr_hvar_id] = fresh_hvar;
        curr_hvar_id ++;
        return fresh_hvar;
    }

    app* slhv_fresh_var_maker::mk_fresh_locvar() {
        std::string name = "f_th_locvar" + std::to_string(this->curr_locvar_id);
        sort* range_sort = this->fe_plug->mk_sort(INTLOC_SORT, 0, nullptr);
        app* fresh_locvar = this->fe_plug->mk_const_locvar(range_sort, 0, nullptr);
        this->locvar_map[curr_locvar_id] = fresh_locvar;
        curr_locvar_id ++;
        return fresh_locvar;
    }
}