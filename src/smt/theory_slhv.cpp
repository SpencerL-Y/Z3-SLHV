#include "ast/ast_ll_pp.h"
#include "ast/slhv_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/theory_slhv.h"
namespace smt {

    // theory-slhv --------------------------------
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
        if(!is_uplus(term) && !is_points_to(term) && !is_locvar(term) && !is_hvar(term)) {
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
        // pre-analysis and determine the equivalence relation on loctation variables
        this->collect_and_analyze_assignments(assignments);
        this->record_distinct_locterms_in_assignments(assignments);
        // TODO: implement theory check here
        
        for(auto e : assignments) {
            /*-------------- learning enode -----------*/
            #ifdef SLHV_DEBUG
            std::cout << "current expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            SASSERT(is_app_of(e, basic_family_id, OP_EQ) || is_app_of(e, basic_family_id, OP_NOT));
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
            // std::cout << mk_ismt2_pp(lhsNode->get_expr(), m) << " " << mk_ismt2_pp(lhsNode->get_root()->get_expr(), m) << std::endl;
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
            // std::cout << mk_ismt2_pp(rhsNode->get_expr(), m) << " " << mk_ismt2_pp(rhsNode->get_root()->get_expr(), m) << std::endl;
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

            // SASSERT(is_app_of(lhsExpr, ctx.get_manager().mk_family_id("slhv"), OP_HVAR_CONST));
            // if(!is_app_of(rhsExpr, ctx.get_manager().mk_family_id("slhv"), OP_HEAP_DISJUNION)) {
            //     ctx.set_conflict(
            //         ctx.mk_justification(
            //         ext_theory_conflict_justification(
            //             get_id(), ctx, 0, nullptr, 0, nullptr, 0, nullptr
            //         ))
            //     );
            //     return false;
            // }
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


    void theory_slhv::collect_and_analyze_assignments(expr_ref_vector assigned_literals) {
        for(auto e : assigned_literals) {
            #ifdef SLHV_DEBUG
            std::cout << "collect expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            app* app_e = to_app(e);
            auto collected_vars = this->collect_vars(app_e);
            this->curr_locvars = slhv_util::setUnion(this->curr_locvars, collected_vars.first);
            this->curr_hvars = slhv_util::setUnion(this->curr_hvars, collected_vars.second);
            
            this->curr_disj_unions = slhv_util::setUnion(this->curr_disj_unions, this->collect_disj_unions(app_e));
        }
    }

    std::pair<std::set<app* >, std::set<app *>> 
    theory_slhv::collect_vars(app* expression) {
        // collect all locvars and hvars appeared recursively.
        std::set<app*> collected_locvars;
        std::set<app*> collected_hvars;
        
        if(is_hvar(expression)) {
            collected_hvars.insert(expression);
            return {collected_locvars, collected_hvars};
        } else if(is_locvar(expression)) {
            collected_locvars.insert(expression);
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

    void theory_slhv::record_distinct_locterms_in_assignments(expr_ref_vector assigned_literals) {
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

    void theory_slhv::collect_heap_cnstr_in_assignments(expr_ref_vector assigned_literals){

    }

    void theory_slhv::reset_configs() {
        this->curr_disj_unions.clear();
        this->curr_hvars.clear();
        this->curr_locvars.clear();

        this->curr_distinct_locterm_pairs.clear();
    }

    // check_logic

    std::map<enode*, std::set<app*>> theory_slhv::get_coarse_locvar_eq() {
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

    std::vector<enode_pair> theory_slhv::unassigned_locvar_pairs(){
        std::map<enode*, std::set<app*>> unique_node_map = this->get_coarse_locvar_eq();
        std::vector<enode*> nodes;
        for(auto record : unique_node_map) {
            nodes.push_back(record.first);
        }

        std::vector<enode_pair> result;
        for(int i = 0; i < nodes.size(); i ++ ) {
            for(int j = i + 1; i < nodes.size(); j ++) {
                result.push_back({nodes[i], nodes[j]});
            }
        }
        return result;
    }

    std::vector<std::map<enode*, std::set<app*>>> theory_slhv::get_feasbible_locvars_eq() {
        // enumerate all feasible assignment to assignable locvar enode pairs
        // the result is a vector of map, where each map represents a way to do the partition of locvar eq
        std::vector<enode_pair> unassigned_pairs = this->unassigned_locvar_pairs();
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




    std::map<enode*, std::set<app*>> theory_slhv::get_fine_locvar_eq(std::set<enode_pair> &assigned_pairs){
        auto unique_node_map = std::move(this->get_coarse_locvar_eq());


        std::map<enode*, std::set<app*>> result = unique_node_map;
        for(enode_pair p : assigned_pairs) {
            if(!slhv_util::setEqual(result[p.first], result[p.second])) {
                std::set<app*> firstSet = result[p.first];
                std::set<app*> secondSet = result[p.second];
                std::set<app*> mergedSet = slhv_util::setUnion(firstSet, secondSet);
                result[p.first] = mergedSet;
                result[p.second] = mergedSet;
            }
        }

        return result;
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
}