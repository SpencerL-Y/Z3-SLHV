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
        // TODO: implement theory check here
        for(auto e : assignments) {

            /*-------------- learning enode -----------*/
            #ifdef SLHV_DEBUG
            std::cout << "current expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            SASSERT(is_app_of(e, basic_family_id, OP_EQ));
            app* equality = to_app(e);
            expr* lhsExpr = std::get<0>(equality->args2());
            expr* rhsExpr = std::get<1>(equality->args2());
            theory_var lhsVar = get_th_var(lhsExpr);
            theory_var rhsVar = get_th_var(rhsExpr);
            std::cout << "lhsVar: " << lhsVar << std::endl;
            std::cout << "rhsVar: " << rhsVar << std::endl;
            enode* lhsNode = get_enode(lhsVar);
            enode* rhsNode = get_enode(rhsVar);
            #ifdef SLHV_DEBUG
            std::cout << "lhsVar: " << lhsVar << std::endl;
            std::cout << "lhsEnode: " << std::endl;
            std::cout << mk_ismt2_pp(lhsNode->get_expr(), m) << " " << mk_ismt2_pp(lhsNode->get_root()->get_expr(), m) << std::endl;
            enode* curr = lhsNode->get_root();
            enode* head = curr;
            std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
            curr = curr->get_next();
            while(curr != head) {
                std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
                curr = curr->get_next();
            }
            std::cout << "rhsVar: " << rhsVar << std::endl;
            std::cout << "rhsEnode: " << std::endl;
            std::cout << mk_ismt2_pp(rhsNode->get_expr(), m) << " " << mk_ismt2_pp(rhsNode->get_root()->get_expr(), m) << std::endl;
            curr = rhsNode->get_root();
            head = curr;
            std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
            curr = curr->get_next();
            while(curr != head) {
                std::cout << mk_ismt2_pp(curr->get_expr(), m) << " ";
                curr = curr->get_next();
            }
            #endif

            SASSERT(is_app_of(lhsExpr, ctx.get_manager().mk_family_id("slhv"), OP_HVAR_CONST));
            if(!is_app_of(rhsExpr, ctx.get_manager().mk_family_id("slhv"), OP_HEAP_DISJUNION)) {
                ctx.set_conflict(
                    ctx.mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx, 0, nullptr, 0, nullptr, 0, nullptr
                    ))
                );
                return false;
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


    void theory_slhv::collect_and_analyze_assignments() {
        expr_ref_vector assigned_literals(m);
        ctx.get_assignments(assigned_literals);
        for(auto e : assigned_literals) {
            #ifdef SLHV_DEBUG
            std::cout << "collect expr: " << mk_ismt2_pp(e, m) << std::endl;
            #endif
            app* literal = to_app(e);
            // three possible literals:
            // 1. equality 2. inequality 3. list segment
            if(is_app_of(literal, basic_family_id, OP_EQ) && is_app_of(literal, basic_family_id, OP_DISTINCT)) {
                expr* lhsExpr = literal->get_arg(0);
                expr* rhsExpr = literal->get_arg(1);
                if(lhsExpr->get_kind() == INTLOC_SORT) {

                } else if(lhsExpr->get_kind() == INTHEAP_SORT) {

                } else {
                    std::cout << "cannot handle current sort" << std::endl;
                    SASSERT(false);
                }

            } else if(is_app_of(literal, basic_family_id, OP_NOT)) {
                expr* negated = literal->get_arg(0);
                SASSERT(is_app_of(negated, basic_family_id, OP_EQ));

            }
        }
    }

    std::pair<std::set<app* >, std::set<app *>> 
    theory_slhv::collect_vars_in_term(app* term) {
        // collect all locvars and hvars appeared recursively.
        std::set<app*> collected_locvars;
        std::set<app*> collected_hvars;
        
        if(term->is_app_of(get_id(), OP_HVAR_CONST)) {
            collected_hvars.insert(term);
            return {collected_locvars, collected_hvars};
        } else if(term->is_app_of(get_id(), OP_LOCVAR_CONST)) {
            collected_locvars.insert(term);
            return {collected_locvars, collected_hvars};
        } else {
            for(int i = 0; i < term->get_num_args(); i ++) {
                auto temp_result_pair = this->collect_vars_in_term(to_app(term->get_arg(i)));
                collected_locvars = slhv_util::setUnion(collected_locvars, temp_result_pair.first);
                collected_hvars = slhv_util::setUnion(collected_hvars, temp_result_pair.second);
            }
            return {collected_locvars, collected_hvars};
        }
    }

    
    std::set<app*> theory_slhv::collect_disj_unions(app* term) {
        // collect all app that is disjoint union of heap terms recursively.
        std::set<app*> collected_disj_unions;
        if(term->is_app_of(get_id(), OP_HEAP_DISJUNION)) {
            collected_disj_unions.insert(term);
        } else {
            for(int i = 0; i < term->get_num_args(); i ++) {
                collected_disj_unions = slhv_util::setUnion(collected_disj_unions, this->collect_disj_unions(to_app(term->get_arg(i))));
            }
        }
        return collected_disj_unions;
    }

    void theory_slhv::reset_configs() {
        this->curr_disj_unions.clear();
        this->curr_hvars.clear();
        this->curr_locvars.clear();
    }


    void theory_slhv::init_model(model_generator & mg)  {
        #ifdef SLHV_DEBUG
        std::cout << "slhv init model" << std::endl;
        #endif
    }

    model_value_proc* theory_slhv::mk_value(enode* n, model_generator & mg) {

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