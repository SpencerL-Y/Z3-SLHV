#include "ast/ast_ll_pp.h"
#include "ast/slhv_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/theory_slhv.h"
namespace smt {
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

        if(is_uplus(term) || is_points_to(term)) {
            SASSERT(term->get_num_args() == 2);
            enode* arg0_node = ctx.get_enode(term->get_arg(0));
            enode* arg1_node = ctx.get_enode(term->get_arg(1));

            theory_var arg0_var = arg0_node->get_th_var(get_id());
            theory_var arg1_var = arg0_node->get_th_var(get_id());
            #ifdef SLHV_DEBUG
            std::cout << "term name: " << term->get_name() << " is_uplus: " << is_uplus(term) << " is_points_to: " << is_points_to(term) << " num args: " << term->get_num_args() << std::endl;
            #endif
        } else {
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
            mk_var(e);
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
}