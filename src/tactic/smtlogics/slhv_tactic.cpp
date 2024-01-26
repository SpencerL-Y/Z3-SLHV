
// SLHV tactic source

#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/core/nnf_tactic.h"


tactic *mk_slhv_tactic(ast_manager & m, params_ref const & p) {
    return using_params(
        // and_then(mk_simplify_tactic(m), 
        // and_then(
        // mk_solve_eqs_tactic(m), 
        // and_then(
        // mk_nnf_tactic(m),
        mk_smt_tactic(m)
        // )
        // )
        // )
        ,p
    );
}