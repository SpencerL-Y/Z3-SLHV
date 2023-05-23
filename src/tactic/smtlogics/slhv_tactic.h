// SLHV tactic

#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic *mk_slhv_tactic(ast_manager &m, params_ref const& p = params_ref());

