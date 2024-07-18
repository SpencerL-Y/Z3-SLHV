(set-logic SLHV)
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
; Asserts from ESMBC starts
; 
(set-info :status unknown)
(declare-datatype 
    pt_record_0
    ((Pt_R_0 (loc IntLoc)))
)
(declare-datatypes ((pt_record_1 0)) (((Pt_R_1 (data Int)))))

(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)



 (declare-fun |symex_dynamic::dynamic_heap_2&0#1| () IntHeap)
(declare-fun |nondet$symex::nondet2| () Int)
(declare-fun |c:@F@main::$tmp::return_value$_malloc$1?1!0&0#0| () IntLoc)
(declare-fun |execution_statet::__guard_exec?0!0| () Bool)
(assert
 (let ((?x9 (pt |c:@F@main::$tmp::return_value$_malloc$1?1!0&0#0| (Pt_R_1 |nondet$symex::nondet2|))))
 (= ?x9 |symex_dynamic::dynamic_heap_2&0#1|)))
(assert
 (let (($x30 (= |symex_dynamic::dynamic_heap_2&0#1| emp)))
 (let (($x31 (not $x30)))
 (let (($x32 (=> true $x31)))
 (let (($x33 (=> (and |execution_statet::__guard_exec?0!0| true) $x31)))
 (let (($x34 (=> (and true |execution_statet::__guard_exec?0!0| true) $x31)))
 (not $x34)))))))
(check-sat)
; Asserts from ESMBC ends
(get-model)
(exit)
