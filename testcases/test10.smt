(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)


(declare-hvar h IntHeap)
(declare-hvar hp IntHeap)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)
(declare-const d Int)

(declare-datatype
    pt_record_0
    ((Pt_R_0 (next IntLoc) (data Int)))
)
(
    declare-datatype
    pt_record_1
    ((Pt_R_1 (next IntLoc) (nn IntLoc) (data Int)))
)


(assert (= h (pt x (Pt_R_0   x d))))
(assert (= h (pt x (Pt_R_1 x x d))))
(check-sat)