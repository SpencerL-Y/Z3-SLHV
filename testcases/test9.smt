(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-hvar h IntHeap)
(declare-hvar hp IntHeap)
(declare-locvar nil IntLoc)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)
(declare-const d Int)

(declare-datatype
    pt_record
    ((Pt_R (next IntLoc) (data Int)))
)


(assert (= h (pt x (Pt_R x d))))
(check-sat)
