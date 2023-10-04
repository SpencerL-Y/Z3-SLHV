(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-hvar h IntHeap)
(declare-hvar hp IntHeap)
(declare-locvar nil IntLoc)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)
(declare-const d1 Int)
(declare-const d2 Int)

(declare-datatype
    pt_record_0
    ((Pt_R_0 (next IntLoc) (data Int)))
)


(assert (not (= h (pt x (Pt_R_0 x d2)))))
(assert (=  h (pt x (Pt_R_0 y d1))))
(assert (= x y))
(check-sat)
