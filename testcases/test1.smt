(set-logic SLHV)
(declare-hvar h IntHeap)
(declare-hvar h1 IntHeap)
(declare-hvar h2 IntHeap)
(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)

(declare-datatype 
    pt_record_0
    ((Pt_R_0 (l Int)))
)

(assert (not (= h1 h2) ) )
(check-sat)



