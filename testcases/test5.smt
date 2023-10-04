(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-hvar h IntHeap)
(declare-locvar nil IntLoc)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)


(declare-datatype
    pt_record_0
    ((Pt_R_0 (l IntLoc)))

)

(assert (or (= h (uplus (pt x (Pt_R_0 x) ) (pt x (Pt_R_0 y)))) (= h (uplus (pt y (Pt_R_0 y)) (pt x (Pt_R_0 x))))))
(check-sat)
