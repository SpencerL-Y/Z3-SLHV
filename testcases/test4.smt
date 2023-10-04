(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-hvar h IntHeap)
(declare-hvar hp IntHeap)
(declare-locvar nil IntLoc)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)
(declare-const i Int)
(declare-const j Int)

(declare-datatype 
    pt_record_0
    ((Pt_R_0 (l IntLoc)))
)


(assert (and (= hp (uplus h (pt x (Pt_R_0 x) ) (pt x (Pt_R_0 y)))) (> i j) (> j 0)))
(check-sat)
