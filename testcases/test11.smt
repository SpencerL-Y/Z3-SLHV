(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)


(declare-hvar H3_1 IntHeap)
(declare-hvar h4 IntHeap)
(declare-locvar $p9_main0 IntLoc)
(declare-locvar l6 IntLoc)
(declare-const d5_1 Int)

(declare-datatype
    pt_record_0
    ((Pt_R_0 (next IntLoc) (data Int) ))
)
(assert 
(let ((a!1 (= H3_1 (uplus h4 (pt $p9_main0 (Pt_R_0 l6 d5_1 ))))))
  (not a!1)))
(check-sat)