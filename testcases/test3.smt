(set-logic SLHV)

(declare-hvar h1 IntHeap)
(declare-hvar h2 IntHeap)
(declare-locvar l1 IntLoc)
(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)
(assert (or (= h1 (uplus h2 (pt l1 l1))) (= h2 (uplus h1 (pt l1 l1)))))
(check-sat)