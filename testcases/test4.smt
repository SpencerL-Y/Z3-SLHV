(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-hvar h IntHeap)
(declare-hvar hp IntHeap)
(declare-locvar nil IntLoc)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)
(declare-const i Int)
(declare-const j Int)


(assert (and (= hp (uplus h (pt x x) (pt x y))) (> i j) (> j 0)))
(check-sat)
