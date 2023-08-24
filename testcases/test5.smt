(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-hvar h IntHeap)
(declare-locvar nil IntLoc)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)

(assert (or (= h (uplus (pt x x) (pt x y))) (= h (uplus (pt y y) (pt x x)))))
(check-sat)
