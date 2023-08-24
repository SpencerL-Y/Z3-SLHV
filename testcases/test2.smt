(set-logic SLHV)

(declare-hvar h IntHeap)
(declare-locvar x IntLoc)
(declare-locvar y IntLoc)
(assert (exists ((hp IntHeap)) (= hp (uplus (pt x x) (pt x y)))))
(assert (exists ((hp IntHeap)) (= hp (uplus h (pt x y)))))
(check-sat)