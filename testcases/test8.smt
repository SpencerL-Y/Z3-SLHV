(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)

(declare-const loc0 Int)
(declare-const loc1 Int)


(assert (= loc0 1) )

(check-sat)

