(set-logic SLHV)

(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)
(declare-hvar h0 IntHeap)
(declare-hvar h1 IntHeap)
(declare-locvar head0 IntLoc)
(declare-locvar head1 IntLoc)
(declare-locvar curr0 IntLoc)
(declare-locvar curr1 IntLoc)
(declare-locvar temp0 IntLoc)
(declare-locvar temp1 IntLoc)


(declare-const loc0 Int)
(declare-const loc1 Int)

(declare-hvar h1_B2 IntHeap)
(declare-locvar x_B2 IntLoc)
(declare-locvar x_B4 IntLoc)

(declare-datatype
    pt_record_0
    ((Pt_R_0 (l IntLoc)))

)

(assert (= loc0 1) )
(assert (= loc1 2) )
(assert (distinct h1 emp))
(assert (or (distinct loc0 1) (and 
    (= h0 emp)
    (= h1 (pt head1 (Pt_R_0 nil) ))
    (= curr1 head1)
    (= temp1 temp0)
    (= loc1 2)
)))

(assert (or (distinct loc0 2) (and 
    (= (h0 (uplus (pt curr0 (Pt_R_0 x_B2)) h1_B2)))
    (= h1 (uplus (pt temp1 (Pt_R_0 nil)) (pt curr0 (Pt_R_0 temp1)) h1))
    (= curr1 temp1)
    (= head1 head0)
    (= loc1 2)
)))
(assert (or (distinct loc0 2) (and 
    (= curr1 head0)
    (= head1 head0)
    (= temp1 temp0)
    (= h1 h0)
    (= loc1 3)
)))
(assert (or (distinct loc0 3) (and 
    (distinct curr0 nil)
    (= h0 (uplus (pt curr0 (Pt_R_0 x_B4)) h1))
    (= temp1 x_B4)
    (= temp1 curr1)
    (= head0 head1)
    (= loc1 3)
)))
(assert (or (distinct loc0 3) (and 
    (= curr0 nil)
    (= head1 head0)
    (= curr1 curr0)
    (= temp1 temp0)
    (= loc1 4)
)))
(check-sat)
