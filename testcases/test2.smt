(set-logic QF_LIA)

(declare-const i1 Int)
(declare-const i2 Int)
(assert (= ( + i1 2) i2))
(assert (= i1 1))
(assert (= i2 2))
(check-sat)
(get-model)