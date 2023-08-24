(declare-const x1 Int)
(declare-const x2 Int)

(assert (or (= x1 (+ x2 4))  (= x2 (+ x1 4))))
(assert (distinct x1 (+ x2 4)))
(check-sat)