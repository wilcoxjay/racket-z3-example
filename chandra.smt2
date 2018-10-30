(declare-const a Int)
(declare-const b Int)

(assert (= (+ (* a 1) b) 1))
(assert (= (+ (* a 2) b) 2))

(check-sat)
(get-model)
