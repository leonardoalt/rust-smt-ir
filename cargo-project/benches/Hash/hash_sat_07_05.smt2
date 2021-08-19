(set-info :smt-lib-version 2.6)
(set-logic QF_UFLIA)
(set-info :source | MathSat group |)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun hash_1 (Int) Int)
(declare-fun hash_2 (Int) Int)
(declare-fun hash_3 (Int) Int)
(declare-fun hash_4 (Int) Int)
(declare-fun hash_5 (Int) Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(assert (let ((?v_0 (hash_1 x1)) (?v_1 (hash_1 x2)) (?v_2 (hash_1 x3)) (?v_3 (hash_1 x4)) (?v_4 (hash_1 x5)) (?v_5 (hash_1 x6)) (?v_6 (hash_1 x7)) (?v_7 (hash_2 x1)) (?v_8 (hash_2 x2)) (?v_9 (hash_2 x3)) (?v_10 (hash_2 x4)) (?v_11 (hash_2 x5)) (?v_12 (hash_2 x6)) (?v_13 (hash_2 x7)) (?v_14 (hash_3 x1)) (?v_15 (hash_3 x2)) (?v_16 (hash_3 x3)) (?v_17 (hash_3 x4)) (?v_18 (hash_3 x5)) (?v_19 (hash_3 x6)) (?v_20 (hash_3 x7)) (?v_21 (hash_4 x1)) (?v_22 (hash_4 x2)) (?v_23 (hash_4 x3)) (?v_24 (hash_4 x4)) (?v_25 (hash_4 x5)) (?v_26 (hash_4 x6)) (?v_27 (hash_4 x7)) (?v_28 (hash_5 x1)) (?v_29 (hash_5 x2)) (?v_30 (hash_5 x3)) (?v_31 (hash_5 x4)) (?v_32 (hash_5 x5)) (?v_33 (hash_5 x6)) (?v_34 (hash_5 x7)) (?v_35 (+ x1 x7)) (?v_36 (+ x1 x2))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (distinct ?v_0 ?v_1) (distinct ?v_0 ?v_2)) (distinct ?v_0 ?v_3)) (distinct ?v_0 ?v_4)) (distinct ?v_0 ?v_5)) (distinct ?v_0 ?v_6)) (distinct ?v_1 ?v_2)) (distinct ?v_1 ?v_3)) (distinct ?v_1 ?v_4)) (distinct ?v_1 ?v_5)) (distinct ?v_1 ?v_6)) (distinct ?v_2 ?v_3)) (distinct ?v_2 ?v_4)) (distinct ?v_2 ?v_5)) (distinct ?v_2 ?v_6)) (distinct ?v_3 ?v_4)) (distinct ?v_3 ?v_5)) (distinct ?v_3 ?v_6)) (distinct ?v_4 ?v_5)) (distinct ?v_4 ?v_6)) (distinct ?v_5 ?v_6)) (distinct ?v_7 ?v_8)) (distinct ?v_7 ?v_9)) (distinct ?v_7 ?v_10)) (distinct ?v_7 ?v_11)) (distinct ?v_7 ?v_12)) (distinct ?v_7 ?v_13)) (distinct ?v_8 ?v_9)) (distinct ?v_8 ?v_10)) (distinct ?v_8 ?v_11)) (distinct ?v_8 ?v_12)) (distinct ?v_8 ?v_13)) (distinct ?v_9 ?v_10)) (distinct ?v_9 ?v_11)) (distinct ?v_9 ?v_12)) (distinct ?v_9 ?v_13)) (distinct ?v_10 ?v_11)) (distinct ?v_10 ?v_12)) (distinct ?v_10 ?v_13)) (distinct ?v_11 ?v_12)) (distinct ?v_11 ?v_13)) (distinct ?v_12 ?v_13)) (distinct ?v_14 ?v_15)) (distinct ?v_14 ?v_16)) (distinct ?v_14 ?v_17)) (distinct ?v_14 ?v_18)) (distinct ?v_14 ?v_19)) (distinct ?v_14 ?v_20)) (distinct ?v_15 ?v_16)) (distinct ?v_15 ?v_17)) (distinct ?v_15 ?v_18)) (distinct ?v_15 ?v_19)) (distinct ?v_15 ?v_20)) (distinct ?v_16 ?v_17)) (distinct ?v_16 ?v_18)) (distinct ?v_16 ?v_19)) (distinct ?v_16 ?v_20)) (distinct ?v_17 ?v_18)) (distinct ?v_17 ?v_19)) (distinct ?v_17 ?v_20)) (distinct ?v_18 ?v_19)) (distinct ?v_18 ?v_20)) (distinct ?v_19 ?v_20)) (distinct ?v_21 ?v_22)) (distinct ?v_21 ?v_23)) (distinct ?v_21 ?v_24)) (distinct ?v_21 ?v_25)) (distinct ?v_21 ?v_26)) (distinct ?v_21 ?v_27)) (distinct ?v_22 ?v_23)) (distinct ?v_22 ?v_24)) (distinct ?v_22 ?v_25)) (distinct ?v_22 ?v_26)) (distinct ?v_22 ?v_27)) (distinct ?v_23 ?v_24)) (distinct ?v_23 ?v_25)) (distinct ?v_23 ?v_26)) (distinct ?v_23 ?v_27)) (distinct ?v_24 ?v_25)) (distinct ?v_24 ?v_26)) (distinct ?v_24 ?v_27)) (distinct ?v_25 ?v_26)) (distinct ?v_25 ?v_27)) (distinct ?v_26 ?v_27)) (distinct ?v_28 ?v_29)) (distinct ?v_28 ?v_30)) (distinct ?v_28 ?v_31)) (distinct ?v_28 ?v_32)) (distinct ?v_28 ?v_33)) (distinct ?v_28 ?v_34)) (distinct ?v_29 ?v_30)) (distinct ?v_29 ?v_31)) (distinct ?v_29 ?v_32)) (distinct ?v_29 ?v_33)) (distinct ?v_29 ?v_34)) (distinct ?v_30 ?v_31)) (distinct ?v_30 ?v_32)) (distinct ?v_30 ?v_33)) (distinct ?v_30 ?v_34)) (distinct ?v_31 ?v_32)) (distinct ?v_31 ?v_33)) (distinct ?v_31 ?v_34)) (distinct ?v_32 ?v_33)) (distinct ?v_32 ?v_34)) (distinct ?v_33 ?v_34)) (or (or (or (or (or (or (= ?v_0 x1) (= ?v_0 x2)) (= ?v_0 x3)) (= ?v_0 x4)) (= ?v_0 x5)) (= ?v_0 x6)) (= ?v_0 x7))) (or (or (or (or (or (or (= ?v_1 x1) (= ?v_1 x2)) (= ?v_1 x3)) (= ?v_1 x4)) (= ?v_1 x5)) (= ?v_1 x6)) (= ?v_1 x7))) (or (or (or (or (or (or (= ?v_2 x1) (= ?v_2 x2)) (= ?v_2 x3)) (= ?v_2 x4)) (= ?v_2 x5)) (= ?v_2 x6)) (= ?v_2 x7))) (or (or (or (or (or (or (= ?v_3 x1) (= ?v_3 x2)) (= ?v_3 x3)) (= ?v_3 x4)) (= ?v_3 x5)) (= ?v_3 x6)) (= ?v_3 x7))) (or (or (or (or (or (or (= ?v_4 x1) (= ?v_4 x2)) (= ?v_4 x3)) (= ?v_4 x4)) (= ?v_4 x5)) (= ?v_4 x6)) (= ?v_4 x7))) (or (or (or (or (or (or (= ?v_5 x1) (= ?v_5 x2)) (= ?v_5 x3)) (= ?v_5 x4)) (= ?v_5 x5)) (= ?v_5 x6)) (= ?v_5 x7))) (or (or (or (or (or (or (= ?v_6 x1) (= ?v_6 x2)) (= ?v_6 x3)) (= ?v_6 x4)) (= ?v_6 x5)) (= ?v_6 x6)) (= ?v_6 x7))) (or (or (or (or (or (or (= ?v_7 x1) (= ?v_7 x2)) (= ?v_7 x3)) (= ?v_7 x4)) (= ?v_7 x5)) (= ?v_7 x6)) (= ?v_7 x7))) (or (or (or (or (or (or (= ?v_8 x1) (= ?v_8 x2)) (= ?v_8 x3)) (= ?v_8 x4)) (= ?v_8 x5)) (= ?v_8 x6)) (= ?v_8 x7))) (or (or (or (or (or (or (= ?v_9 x1) (= ?v_9 x2)) (= ?v_9 x3)) (= ?v_9 x4)) (= ?v_9 x5)) (= ?v_9 x6)) (= ?v_9 x7))) (or (or (or (or (or (or (= ?v_10 x1) (= ?v_10 x2)) (= ?v_10 x3)) (= ?v_10 x4)) (= ?v_10 x5)) (= ?v_10 x6)) (= ?v_10 x7))) (or (or (or (or (or (or (= ?v_11 x1) (= ?v_11 x2)) (= ?v_11 x3)) (= ?v_11 x4)) (= ?v_11 x5)) (= ?v_11 x6)) (= ?v_11 x7))) (or (or (or (or (or (or (= ?v_12 x1) (= ?v_12 x2)) (= ?v_12 x3)) (= ?v_12 x4)) (= ?v_12 x5)) (= ?v_12 x6)) (= ?v_12 x7))) (or (or (or (or (or (or (= ?v_13 x1) (= ?v_13 x2)) (= ?v_13 x3)) (= ?v_13 x4)) (= ?v_13 x5)) (= ?v_13 x6)) (= ?v_13 x7))) (or (or (or (or (or (or (= ?v_14 x1) (= ?v_14 x2)) (= ?v_14 x3)) (= ?v_14 x4)) (= ?v_14 x5)) (= ?v_14 x6)) (= ?v_14 x7))) (or (or (or (or (or (or (= ?v_15 x1) (= ?v_15 x2)) (= ?v_15 x3)) (= ?v_15 x4)) (= ?v_15 x5)) (= ?v_15 x6)) (= ?v_15 x7))) (or (or (or (or (or (or (= ?v_16 x1) (= ?v_16 x2)) (= ?v_16 x3)) (= ?v_16 x4)) (= ?v_16 x5)) (= ?v_16 x6)) (= ?v_16 x7))) (or (or (or (or (or (or (= ?v_17 x1) (= ?v_17 x2)) (= ?v_17 x3)) (= ?v_17 x4)) (= ?v_17 x5)) (= ?v_17 x6)) (= ?v_17 x7))) (or (or (or (or (or (or (= ?v_18 x1) (= ?v_18 x2)) (= ?v_18 x3)) (= ?v_18 x4)) (= ?v_18 x5)) (= ?v_18 x6)) (= ?v_18 x7))) (or (or (or (or (or (or (= ?v_19 x1) (= ?v_19 x2)) (= ?v_19 x3)) (= ?v_19 x4)) (= ?v_19 x5)) (= ?v_19 x6)) (= ?v_19 x7))) (or (or (or (or (or (or (= ?v_20 x1) (= ?v_20 x2)) (= ?v_20 x3)) (= ?v_20 x4)) (= ?v_20 x5)) (= ?v_20 x6)) (= ?v_20 x7))) (or (or (or (or (or (or (= ?v_21 x1) (= ?v_21 x2)) (= ?v_21 x3)) (= ?v_21 x4)) (= ?v_21 x5)) (= ?v_21 x6)) (= ?v_21 x7))) (or (or (or (or (or (or (= ?v_22 x1) (= ?v_22 x2)) (= ?v_22 x3)) (= ?v_22 x4)) (= ?v_22 x5)) (= ?v_22 x6)) (= ?v_22 x7))) (or (or (or (or (or (or (= ?v_23 x1) (= ?v_23 x2)) (= ?v_23 x3)) (= ?v_23 x4)) (= ?v_23 x5)) (= ?v_23 x6)) (= ?v_23 x7))) (or (or (or (or (or (or (= ?v_24 x1) (= ?v_24 x2)) (= ?v_24 x3)) (= ?v_24 x4)) (= ?v_24 x5)) (= ?v_24 x6)) (= ?v_24 x7))) (or (or (or (or (or (or (= ?v_25 x1) (= ?v_25 x2)) (= ?v_25 x3)) (= ?v_25 x4)) (= ?v_25 x5)) (= ?v_25 x6)) (= ?v_25 x7))) (or (or (or (or (or (or (= ?v_26 x1) (= ?v_26 x2)) (= ?v_26 x3)) (= ?v_26 x4)) (= ?v_26 x5)) (= ?v_26 x6)) (= ?v_26 x7))) (or (or (or (or (or (or (= ?v_27 x1) (= ?v_27 x2)) (= ?v_27 x3)) (= ?v_27 x4)) (= ?v_27 x5)) (= ?v_27 x6)) (= ?v_27 x7))) (or (or (or (or (or (or (= ?v_28 x1) (= ?v_28 x2)) (= ?v_28 x3)) (= ?v_28 x4)) (= ?v_28 x5)) (= ?v_28 x6)) (= ?v_28 x7))) (or (or (or (or (or (or (= ?v_29 x1) (= ?v_29 x2)) (= ?v_29 x3)) (= ?v_29 x4)) (= ?v_29 x5)) (= ?v_29 x6)) (= ?v_29 x7))) (or (or (or (or (or (or (= ?v_30 x1) (= ?v_30 x2)) (= ?v_30 x3)) (= ?v_30 x4)) (= ?v_30 x5)) (= ?v_30 x6)) (= ?v_30 x7))) (or (or (or (or (or (or (= ?v_31 x1) (= ?v_31 x2)) (= ?v_31 x3)) (= ?v_31 x4)) (= ?v_31 x5)) (= ?v_31 x6)) (= ?v_31 x7))) (or (or (or (or (or (or (= ?v_32 x1) (= ?v_32 x2)) (= ?v_32 x3)) (= ?v_32 x4)) (= ?v_32 x5)) (= ?v_32 x6)) (= ?v_32 x7))) (or (or (or (or (or (or (= ?v_33 x1) (= ?v_33 x2)) (= ?v_33 x3)) (= ?v_33 x4)) (= ?v_33 x5)) (= ?v_33 x6)) (= ?v_33 x7))) (or (or (or (or (or (or (= ?v_34 x1) (= ?v_34 x2)) (= ?v_34 x3)) (= ?v_34 x4)) (= ?v_34 x5)) (= ?v_34 x6)) (= ?v_34 x7))) (distinct x1 x2)) (distinct x1 x3)) (distinct x1 x4)) (distinct x1 x5)) (distinct x1 x6)) (distinct x1 x7)) (distinct x2 x3)) (distinct x2 x4)) (distinct x2 x5)) (distinct x2 x6)) (distinct x2 x7)) (distinct x3 x4)) (distinct x3 x5)) (distinct x3 x6)) (distinct x3 x7)) (distinct x4 x5)) (distinct x4 x6)) (distinct x4 x7)) (distinct x5 x6)) (distinct x5 x7)) (distinct x6 x7)) (<= 0 x1)) (< x1 8)) (<= 0 x2)) (< x2 8)) (<= 0 x3)) (< x3 8)) (<= 0 x4)) (< x4 8)) (<= 0 x5)) (< x5 8)) (<= 0 x6)) (< x6 8)) (<= 0 x7)) (< x7 8)) (= (hash_1 (hash_1 (hash_5 (ite (< ?v_35 8) ?v_35 x1)))) (hash_1 (hash_1 (hash_5 (ite (< ?v_36 8) ?v_36 x1))))))))
(check-sat)
(exit)
