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
(declare-fun hash_6 (Int) Int)
(declare-fun hash_7 (Int) Int)
(declare-fun hash_8 (Int) Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(assert (let ((?v_0 (hash_1 x1)) (?v_1 (hash_1 x2)) (?v_2 (hash_1 x3)) (?v_3 (hash_1 x4)) (?v_4 (hash_1 x5)) (?v_5 (hash_1 x6)) (?v_6 (hash_2 x1)) (?v_7 (hash_2 x2)) (?v_8 (hash_2 x3)) (?v_9 (hash_2 x4)) (?v_10 (hash_2 x5)) (?v_11 (hash_2 x6)) (?v_12 (hash_3 x1)) (?v_13 (hash_3 x2)) (?v_14 (hash_3 x3)) (?v_15 (hash_3 x4)) (?v_16 (hash_3 x5)) (?v_17 (hash_3 x6)) (?v_18 (hash_4 x1)) (?v_19 (hash_4 x2)) (?v_20 (hash_4 x3)) (?v_21 (hash_4 x4)) (?v_22 (hash_4 x5)) (?v_23 (hash_4 x6)) (?v_24 (hash_5 x1)) (?v_25 (hash_5 x2)) (?v_26 (hash_5 x3)) (?v_27 (hash_5 x4)) (?v_28 (hash_5 x5)) (?v_29 (hash_5 x6)) (?v_30 (hash_6 x1)) (?v_31 (hash_6 x2)) (?v_32 (hash_6 x3)) (?v_33 (hash_6 x4)) (?v_34 (hash_6 x5)) (?v_35 (hash_6 x6)) (?v_36 (hash_7 x1)) (?v_37 (hash_7 x2)) (?v_38 (hash_7 x3)) (?v_39 (hash_7 x4)) (?v_40 (hash_7 x5)) (?v_41 (hash_7 x6)) (?v_42 (hash_8 x1)) (?v_43 (hash_8 x2)) (?v_44 (hash_8 x3)) (?v_45 (hash_8 x4)) (?v_46 (hash_8 x5)) (?v_47 (hash_8 x6)) (?v_48 (+ x1 x6)) (?v_49 (+ x1 x2))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (distinct ?v_0 ?v_1) (distinct ?v_0 ?v_2)) (distinct ?v_0 ?v_3)) (distinct ?v_0 ?v_4)) (distinct ?v_0 ?v_5)) (distinct ?v_1 ?v_2)) (distinct ?v_1 ?v_3)) (distinct ?v_1 ?v_4)) (distinct ?v_1 ?v_5)) (distinct ?v_2 ?v_3)) (distinct ?v_2 ?v_4)) (distinct ?v_2 ?v_5)) (distinct ?v_3 ?v_4)) (distinct ?v_3 ?v_5)) (distinct ?v_4 ?v_5)) (distinct ?v_6 ?v_7)) (distinct ?v_6 ?v_8)) (distinct ?v_6 ?v_9)) (distinct ?v_6 ?v_10)) (distinct ?v_6 ?v_11)) (distinct ?v_7 ?v_8)) (distinct ?v_7 ?v_9)) (distinct ?v_7 ?v_10)) (distinct ?v_7 ?v_11)) (distinct ?v_8 ?v_9)) (distinct ?v_8 ?v_10)) (distinct ?v_8 ?v_11)) (distinct ?v_9 ?v_10)) (distinct ?v_9 ?v_11)) (distinct ?v_10 ?v_11)) (distinct ?v_12 ?v_13)) (distinct ?v_12 ?v_14)) (distinct ?v_12 ?v_15)) (distinct ?v_12 ?v_16)) (distinct ?v_12 ?v_17)) (distinct ?v_13 ?v_14)) (distinct ?v_13 ?v_15)) (distinct ?v_13 ?v_16)) (distinct ?v_13 ?v_17)) (distinct ?v_14 ?v_15)) (distinct ?v_14 ?v_16)) (distinct ?v_14 ?v_17)) (distinct ?v_15 ?v_16)) (distinct ?v_15 ?v_17)) (distinct ?v_16 ?v_17)) (distinct ?v_18 ?v_19)) (distinct ?v_18 ?v_20)) (distinct ?v_18 ?v_21)) (distinct ?v_18 ?v_22)) (distinct ?v_18 ?v_23)) (distinct ?v_19 ?v_20)) (distinct ?v_19 ?v_21)) (distinct ?v_19 ?v_22)) (distinct ?v_19 ?v_23)) (distinct ?v_20 ?v_21)) (distinct ?v_20 ?v_22)) (distinct ?v_20 ?v_23)) (distinct ?v_21 ?v_22)) (distinct ?v_21 ?v_23)) (distinct ?v_22 ?v_23)) (distinct ?v_24 ?v_25)) (distinct ?v_24 ?v_26)) (distinct ?v_24 ?v_27)) (distinct ?v_24 ?v_28)) (distinct ?v_24 ?v_29)) (distinct ?v_25 ?v_26)) (distinct ?v_25 ?v_27)) (distinct ?v_25 ?v_28)) (distinct ?v_25 ?v_29)) (distinct ?v_26 ?v_27)) (distinct ?v_26 ?v_28)) (distinct ?v_26 ?v_29)) (distinct ?v_27 ?v_28)) (distinct ?v_27 ?v_29)) (distinct ?v_28 ?v_29)) (distinct ?v_30 ?v_31)) (distinct ?v_30 ?v_32)) (distinct ?v_30 ?v_33)) (distinct ?v_30 ?v_34)) (distinct ?v_30 ?v_35)) (distinct ?v_31 ?v_32)) (distinct ?v_31 ?v_33)) (distinct ?v_31 ?v_34)) (distinct ?v_31 ?v_35)) (distinct ?v_32 ?v_33)) (distinct ?v_32 ?v_34)) (distinct ?v_32 ?v_35)) (distinct ?v_33 ?v_34)) (distinct ?v_33 ?v_35)) (distinct ?v_34 ?v_35)) (distinct ?v_36 ?v_37)) (distinct ?v_36 ?v_38)) (distinct ?v_36 ?v_39)) (distinct ?v_36 ?v_40)) (distinct ?v_36 ?v_41)) (distinct ?v_37 ?v_38)) (distinct ?v_37 ?v_39)) (distinct ?v_37 ?v_40)) (distinct ?v_37 ?v_41)) (distinct ?v_38 ?v_39)) (distinct ?v_38 ?v_40)) (distinct ?v_38 ?v_41)) (distinct ?v_39 ?v_40)) (distinct ?v_39 ?v_41)) (distinct ?v_40 ?v_41)) (distinct ?v_42 ?v_43)) (distinct ?v_42 ?v_44)) (distinct ?v_42 ?v_45)) (distinct ?v_42 ?v_46)) (distinct ?v_42 ?v_47)) (distinct ?v_43 ?v_44)) (distinct ?v_43 ?v_45)) (distinct ?v_43 ?v_46)) (distinct ?v_43 ?v_47)) (distinct ?v_44 ?v_45)) (distinct ?v_44 ?v_46)) (distinct ?v_44 ?v_47)) (distinct ?v_45 ?v_46)) (distinct ?v_45 ?v_47)) (distinct ?v_46 ?v_47)) (or (or (or (or (or (= ?v_0 x1) (= ?v_0 x2)) (= ?v_0 x3)) (= ?v_0 x4)) (= ?v_0 x5)) (= ?v_0 x6))) (or (or (or (or (or (= ?v_1 x1) (= ?v_1 x2)) (= ?v_1 x3)) (= ?v_1 x4)) (= ?v_1 x5)) (= ?v_1 x6))) (or (or (or (or (or (= ?v_2 x1) (= ?v_2 x2)) (= ?v_2 x3)) (= ?v_2 x4)) (= ?v_2 x5)) (= ?v_2 x6))) (or (or (or (or (or (= ?v_3 x1) (= ?v_3 x2)) (= ?v_3 x3)) (= ?v_3 x4)) (= ?v_3 x5)) (= ?v_3 x6))) (or (or (or (or (or (= ?v_4 x1) (= ?v_4 x2)) (= ?v_4 x3)) (= ?v_4 x4)) (= ?v_4 x5)) (= ?v_4 x6))) (or (or (or (or (or (= ?v_5 x1) (= ?v_5 x2)) (= ?v_5 x3)) (= ?v_5 x4)) (= ?v_5 x5)) (= ?v_5 x6))) (or (or (or (or (or (= ?v_6 x1) (= ?v_6 x2)) (= ?v_6 x3)) (= ?v_6 x4)) (= ?v_6 x5)) (= ?v_6 x6))) (or (or (or (or (or (= ?v_7 x1) (= ?v_7 x2)) (= ?v_7 x3)) (= ?v_7 x4)) (= ?v_7 x5)) (= ?v_7 x6))) (or (or (or (or (or (= ?v_8 x1) (= ?v_8 x2)) (= ?v_8 x3)) (= ?v_8 x4)) (= ?v_8 x5)) (= ?v_8 x6))) (or (or (or (or (or (= ?v_9 x1) (= ?v_9 x2)) (= ?v_9 x3)) (= ?v_9 x4)) (= ?v_9 x5)) (= ?v_9 x6))) (or (or (or (or (or (= ?v_10 x1) (= ?v_10 x2)) (= ?v_10 x3)) (= ?v_10 x4)) (= ?v_10 x5)) (= ?v_10 x6))) (or (or (or (or (or (= ?v_11 x1) (= ?v_11 x2)) (= ?v_11 x3)) (= ?v_11 x4)) (= ?v_11 x5)) (= ?v_11 x6))) (or (or (or (or (or (= ?v_12 x1) (= ?v_12 x2)) (= ?v_12 x3)) (= ?v_12 x4)) (= ?v_12 x5)) (= ?v_12 x6))) (or (or (or (or (or (= ?v_13 x1) (= ?v_13 x2)) (= ?v_13 x3)) (= ?v_13 x4)) (= ?v_13 x5)) (= ?v_13 x6))) (or (or (or (or (or (= ?v_14 x1) (= ?v_14 x2)) (= ?v_14 x3)) (= ?v_14 x4)) (= ?v_14 x5)) (= ?v_14 x6))) (or (or (or (or (or (= ?v_15 x1) (= ?v_15 x2)) (= ?v_15 x3)) (= ?v_15 x4)) (= ?v_15 x5)) (= ?v_15 x6))) (or (or (or (or (or (= ?v_16 x1) (= ?v_16 x2)) (= ?v_16 x3)) (= ?v_16 x4)) (= ?v_16 x5)) (= ?v_16 x6))) (or (or (or (or (or (= ?v_17 x1) (= ?v_17 x2)) (= ?v_17 x3)) (= ?v_17 x4)) (= ?v_17 x5)) (= ?v_17 x6))) (or (or (or (or (or (= ?v_18 x1) (= ?v_18 x2)) (= ?v_18 x3)) (= ?v_18 x4)) (= ?v_18 x5)) (= ?v_18 x6))) (or (or (or (or (or (= ?v_19 x1) (= ?v_19 x2)) (= ?v_19 x3)) (= ?v_19 x4)) (= ?v_19 x5)) (= ?v_19 x6))) (or (or (or (or (or (= ?v_20 x1) (= ?v_20 x2)) (= ?v_20 x3)) (= ?v_20 x4)) (= ?v_20 x5)) (= ?v_20 x6))) (or (or (or (or (or (= ?v_21 x1) (= ?v_21 x2)) (= ?v_21 x3)) (= ?v_21 x4)) (= ?v_21 x5)) (= ?v_21 x6))) (or (or (or (or (or (= ?v_22 x1) (= ?v_22 x2)) (= ?v_22 x3)) (= ?v_22 x4)) (= ?v_22 x5)) (= ?v_22 x6))) (or (or (or (or (or (= ?v_23 x1) (= ?v_23 x2)) (= ?v_23 x3)) (= ?v_23 x4)) (= ?v_23 x5)) (= ?v_23 x6))) (or (or (or (or (or (= ?v_24 x1) (= ?v_24 x2)) (= ?v_24 x3)) (= ?v_24 x4)) (= ?v_24 x5)) (= ?v_24 x6))) (or (or (or (or (or (= ?v_25 x1) (= ?v_25 x2)) (= ?v_25 x3)) (= ?v_25 x4)) (= ?v_25 x5)) (= ?v_25 x6))) (or (or (or (or (or (= ?v_26 x1) (= ?v_26 x2)) (= ?v_26 x3)) (= ?v_26 x4)) (= ?v_26 x5)) (= ?v_26 x6))) (or (or (or (or (or (= ?v_27 x1) (= ?v_27 x2)) (= ?v_27 x3)) (= ?v_27 x4)) (= ?v_27 x5)) (= ?v_27 x6))) (or (or (or (or (or (= ?v_28 x1) (= ?v_28 x2)) (= ?v_28 x3)) (= ?v_28 x4)) (= ?v_28 x5)) (= ?v_28 x6))) (or (or (or (or (or (= ?v_29 x1) (= ?v_29 x2)) (= ?v_29 x3)) (= ?v_29 x4)) (= ?v_29 x5)) (= ?v_29 x6))) (or (or (or (or (or (= ?v_30 x1) (= ?v_30 x2)) (= ?v_30 x3)) (= ?v_30 x4)) (= ?v_30 x5)) (= ?v_30 x6))) (or (or (or (or (or (= ?v_31 x1) (= ?v_31 x2)) (= ?v_31 x3)) (= ?v_31 x4)) (= ?v_31 x5)) (= ?v_31 x6))) (or (or (or (or (or (= ?v_32 x1) (= ?v_32 x2)) (= ?v_32 x3)) (= ?v_32 x4)) (= ?v_32 x5)) (= ?v_32 x6))) (or (or (or (or (or (= ?v_33 x1) (= ?v_33 x2)) (= ?v_33 x3)) (= ?v_33 x4)) (= ?v_33 x5)) (= ?v_33 x6))) (or (or (or (or (or (= ?v_34 x1) (= ?v_34 x2)) (= ?v_34 x3)) (= ?v_34 x4)) (= ?v_34 x5)) (= ?v_34 x6))) (or (or (or (or (or (= ?v_35 x1) (= ?v_35 x2)) (= ?v_35 x3)) (= ?v_35 x4)) (= ?v_35 x5)) (= ?v_35 x6))) (or (or (or (or (or (= ?v_36 x1) (= ?v_36 x2)) (= ?v_36 x3)) (= ?v_36 x4)) (= ?v_36 x5)) (= ?v_36 x6))) (or (or (or (or (or (= ?v_37 x1) (= ?v_37 x2)) (= ?v_37 x3)) (= ?v_37 x4)) (= ?v_37 x5)) (= ?v_37 x6))) (or (or (or (or (or (= ?v_38 x1) (= ?v_38 x2)) (= ?v_38 x3)) (= ?v_38 x4)) (= ?v_38 x5)) (= ?v_38 x6))) (or (or (or (or (or (= ?v_39 x1) (= ?v_39 x2)) (= ?v_39 x3)) (= ?v_39 x4)) (= ?v_39 x5)) (= ?v_39 x6))) (or (or (or (or (or (= ?v_40 x1) (= ?v_40 x2)) (= ?v_40 x3)) (= ?v_40 x4)) (= ?v_40 x5)) (= ?v_40 x6))) (or (or (or (or (or (= ?v_41 x1) (= ?v_41 x2)) (= ?v_41 x3)) (= ?v_41 x4)) (= ?v_41 x5)) (= ?v_41 x6))) (or (or (or (or (or (= ?v_42 x1) (= ?v_42 x2)) (= ?v_42 x3)) (= ?v_42 x4)) (= ?v_42 x5)) (= ?v_42 x6))) (or (or (or (or (or (= ?v_43 x1) (= ?v_43 x2)) (= ?v_43 x3)) (= ?v_43 x4)) (= ?v_43 x5)) (= ?v_43 x6))) (or (or (or (or (or (= ?v_44 x1) (= ?v_44 x2)) (= ?v_44 x3)) (= ?v_44 x4)) (= ?v_44 x5)) (= ?v_44 x6))) (or (or (or (or (or (= ?v_45 x1) (= ?v_45 x2)) (= ?v_45 x3)) (= ?v_45 x4)) (= ?v_45 x5)) (= ?v_45 x6))) (or (or (or (or (or (= ?v_46 x1) (= ?v_46 x2)) (= ?v_46 x3)) (= ?v_46 x4)) (= ?v_46 x5)) (= ?v_46 x6))) (or (or (or (or (or (= ?v_47 x1) (= ?v_47 x2)) (= ?v_47 x3)) (= ?v_47 x4)) (= ?v_47 x5)) (= ?v_47 x6))) (distinct x1 x2)) (distinct x1 x3)) (distinct x1 x4)) (distinct x1 x5)) (distinct x1 x6)) (distinct x2 x3)) (distinct x2 x4)) (distinct x2 x5)) (distinct x2 x6)) (distinct x3 x4)) (distinct x3 x5)) (distinct x3 x6)) (distinct x4 x5)) (distinct x4 x6)) (distinct x5 x6)) (<= 0 x1)) (< x1 7)) (<= 0 x2)) (< x2 7)) (<= 0 x3)) (< x3 7)) (<= 0 x4)) (< x4 7)) (<= 0 x5)) (< x5 7)) (<= 0 x6)) (< x6 7)) (= (hash_1 (hash_1 (hash_8 (ite (< ?v_48 7) ?v_48 x1)))) (hash_1 (hash_1 (hash_8 (ite (< ?v_49 7) ?v_49 x1))))))))
(check-sat)
(exit)
