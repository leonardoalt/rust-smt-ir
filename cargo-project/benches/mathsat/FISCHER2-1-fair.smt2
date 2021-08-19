(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
Older mathsat benchmarks.  Contact Mathsat group at http://mathsat.itc.it/ for
more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun AT0_PROC1_X () Int)
(declare-fun AT0_ID0 () Bool)
(declare-fun AT1_PROC2_C () Bool)
(declare-fun AT0_ID1 () Bool)
(declare-fun AT1_PROC2_B () Bool)
(declare-fun AT0_ID2 () Bool)
(declare-fun AT1_PROC2_A () Bool)
(declare-fun AT1_PROC2_CS () Bool)
(declare-fun AT0_PROC2_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC1_C () Bool)
(declare-fun AT0_PROC1_B () Bool)
(declare-fun AT0_PROC1_A () Bool)
(declare-fun AT0_PROC2_CS () Bool)
(declare-fun AT1_ID0 () Bool)
(declare-fun AT1_ID1 () Bool)
(declare-fun AT1_ID2 () Bool)
(declare-fun AT0_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC2_X () Int)
(declare-fun AT1_PROC1_X () Int)
(declare-fun AT1_Z () Int)
(declare-fun AT0_PROC2_C () Bool)
(declare-fun AT0_PROC2_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC2_B () Bool)
(declare-fun AT0_PROC2_A () Bool)
(declare-fun AT0_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC1_CS () Bool)
(declare-fun AT0_PROC1_TAU () Bool)
(declare-fun AT0_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC1_WAIT () Bool)
(declare-fun AT1_PROC1_C () Bool)
(declare-fun AT1_PROC1_B () Bool)
(declare-fun AT1_PROC1_A () Bool)
(declare-fun AT0_DELTA () Bool)
(declare-fun AT0_PROC2_SW_B_C_TAU () Bool)
(declare-fun AT1_PROC1_CS () Bool)
(declare-fun AT0_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT0_PROC2_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC2_TAU () Bool)
(declare-fun AT1_PROC2_X () Int)
(declare-fun AT0_Z () Int)
(declare-fun AT0_PROC2_SW_A_B_TAU () Bool)
(declare-fun AT0_PROC2_WAIT () Bool)
(declare-fun AT0_PROC1_SW_B_C_TAU () Bool)
(assert (let ((?v_0 (not AT0_PROC1_A)) (?v_1 (not AT0_PROC1_B)) (?v_2 (not AT0_PROC1_C)) (?v_3 (not AT0_PROC1_CS)) (?v_4 (not AT1_PROC1_A)) (?v_5 (not AT1_PROC1_B)) (?v_6 (not AT1_PROC1_C)) (?v_7 (not AT1_PROC1_CS)) (?v_8 (not AT0_PROC2_A)) (?v_9 (not AT0_PROC2_B)) (?v_10 (not AT0_PROC2_C)) (?v_11 (not AT0_PROC2_CS)) (?v_12 (not AT1_PROC2_A)) (?v_13 (not AT1_PROC2_B)) (?v_14 (not AT1_PROC2_C)) (?v_15 (not AT1_PROC2_CS)) (?v_16 (= AT0_PROC1_X AT0_Z)) (?v_17 (> AT0_PROC1_X AT0_Z))) (let ((?v_53 (not ?v_16)) (?v_18 (= AT1_PROC1_X AT1_Z)) (?v_19 (> AT1_PROC1_X AT1_Z))) (let ((?v_52 (not ?v_18)) (?v_20 (= AT0_PROC2_X AT0_Z)) (?v_21 (> AT0_PROC2_X AT0_Z))) (let ((?v_58 (not ?v_20)) (?v_22 (= AT1_PROC2_X AT1_Z)) (?v_23 (> AT1_PROC2_X AT1_Z))) (let ((?v_57 (not ?v_22)) (?v_29 (- AT0_PROC1_X AT0_Z))) (let ((?v_26 (<= ?v_29 10)) (?v_37 (- AT0_PROC2_X AT0_Z))) (let ((?v_34 (<= ?v_37 10)) (?v_24 (not AT0_PROC1_SW_A_B_TAU)) (?v_25 (not AT0_PROC1_SW_B_C_TAU)) (?v_27 (not AT0_PROC1_SW_C_B_TAU)) (?v_28 (not AT0_PROC1_SW_C_CS_TAU)) (?v_40 (= AT1_PROC1_X AT0_PROC1_X)) (?v_30 (not AT0_PROC1_SW_CS_A_TAU)) (?v_31 (= AT1_Z AT0_Z)) (?v_32 (not AT0_PROC2_SW_A_B_TAU)) (?v_33 (not AT0_PROC2_SW_B_C_TAU)) (?v_35 (not AT0_PROC2_SW_C_B_TAU)) (?v_36 (not AT0_PROC2_SW_C_CS_TAU)) (?v_42 (= AT1_PROC2_X AT0_PROC2_X)) (?v_38 (not AT0_PROC2_SW_CS_A_TAU)) (?v_39 (not AT0_PROC1_WAIT)) (?v_44 (not AT0_PROC1_TAU)) (?v_41 (not AT0_PROC2_WAIT)) (?v_45 (not AT0_PROC2_TAU)) (?v_43 (not AT0_DELTA)) (?v_49 (< AT1_Z AT0_Z))) (let ((?v_46 (or ?v_43 ?v_49)) (?v_47 (< AT1_PROC1_X AT0_PROC1_X)) (?v_50 (not ?v_40)) (?v_48 (< AT1_PROC2_X AT0_PROC2_X)) (?v_56 (not ?v_42)) (?v_51 (not ?v_31)) (?v_55 (not ?v_49))) (let ((?v_54 (or ?v_53 ?v_50)) (?v_59 (or ?v_58 ?v_56)) (?v_60 (not AT0_ID0)) (?v_61 (not AT0_ID1)) (?v_62 (not AT0_ID2)) (?v_63 (not AT1_ID0)) (?v_64 (not AT1_ID1)) (?v_65 (not AT1_ID2)) (?v_66 (- AT1_PROC1_X AT1_Z)) (?v_67 (- AT1_PROC2_X AT1_Z))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_0 ?v_1) (or ?v_0 ?v_2)) (or ?v_0 ?v_3)) (or ?v_1 ?v_2)) (or ?v_1 ?v_3)) (or ?v_2 ?v_3)) (or ?v_4 ?v_5)) (or ?v_4 ?v_6)) (or ?v_4 ?v_7)) (or ?v_5 ?v_6)) (or ?v_5 ?v_7)) (or ?v_6 ?v_7)) (or ?v_8 ?v_9)) (or ?v_8 ?v_10)) (or ?v_8 ?v_11)) (or ?v_9 ?v_10)) (or ?v_9 ?v_11)) (or ?v_10 ?v_11)) (or ?v_12 ?v_13)) (or ?v_12 ?v_14)) (or ?v_12 ?v_15)) (or ?v_13 ?v_14)) (or ?v_13 ?v_15)) (or ?v_14 ?v_15)) (or ?v_16 ?v_17)) (or ?v_53 (not ?v_17))) (or ?v_18 ?v_19)) (or ?v_52 (not ?v_19))) (or ?v_20 ?v_21)) (or ?v_58 (not ?v_21))) (or ?v_22 ?v_23)) (or ?v_57 (not ?v_23))) (or ?v_1 ?v_26)) (or ?v_5 (<= ?v_66 10))) (or ?v_9 ?v_34)) (or ?v_13 (<= ?v_67 10))) (or (or (or (or (or (or AT0_PROC1_WAIT AT0_DELTA) AT0_PROC1_SW_A_B_TAU) AT0_PROC1_SW_B_C_TAU) AT0_PROC1_SW_C_B_TAU) AT0_PROC1_SW_C_CS_TAU) AT0_PROC1_SW_CS_A_TAU)) (or (or (or (or (or (or AT0_PROC2_WAIT AT0_DELTA) AT0_PROC2_SW_A_B_TAU) AT0_PROC2_SW_B_C_TAU) AT0_PROC2_SW_C_B_TAU) AT0_PROC2_SW_C_CS_TAU) AT0_PROC2_SW_CS_A_TAU)) (or ?v_24 AT0_PROC1_A)) (or ?v_24 AT0_PROC1_TAU)) (or ?v_24 AT1_PROC1_B)) (or ?v_24 ?v_18)) (or ?v_25 AT0_PROC1_B)) (or ?v_25 AT0_PROC1_TAU)) (or ?v_25 AT1_PROC1_C)) (or ?v_25 ?v_26)) (or ?v_25 ?v_18)) (or ?v_27 AT0_PROC1_C)) (or ?v_27 AT0_PROC1_TAU)) (or ?v_27 AT1_PROC1_B)) (or ?v_27 ?v_18)) (or ?v_28 AT0_PROC1_C)) (or ?v_28 AT0_PROC1_TAU)) (or ?v_28 AT1_PROC1_CS)) (or ?v_28 (> ?v_29 10))) (or ?v_28 ?v_40)) (or ?v_30 AT0_PROC1_CS)) (or ?v_30 AT0_PROC1_TAU)) (or ?v_30 AT1_PROC1_A)) (or ?v_30 ?v_18)) (or ?v_24 ?v_31)) (or ?v_25 ?v_31)) (or ?v_27 ?v_31)) (or ?v_28 ?v_31)) (or ?v_30 ?v_31)) (or ?v_32 AT0_PROC2_A)) (or ?v_32 AT0_PROC2_TAU)) (or ?v_32 AT1_PROC2_B)) (or ?v_32 ?v_22)) (or ?v_33 AT0_PROC2_B)) (or ?v_33 AT0_PROC2_TAU)) (or ?v_33 AT1_PROC2_C)) (or ?v_33 ?v_34)) (or ?v_33 ?v_22)) (or ?v_35 AT0_PROC2_C)) (or ?v_35 AT0_PROC2_TAU)) (or ?v_35 AT1_PROC2_B)) (or ?v_35 ?v_22)) (or ?v_36 AT0_PROC2_C)) (or ?v_36 AT0_PROC2_TAU)) (or ?v_36 AT1_PROC2_CS)) (or ?v_36 (> ?v_37 10))) (or ?v_36 ?v_42)) (or ?v_38 AT0_PROC2_CS)) (or ?v_38 AT0_PROC2_TAU)) (or ?v_38 AT1_PROC2_A)) (or ?v_38 ?v_22)) (or ?v_32 ?v_31)) (or ?v_33 ?v_31)) (or ?v_35 ?v_31)) (or ?v_36 ?v_31)) (or ?v_38 ?v_31)) (or (or ?v_39 ?v_0) AT1_PROC1_A)) (or (or ?v_39 AT0_PROC1_A) ?v_4)) (or (or ?v_39 ?v_1) AT1_PROC1_B)) (or (or ?v_39 AT0_PROC1_B) ?v_5)) (or (or ?v_39 ?v_2) AT1_PROC1_C)) (or (or ?v_39 AT0_PROC1_C) ?v_6)) (or (or ?v_39 ?v_3) AT1_PROC1_CS)) (or (or ?v_39 AT0_PROC1_CS) ?v_7)) (or ?v_39 ?v_44)) (or ?v_39 ?v_40)) (or ?v_39 ?v_31)) (or (or ?v_41 ?v_8) AT1_PROC2_A)) (or (or ?v_41 AT0_PROC2_A) ?v_12)) (or (or ?v_41 ?v_9) AT1_PROC2_B)) (or (or ?v_41 AT0_PROC2_B) ?v_13)) (or (or ?v_41 ?v_10) AT1_PROC2_C)) (or (or ?v_41 AT0_PROC2_C) ?v_14)) (or (or ?v_41 ?v_11) AT1_PROC2_CS)) (or (or ?v_41 AT0_PROC2_CS) ?v_15)) (or ?v_41 ?v_45)) (or ?v_41 ?v_42)) (or ?v_41 ?v_31)) (or (or ?v_43 ?v_0) AT1_PROC1_A)) (or (or ?v_43 AT0_PROC1_A) ?v_4)) (or (or ?v_43 ?v_1) AT1_PROC1_B)) (or (or ?v_43 AT0_PROC1_B) ?v_5)) (or (or ?v_43 ?v_2) AT1_PROC1_C)) (or (or ?v_43 AT0_PROC1_C) ?v_6)) (or (or ?v_43 ?v_3) AT1_PROC1_CS)) (or (or ?v_43 AT0_PROC1_CS) ?v_7)) (or ?v_43 ?v_40)) (or ?v_43 ?v_44)) ?v_46) (or (or ?v_43 ?v_8) AT1_PROC2_A)) (or (or ?v_43 AT0_PROC2_A) ?v_12)) (or (or ?v_43 ?v_9) AT1_PROC2_B)) (or (or ?v_43 AT0_PROC2_B) ?v_13)) (or (or ?v_43 ?v_10) AT1_PROC2_C)) (or (or ?v_43 AT0_PROC2_C) ?v_14)) (or (or ?v_43 ?v_11) AT1_PROC2_CS)) (or (or ?v_43 AT0_PROC2_CS) ?v_15)) (or ?v_43 ?v_42)) (or ?v_43 ?v_45)) ?v_46) (or ?v_40 ?v_47)) (or ?v_50 (not ?v_47))) (or ?v_42 ?v_48)) (or ?v_56 (not ?v_48))) (or ?v_31 ?v_49)) (or ?v_51 ?v_55)) (or (or (or ?v_16 ?v_50) ?v_51) ?v_52)) (or (or (or ?v_53 ?v_40) ?v_51) ?v_52)) (or (or ?v_54 ?v_31) ?v_52)) (or (or ?v_54 ?v_51) ?v_18)) (or (or (or (not (< AT0_Z AT0_PROC1_X)) ?v_50) ?v_55) (< AT1_Z AT1_PROC1_X))) (or (or (or ?v_20 ?v_56) ?v_51) ?v_57)) (or (or (or ?v_58 ?v_42) ?v_51) ?v_57)) (or (or ?v_59 ?v_31) ?v_57)) (or (or ?v_59 ?v_51) ?v_22)) (or (or (or (not (< AT0_Z AT0_PROC2_X)) ?v_56) ?v_55) (< AT1_Z AT1_PROC2_X))) AT0_PROC1_A) AT0_PROC2_A) ?v_16) ?v_20) AT0_ID0) (or ?v_39 ?v_41)) (or ?v_60 ?v_61)) (or ?v_60 ?v_62)) (or ?v_61 ?v_62)) (or ?v_63 ?v_64)) (or ?v_63 ?v_65)) (or ?v_64 ?v_65)) (or ?v_24 AT0_ID0)) (or ?v_24 AT1_ID0)) (or ?v_25 AT1_ID1)) (or ?v_27 AT0_ID0)) (or ?v_27 AT1_ID0)) (or ?v_28 AT0_ID1)) (or ?v_28 AT1_ID1)) (or ?v_30 AT1_ID0)) (or (or ?v_43 ?v_61) AT1_ID1)) (or ?v_32 AT0_ID0)) (or ?v_32 AT1_ID0)) (or ?v_33 AT1_ID2)) (or ?v_35 AT0_ID0)) (or ?v_35 AT1_ID0)) (or ?v_36 AT0_ID2)) (or ?v_36 AT1_ID2)) (or ?v_38 AT1_ID0)) (or (or ?v_43 ?v_62) AT1_ID2)) (or (or ?v_43 ?v_60) AT1_ID0)) (or ?v_4 AT1_PROC1_A)) (or AT1_PROC1_A ?v_4)) (or ?v_5 AT1_PROC1_B)) (or AT1_PROC1_B ?v_5)) (or ?v_6 AT1_PROC1_C)) (or AT1_PROC1_C ?v_6)) (or ?v_7 AT1_PROC1_CS)) (or AT1_PROC1_CS ?v_7)) (or ?v_64 AT1_ID1)) (or AT1_ID1 ?v_64)) (= ?v_66 ?v_66)) (or ?v_12 AT1_PROC2_A)) (or AT1_PROC2_A ?v_12)) (or ?v_13 AT1_PROC2_B)) (or AT1_PROC2_B ?v_13)) (or ?v_14 AT1_PROC2_C)) (or AT1_PROC2_C ?v_14)) (or ?v_15 AT1_PROC2_CS)) (or AT1_PROC2_CS ?v_15)) (or ?v_65 AT1_ID2)) (or AT1_ID2 ?v_65)) (= ?v_67 ?v_67)) AT1_PROC1_B) ?v_7)))))))))))
(check-sat)
(exit)
