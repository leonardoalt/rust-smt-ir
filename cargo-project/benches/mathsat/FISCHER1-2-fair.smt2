(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
Older mathsat benchmarks.  Contact Mathsat group at http://mathsat.itc.it/ for
more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun AT2_PROC1_X () Int)
(declare-fun AT0_PROC1_X () Int)
(declare-fun AT1_PROC1_SW_B_C_TAU () Bool)
(declare-fun AT0_ID0 () Bool)
(declare-fun AT0_ID1 () Bool)
(declare-fun AT1_PROC1_WAIT () Bool)
(declare-fun AT2_Z () Int)
(declare-fun AT2_PROC1_C () Bool)
(declare-fun AT2_PROC1_B () Bool)
(declare-fun AT2_PROC1_A () Bool)
(declare-fun AT0_PROC1_C () Bool)
(declare-fun AT0_PROC1_B () Bool)
(declare-fun AT0_PROC1_A () Bool)
(declare-fun AT2_PROC1_CS () Bool)
(declare-fun AT1_ID0 () Bool)
(declare-fun AT1_ID1 () Bool)
(declare-fun AT0_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT1_PROC1_X () Int)
(declare-fun AT1_Z () Int)
(declare-fun AT2_ID0 () Bool)
(declare-fun AT2_ID1 () Bool)
(declare-fun AT0_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC1_CS () Bool)
(declare-fun AT0_PROC1_TAU () Bool)
(declare-fun AT0_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC1_WAIT () Bool)
(declare-fun AT1_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT1_PROC1_C () Bool)
(declare-fun AT1_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT1_PROC1_B () Bool)
(declare-fun AT1_PROC1_A () Bool)
(declare-fun AT0_DELTA () Bool)
(declare-fun AT1_PROC1_TAU () Bool)
(declare-fun AT1_PROC1_CS () Bool)
(declare-fun AT0_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT1_DELTA () Bool)
(declare-fun AT1_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT0_Z () Int)
(declare-fun AT1_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC1_SW_B_C_TAU () Bool)
(assert (let ((?v_0 (not AT0_PROC1_A)) (?v_1 (not AT0_PROC1_B)) (?v_2 (not AT0_PROC1_C)) (?v_3 (not AT0_PROC1_CS)) (?v_4 (not AT1_PROC1_A)) (?v_5 (not AT1_PROC1_B)) (?v_6 (not AT1_PROC1_C)) (?v_7 (not AT1_PROC1_CS)) (?v_8 (not AT2_PROC1_A)) (?v_9 (not AT2_PROC1_B)) (?v_10 (not AT2_PROC1_C)) (?v_11 (not AT2_PROC1_CS)) (?v_12 (= AT0_PROC1_X AT0_Z)) (?v_13 (> AT0_PROC1_X AT0_Z))) (let ((?v_49 (not ?v_12)) (?v_14 (= AT1_PROC1_X AT1_Z)) (?v_15 (> AT1_PROC1_X AT1_Z))) (let ((?v_48 (not ?v_14)) (?v_16 (= AT2_PROC1_X AT2_Z)) (?v_17 (> AT2_PROC1_X AT2_Z))) (let ((?v_54 (not ?v_16)) (?v_23 (- AT0_PROC1_X AT0_Z))) (let ((?v_20 (<= ?v_23 10)) (?v_30 (- AT1_PROC1_X AT1_Z))) (let ((?v_27 (<= ?v_30 10)) (?v_18 (not AT0_PROC1_SW_A_B_TAU)) (?v_19 (not AT0_PROC1_SW_B_C_TAU)) (?v_21 (not AT0_PROC1_SW_C_B_TAU)) (?v_22 (not AT0_PROC1_SW_C_CS_TAU)) (?v_35 (= AT1_PROC1_X AT0_PROC1_X)) (?v_24 (not AT0_PROC1_SW_CS_A_TAU)) (?v_25 (not AT1_PROC1_SW_A_B_TAU)) (?v_26 (not AT1_PROC1_SW_B_C_TAU)) (?v_28 (not AT1_PROC1_SW_C_B_TAU)) (?v_29 (not AT1_PROC1_SW_C_CS_TAU)) (?v_37 (= AT2_PROC1_X AT1_PROC1_X)) (?v_31 (not AT1_PROC1_SW_CS_A_TAU)) (?v_32 (= AT1_Z AT0_Z)) (?v_33 (= AT2_Z AT1_Z)) (?v_34 (not AT0_PROC1_WAIT)) (?v_39 (not AT0_PROC1_TAU)) (?v_36 (not AT1_PROC1_WAIT)) (?v_41 (not AT1_PROC1_TAU)) (?v_38 (not AT0_DELTA)) (?v_44 (< AT1_Z AT0_Z)) (?v_40 (not AT1_DELTA)) (?v_45 (< AT2_Z AT1_Z)) (?v_42 (< AT1_PROC1_X AT0_PROC1_X))) (let ((?v_46 (not ?v_35)) (?v_43 (< AT2_PROC1_X AT1_PROC1_X)) (?v_52 (not ?v_37)) (?v_47 (not ?v_32)) (?v_51 (not ?v_44)) (?v_53 (not ?v_33)) (?v_57 (not ?v_45))) (let ((?v_50 (or ?v_49 ?v_46)) (?v_56 (< AT1_Z AT1_PROC1_X)) (?v_55 (or ?v_48 ?v_52)) (?v_59 (not AT0_ID0)) (?v_58 (not AT0_ID1)) (?v_61 (not AT1_ID0)) (?v_60 (not AT1_ID1)) (?v_62 (not AT2_ID1)) (?v_63 (- AT2_PROC1_X AT2_Z))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_0 ?v_1) (or ?v_0 ?v_2)) (or ?v_0 ?v_3)) (or ?v_1 ?v_2)) (or ?v_1 ?v_3)) (or ?v_2 ?v_3)) (or ?v_4 ?v_5)) (or ?v_4 ?v_6)) (or ?v_4 ?v_7)) (or ?v_5 ?v_6)) (or ?v_5 ?v_7)) (or ?v_6 ?v_7)) (or ?v_8 ?v_9)) (or ?v_8 ?v_10)) (or ?v_8 ?v_11)) (or ?v_9 ?v_10)) (or ?v_9 ?v_11)) (or ?v_10 ?v_11)) (or ?v_12 ?v_13)) (or ?v_49 (not ?v_13))) (or ?v_14 ?v_15)) (or ?v_48 (not ?v_15))) (or ?v_16 ?v_17)) (or ?v_54 (not ?v_17))) (or ?v_1 ?v_20)) (or ?v_5 ?v_27)) (or ?v_9 (<= ?v_63 10))) (or (or (or (or (or (or AT0_PROC1_WAIT AT0_DELTA) AT0_PROC1_SW_A_B_TAU) AT0_PROC1_SW_B_C_TAU) AT0_PROC1_SW_C_B_TAU) AT0_PROC1_SW_C_CS_TAU) AT0_PROC1_SW_CS_A_TAU)) (or (or (or (or (or (or AT1_PROC1_WAIT AT1_DELTA) AT1_PROC1_SW_A_B_TAU) AT1_PROC1_SW_B_C_TAU) AT1_PROC1_SW_C_B_TAU) AT1_PROC1_SW_C_CS_TAU) AT1_PROC1_SW_CS_A_TAU)) (or ?v_18 AT0_PROC1_A)) (or ?v_18 AT0_PROC1_TAU)) (or ?v_18 AT1_PROC1_B)) (or ?v_18 ?v_14)) (or ?v_19 AT0_PROC1_B)) (or ?v_19 AT0_PROC1_TAU)) (or ?v_19 AT1_PROC1_C)) (or ?v_19 ?v_20)) (or ?v_19 ?v_14)) (or ?v_21 AT0_PROC1_C)) (or ?v_21 AT0_PROC1_TAU)) (or ?v_21 AT1_PROC1_B)) (or ?v_21 ?v_14)) (or ?v_22 AT0_PROC1_C)) (or ?v_22 AT0_PROC1_TAU)) (or ?v_22 AT1_PROC1_CS)) (or ?v_22 (> ?v_23 10))) (or ?v_22 ?v_35)) (or ?v_24 AT0_PROC1_CS)) (or ?v_24 AT0_PROC1_TAU)) (or ?v_24 AT1_PROC1_A)) (or ?v_24 ?v_14)) (or ?v_25 AT1_PROC1_A)) (or ?v_25 AT1_PROC1_TAU)) (or ?v_25 AT2_PROC1_B)) (or ?v_25 ?v_16)) (or ?v_26 AT1_PROC1_B)) (or ?v_26 AT1_PROC1_TAU)) (or ?v_26 AT2_PROC1_C)) (or ?v_26 ?v_27)) (or ?v_26 ?v_16)) (or ?v_28 AT1_PROC1_C)) (or ?v_28 AT1_PROC1_TAU)) (or ?v_28 AT2_PROC1_B)) (or ?v_28 ?v_16)) (or ?v_29 AT1_PROC1_C)) (or ?v_29 AT1_PROC1_TAU)) (or ?v_29 AT2_PROC1_CS)) (or ?v_29 (> ?v_30 10))) (or ?v_29 ?v_37)) (or ?v_31 AT1_PROC1_CS)) (or ?v_31 AT1_PROC1_TAU)) (or ?v_31 AT2_PROC1_A)) (or ?v_31 ?v_16)) (or ?v_18 ?v_32)) (or ?v_19 ?v_32)) (or ?v_21 ?v_32)) (or ?v_22 ?v_32)) (or ?v_24 ?v_32)) (or ?v_25 ?v_33)) (or ?v_26 ?v_33)) (or ?v_28 ?v_33)) (or ?v_29 ?v_33)) (or ?v_31 ?v_33)) (or (or ?v_34 ?v_0) AT1_PROC1_A)) (or (or ?v_34 AT0_PROC1_A) ?v_4)) (or (or ?v_34 ?v_1) AT1_PROC1_B)) (or (or ?v_34 AT0_PROC1_B) ?v_5)) (or (or ?v_34 ?v_2) AT1_PROC1_C)) (or (or ?v_34 AT0_PROC1_C) ?v_6)) (or (or ?v_34 ?v_3) AT1_PROC1_CS)) (or (or ?v_34 AT0_PROC1_CS) ?v_7)) (or ?v_34 ?v_39)) (or ?v_34 ?v_35)) (or ?v_34 ?v_32)) (or (or ?v_36 ?v_4) AT2_PROC1_A)) (or (or ?v_36 AT1_PROC1_A) ?v_8)) (or (or ?v_36 ?v_5) AT2_PROC1_B)) (or (or ?v_36 AT1_PROC1_B) ?v_9)) (or (or ?v_36 ?v_6) AT2_PROC1_C)) (or (or ?v_36 AT1_PROC1_C) ?v_10)) (or (or ?v_36 ?v_7) AT2_PROC1_CS)) (or (or ?v_36 AT1_PROC1_CS) ?v_11)) (or ?v_36 ?v_41)) (or ?v_36 ?v_37)) (or ?v_36 ?v_33)) (or (or ?v_38 ?v_0) AT1_PROC1_A)) (or (or ?v_38 AT0_PROC1_A) ?v_4)) (or (or ?v_38 ?v_1) AT1_PROC1_B)) (or (or ?v_38 AT0_PROC1_B) ?v_5)) (or (or ?v_38 ?v_2) AT1_PROC1_C)) (or (or ?v_38 AT0_PROC1_C) ?v_6)) (or (or ?v_38 ?v_3) AT1_PROC1_CS)) (or (or ?v_38 AT0_PROC1_CS) ?v_7)) (or ?v_38 ?v_35)) (or ?v_38 ?v_39)) (or ?v_38 ?v_44)) (or (or ?v_40 ?v_4) AT2_PROC1_A)) (or (or ?v_40 AT1_PROC1_A) ?v_8)) (or (or ?v_40 ?v_5) AT2_PROC1_B)) (or (or ?v_40 AT1_PROC1_B) ?v_9)) (or (or ?v_40 ?v_6) AT2_PROC1_C)) (or (or ?v_40 AT1_PROC1_C) ?v_10)) (or (or ?v_40 ?v_7) AT2_PROC1_CS)) (or (or ?v_40 AT1_PROC1_CS) ?v_11)) (or ?v_40 ?v_37)) (or ?v_40 ?v_41)) (or ?v_40 ?v_45)) (or ?v_35 ?v_42)) (or ?v_46 (not ?v_42))) (or ?v_37 ?v_43)) (or ?v_52 (not ?v_43))) (or ?v_38 ?v_40)) (or ?v_32 ?v_44)) (or ?v_47 ?v_51)) (or ?v_33 ?v_45)) (or ?v_53 ?v_57)) (or (or (or ?v_12 ?v_46) ?v_47) ?v_48)) (or (or (or ?v_49 ?v_35) ?v_47) ?v_48)) (or (or ?v_50 ?v_32) ?v_48)) (or (or ?v_50 ?v_47) ?v_14)) (or (or (or (not (< AT0_Z AT0_PROC1_X)) ?v_46) ?v_51) ?v_56)) (or (or (or ?v_14 ?v_52) ?v_53) ?v_54)) (or (or (or ?v_48 ?v_37) ?v_53) ?v_54)) (or (or ?v_55 ?v_33) ?v_54)) (or (or ?v_55 ?v_53) ?v_16)) (or (or (or (not ?v_56) ?v_52) ?v_57) (< AT2_Z AT2_PROC1_X))) AT0_PROC1_A) ?v_12) AT0_ID0) ?v_34) ?v_36) (or ?v_59 ?v_58)) (or ?v_61 ?v_60)) (or (not AT2_ID0) ?v_62)) (or ?v_18 AT0_ID0)) (or ?v_18 AT1_ID0)) (or ?v_19 AT1_ID1)) (or ?v_21 AT0_ID0)) (or ?v_21 AT1_ID0)) (or ?v_22 AT0_ID1)) (or ?v_22 AT1_ID1)) (or ?v_24 AT1_ID0)) (or (or ?v_38 ?v_58) AT1_ID1)) (or (or ?v_38 ?v_59) AT1_ID0)) (or ?v_25 AT1_ID0)) (or ?v_25 AT2_ID0)) (or ?v_26 AT2_ID1)) (or ?v_28 AT1_ID0)) (or ?v_28 AT2_ID0)) (or ?v_29 AT1_ID1)) (or ?v_29 AT2_ID1)) (or ?v_31 AT2_ID0)) (or (or ?v_40 ?v_60) AT2_ID1)) (or (or ?v_40 ?v_61) AT2_ID0)) (or ?v_4 AT2_PROC1_A)) (or AT1_PROC1_A ?v_8)) (or ?v_5 AT2_PROC1_B)) (or AT1_PROC1_B ?v_9)) (or ?v_6 AT2_PROC1_C)) (or AT1_PROC1_C ?v_10)) (or ?v_7 AT2_PROC1_CS)) (or AT1_PROC1_CS ?v_11)) (or ?v_60 AT2_ID1)) (or AT1_ID1 ?v_62)) (= ?v_30 ?v_63)) (or AT1_PROC1_B AT2_PROC1_B)) ?v_7) ?v_11))))))))))
(check-sat)
(exit)
