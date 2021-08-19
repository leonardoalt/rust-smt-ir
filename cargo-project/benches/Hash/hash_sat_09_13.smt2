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
(declare-fun hash_9 (Int) Int)
(declare-fun hash_10 (Int) Int)
(declare-fun hash_11 (Int) Int)
(declare-fun hash_12 (Int) Int)
(declare-fun hash_13 (Int) Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x9 () Int)
(assert (let ((?v_0 (hash_1 x1)) (?v_1 (hash_1 x2)) (?v_2 (hash_1 x3)) (?v_3 (hash_1 x4)) (?v_4 (hash_1 x5)) (?v_5 (hash_1 x6)) (?v_6 (hash_1 x7)) (?v_7 (hash_1 x8)) (?v_8 (hash_1 x9)) (?v_9 (hash_2 x1)) (?v_10 (hash_2 x2)) (?v_11 (hash_2 x3)) (?v_12 (hash_2 x4)) (?v_13 (hash_2 x5)) (?v_14 (hash_2 x6)) (?v_15 (hash_2 x7)) (?v_16 (hash_2 x8)) (?v_17 (hash_2 x9)) (?v_18 (hash_3 x1)) (?v_19 (hash_3 x2)) (?v_20 (hash_3 x3)) (?v_21 (hash_3 x4)) (?v_22 (hash_3 x5)) (?v_23 (hash_3 x6)) (?v_24 (hash_3 x7)) (?v_25 (hash_3 x8)) (?v_26 (hash_3 x9)) (?v_27 (hash_4 x1)) (?v_28 (hash_4 x2)) (?v_29 (hash_4 x3)) (?v_30 (hash_4 x4)) (?v_31 (hash_4 x5)) (?v_32 (hash_4 x6)) (?v_33 (hash_4 x7)) (?v_34 (hash_4 x8)) (?v_35 (hash_4 x9)) (?v_36 (hash_5 x1)) (?v_37 (hash_5 x2)) (?v_38 (hash_5 x3)) (?v_39 (hash_5 x4)) (?v_40 (hash_5 x5)) (?v_41 (hash_5 x6)) (?v_42 (hash_5 x7)) (?v_43 (hash_5 x8)) (?v_44 (hash_5 x9)) (?v_45 (hash_6 x1)) (?v_46 (hash_6 x2)) (?v_47 (hash_6 x3)) (?v_48 (hash_6 x4)) (?v_49 (hash_6 x5)) (?v_50 (hash_6 x6)) (?v_51 (hash_6 x7)) (?v_52 (hash_6 x8)) (?v_53 (hash_6 x9)) (?v_54 (hash_7 x1)) (?v_55 (hash_7 x2)) (?v_56 (hash_7 x3)) (?v_57 (hash_7 x4)) (?v_58 (hash_7 x5)) (?v_59 (hash_7 x6)) (?v_60 (hash_7 x7)) (?v_61 (hash_7 x8)) (?v_62 (hash_7 x9)) (?v_63 (hash_8 x1)) (?v_64 (hash_8 x2)) (?v_65 (hash_8 x3)) (?v_66 (hash_8 x4)) (?v_67 (hash_8 x5)) (?v_68 (hash_8 x6)) (?v_69 (hash_8 x7)) (?v_70 (hash_8 x8)) (?v_71 (hash_8 x9)) (?v_72 (hash_9 x1)) (?v_73 (hash_9 x2)) (?v_74 (hash_9 x3)) (?v_75 (hash_9 x4)) (?v_76 (hash_9 x5)) (?v_77 (hash_9 x6)) (?v_78 (hash_9 x7)) (?v_79 (hash_9 x8)) (?v_80 (hash_9 x9)) (?v_81 (hash_10 x1)) (?v_82 (hash_10 x2)) (?v_83 (hash_10 x3)) (?v_84 (hash_10 x4)) (?v_85 (hash_10 x5)) (?v_86 (hash_10 x6)) (?v_87 (hash_10 x7)) (?v_88 (hash_10 x8)) (?v_89 (hash_10 x9)) (?v_90 (hash_11 x1)) (?v_91 (hash_11 x2)) (?v_92 (hash_11 x3)) (?v_93 (hash_11 x4)) (?v_94 (hash_11 x5)) (?v_95 (hash_11 x6)) (?v_96 (hash_11 x7)) (?v_97 (hash_11 x8)) (?v_98 (hash_11 x9)) (?v_99 (hash_12 x1)) (?v_100 (hash_12 x2)) (?v_101 (hash_12 x3)) (?v_102 (hash_12 x4)) (?v_103 (hash_12 x5)) (?v_104 (hash_12 x6)) (?v_105 (hash_12 x7)) (?v_106 (hash_12 x8)) (?v_107 (hash_12 x9)) (?v_108 (hash_13 x1)) (?v_109 (hash_13 x2)) (?v_110 (hash_13 x3)) (?v_111 (hash_13 x4)) (?v_112 (hash_13 x5)) (?v_113 (hash_13 x6)) (?v_114 (hash_13 x7)) (?v_115 (hash_13 x8)) (?v_116 (hash_13 x9)) (?v_117 (+ x1 x9)) (?v_118 (+ x1 x2))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (distinct ?v_0 ?v_1) (distinct ?v_0 ?v_2)) (distinct ?v_0 ?v_3)) (distinct ?v_0 ?v_4)) (distinct ?v_0 ?v_5)) (distinct ?v_0 ?v_6)) (distinct ?v_0 ?v_7)) (distinct ?v_0 ?v_8)) (distinct ?v_1 ?v_2)) (distinct ?v_1 ?v_3)) (distinct ?v_1 ?v_4)) (distinct ?v_1 ?v_5)) (distinct ?v_1 ?v_6)) (distinct ?v_1 ?v_7)) (distinct ?v_1 ?v_8)) (distinct ?v_2 ?v_3)) (distinct ?v_2 ?v_4)) (distinct ?v_2 ?v_5)) (distinct ?v_2 ?v_6)) (distinct ?v_2 ?v_7)) (distinct ?v_2 ?v_8)) (distinct ?v_3 ?v_4)) (distinct ?v_3 ?v_5)) (distinct ?v_3 ?v_6)) (distinct ?v_3 ?v_7)) (distinct ?v_3 ?v_8)) (distinct ?v_4 ?v_5)) (distinct ?v_4 ?v_6)) (distinct ?v_4 ?v_7)) (distinct ?v_4 ?v_8)) (distinct ?v_5 ?v_6)) (distinct ?v_5 ?v_7)) (distinct ?v_5 ?v_8)) (distinct ?v_6 ?v_7)) (distinct ?v_6 ?v_8)) (distinct ?v_7 ?v_8)) (distinct ?v_9 ?v_10)) (distinct ?v_9 ?v_11)) (distinct ?v_9 ?v_12)) (distinct ?v_9 ?v_13)) (distinct ?v_9 ?v_14)) (distinct ?v_9 ?v_15)) (distinct ?v_9 ?v_16)) (distinct ?v_9 ?v_17)) (distinct ?v_10 ?v_11)) (distinct ?v_10 ?v_12)) (distinct ?v_10 ?v_13)) (distinct ?v_10 ?v_14)) (distinct ?v_10 ?v_15)) (distinct ?v_10 ?v_16)) (distinct ?v_10 ?v_17)) (distinct ?v_11 ?v_12)) (distinct ?v_11 ?v_13)) (distinct ?v_11 ?v_14)) (distinct ?v_11 ?v_15)) (distinct ?v_11 ?v_16)) (distinct ?v_11 ?v_17)) (distinct ?v_12 ?v_13)) (distinct ?v_12 ?v_14)) (distinct ?v_12 ?v_15)) (distinct ?v_12 ?v_16)) (distinct ?v_12 ?v_17)) (distinct ?v_13 ?v_14)) (distinct ?v_13 ?v_15)) (distinct ?v_13 ?v_16)) (distinct ?v_13 ?v_17)) (distinct ?v_14 ?v_15)) (distinct ?v_14 ?v_16)) (distinct ?v_14 ?v_17)) (distinct ?v_15 ?v_16)) (distinct ?v_15 ?v_17)) (distinct ?v_16 ?v_17)) (distinct ?v_18 ?v_19)) (distinct ?v_18 ?v_20)) (distinct ?v_18 ?v_21)) (distinct ?v_18 ?v_22)) (distinct ?v_18 ?v_23)) (distinct ?v_18 ?v_24)) (distinct ?v_18 ?v_25)) (distinct ?v_18 ?v_26)) (distinct ?v_19 ?v_20)) (distinct ?v_19 ?v_21)) (distinct ?v_19 ?v_22)) (distinct ?v_19 ?v_23)) (distinct ?v_19 ?v_24)) (distinct ?v_19 ?v_25)) (distinct ?v_19 ?v_26)) (distinct ?v_20 ?v_21)) (distinct ?v_20 ?v_22)) (distinct ?v_20 ?v_23)) (distinct ?v_20 ?v_24)) (distinct ?v_20 ?v_25)) (distinct ?v_20 ?v_26)) (distinct ?v_21 ?v_22)) (distinct ?v_21 ?v_23)) (distinct ?v_21 ?v_24)) (distinct ?v_21 ?v_25)) (distinct ?v_21 ?v_26)) (distinct ?v_22 ?v_23)) (distinct ?v_22 ?v_24)) (distinct ?v_22 ?v_25)) (distinct ?v_22 ?v_26)) (distinct ?v_23 ?v_24)) (distinct ?v_23 ?v_25)) (distinct ?v_23 ?v_26)) (distinct ?v_24 ?v_25)) (distinct ?v_24 ?v_26)) (distinct ?v_25 ?v_26)) (distinct ?v_27 ?v_28)) (distinct ?v_27 ?v_29)) (distinct ?v_27 ?v_30)) (distinct ?v_27 ?v_31)) (distinct ?v_27 ?v_32)) (distinct ?v_27 ?v_33)) (distinct ?v_27 ?v_34)) (distinct ?v_27 ?v_35)) (distinct ?v_28 ?v_29)) (distinct ?v_28 ?v_30)) (distinct ?v_28 ?v_31)) (distinct ?v_28 ?v_32)) (distinct ?v_28 ?v_33)) (distinct ?v_28 ?v_34)) (distinct ?v_28 ?v_35)) (distinct ?v_29 ?v_30)) (distinct ?v_29 ?v_31)) (distinct ?v_29 ?v_32)) (distinct ?v_29 ?v_33)) (distinct ?v_29 ?v_34)) (distinct ?v_29 ?v_35)) (distinct ?v_30 ?v_31)) (distinct ?v_30 ?v_32)) (distinct ?v_30 ?v_33)) (distinct ?v_30 ?v_34)) (distinct ?v_30 ?v_35)) (distinct ?v_31 ?v_32)) (distinct ?v_31 ?v_33)) (distinct ?v_31 ?v_34)) (distinct ?v_31 ?v_35)) (distinct ?v_32 ?v_33)) (distinct ?v_32 ?v_34)) (distinct ?v_32 ?v_35)) (distinct ?v_33 ?v_34)) (distinct ?v_33 ?v_35)) (distinct ?v_34 ?v_35)) (distinct ?v_36 ?v_37)) (distinct ?v_36 ?v_38)) (distinct ?v_36 ?v_39)) (distinct ?v_36 ?v_40)) (distinct ?v_36 ?v_41)) (distinct ?v_36 ?v_42)) (distinct ?v_36 ?v_43)) (distinct ?v_36 ?v_44)) (distinct ?v_37 ?v_38)) (distinct ?v_37 ?v_39)) (distinct ?v_37 ?v_40)) (distinct ?v_37 ?v_41)) (distinct ?v_37 ?v_42)) (distinct ?v_37 ?v_43)) (distinct ?v_37 ?v_44)) (distinct ?v_38 ?v_39)) (distinct ?v_38 ?v_40)) (distinct ?v_38 ?v_41)) (distinct ?v_38 ?v_42)) (distinct ?v_38 ?v_43)) (distinct ?v_38 ?v_44)) (distinct ?v_39 ?v_40)) (distinct ?v_39 ?v_41)) (distinct ?v_39 ?v_42)) (distinct ?v_39 ?v_43)) (distinct ?v_39 ?v_44)) (distinct ?v_40 ?v_41)) (distinct ?v_40 ?v_42)) (distinct ?v_40 ?v_43)) (distinct ?v_40 ?v_44)) (distinct ?v_41 ?v_42)) (distinct ?v_41 ?v_43)) (distinct ?v_41 ?v_44)) (distinct ?v_42 ?v_43)) (distinct ?v_42 ?v_44)) (distinct ?v_43 ?v_44)) (distinct ?v_45 ?v_46)) (distinct ?v_45 ?v_47)) (distinct ?v_45 ?v_48)) (distinct ?v_45 ?v_49)) (distinct ?v_45 ?v_50)) (distinct ?v_45 ?v_51)) (distinct ?v_45 ?v_52)) (distinct ?v_45 ?v_53)) (distinct ?v_46 ?v_47)) (distinct ?v_46 ?v_48)) (distinct ?v_46 ?v_49)) (distinct ?v_46 ?v_50)) (distinct ?v_46 ?v_51)) (distinct ?v_46 ?v_52)) (distinct ?v_46 ?v_53)) (distinct ?v_47 ?v_48)) (distinct ?v_47 ?v_49)) (distinct ?v_47 ?v_50)) (distinct ?v_47 ?v_51)) (distinct ?v_47 ?v_52)) (distinct ?v_47 ?v_53)) (distinct ?v_48 ?v_49)) (distinct ?v_48 ?v_50)) (distinct ?v_48 ?v_51)) (distinct ?v_48 ?v_52)) (distinct ?v_48 ?v_53)) (distinct ?v_49 ?v_50)) (distinct ?v_49 ?v_51)) (distinct ?v_49 ?v_52)) (distinct ?v_49 ?v_53)) (distinct ?v_50 ?v_51)) (distinct ?v_50 ?v_52)) (distinct ?v_50 ?v_53)) (distinct ?v_51 ?v_52)) (distinct ?v_51 ?v_53)) (distinct ?v_52 ?v_53)) (distinct ?v_54 ?v_55)) (distinct ?v_54 ?v_56)) (distinct ?v_54 ?v_57)) (distinct ?v_54 ?v_58)) (distinct ?v_54 ?v_59)) (distinct ?v_54 ?v_60)) (distinct ?v_54 ?v_61)) (distinct ?v_54 ?v_62)) (distinct ?v_55 ?v_56)) (distinct ?v_55 ?v_57)) (distinct ?v_55 ?v_58)) (distinct ?v_55 ?v_59)) (distinct ?v_55 ?v_60)) (distinct ?v_55 ?v_61)) (distinct ?v_55 ?v_62)) (distinct ?v_56 ?v_57)) (distinct ?v_56 ?v_58)) (distinct ?v_56 ?v_59)) (distinct ?v_56 ?v_60)) (distinct ?v_56 ?v_61)) (distinct ?v_56 ?v_62)) (distinct ?v_57 ?v_58)) (distinct ?v_57 ?v_59)) (distinct ?v_57 ?v_60)) (distinct ?v_57 ?v_61)) (distinct ?v_57 ?v_62)) (distinct ?v_58 ?v_59)) (distinct ?v_58 ?v_60)) (distinct ?v_58 ?v_61)) (distinct ?v_58 ?v_62)) (distinct ?v_59 ?v_60)) (distinct ?v_59 ?v_61)) (distinct ?v_59 ?v_62)) (distinct ?v_60 ?v_61)) (distinct ?v_60 ?v_62)) (distinct ?v_61 ?v_62)) (distinct ?v_63 ?v_64)) (distinct ?v_63 ?v_65)) (distinct ?v_63 ?v_66)) (distinct ?v_63 ?v_67)) (distinct ?v_63 ?v_68)) (distinct ?v_63 ?v_69)) (distinct ?v_63 ?v_70)) (distinct ?v_63 ?v_71)) (distinct ?v_64 ?v_65)) (distinct ?v_64 ?v_66)) (distinct ?v_64 ?v_67)) (distinct ?v_64 ?v_68)) (distinct ?v_64 ?v_69)) (distinct ?v_64 ?v_70)) (distinct ?v_64 ?v_71)) (distinct ?v_65 ?v_66)) (distinct ?v_65 ?v_67)) (distinct ?v_65 ?v_68)) (distinct ?v_65 ?v_69)) (distinct ?v_65 ?v_70)) (distinct ?v_65 ?v_71)) (distinct ?v_66 ?v_67)) (distinct ?v_66 ?v_68)) (distinct ?v_66 ?v_69)) (distinct ?v_66 ?v_70)) (distinct ?v_66 ?v_71)) (distinct ?v_67 ?v_68)) (distinct ?v_67 ?v_69)) (distinct ?v_67 ?v_70)) (distinct ?v_67 ?v_71)) (distinct ?v_68 ?v_69)) (distinct ?v_68 ?v_70)) (distinct ?v_68 ?v_71)) (distinct ?v_69 ?v_70)) (distinct ?v_69 ?v_71)) (distinct ?v_70 ?v_71)) (distinct ?v_72 ?v_73)) (distinct ?v_72 ?v_74)) (distinct ?v_72 ?v_75)) (distinct ?v_72 ?v_76)) (distinct ?v_72 ?v_77)) (distinct ?v_72 ?v_78)) (distinct ?v_72 ?v_79)) (distinct ?v_72 ?v_80)) (distinct ?v_73 ?v_74)) (distinct ?v_73 ?v_75)) (distinct ?v_73 ?v_76)) (distinct ?v_73 ?v_77)) (distinct ?v_73 ?v_78)) (distinct ?v_73 ?v_79)) (distinct ?v_73 ?v_80)) (distinct ?v_74 ?v_75)) (distinct ?v_74 ?v_76)) (distinct ?v_74 ?v_77)) (distinct ?v_74 ?v_78)) (distinct ?v_74 ?v_79)) (distinct ?v_74 ?v_80)) (distinct ?v_75 ?v_76)) (distinct ?v_75 ?v_77)) (distinct ?v_75 ?v_78)) (distinct ?v_75 ?v_79)) (distinct ?v_75 ?v_80)) (distinct ?v_76 ?v_77)) (distinct ?v_76 ?v_78)) (distinct ?v_76 ?v_79)) (distinct ?v_76 ?v_80)) (distinct ?v_77 ?v_78)) (distinct ?v_77 ?v_79)) (distinct ?v_77 ?v_80)) (distinct ?v_78 ?v_79)) (distinct ?v_78 ?v_80)) (distinct ?v_79 ?v_80)) (distinct ?v_81 ?v_82)) (distinct ?v_81 ?v_83)) (distinct ?v_81 ?v_84)) (distinct ?v_81 ?v_85)) (distinct ?v_81 ?v_86)) (distinct ?v_81 ?v_87)) (distinct ?v_81 ?v_88)) (distinct ?v_81 ?v_89)) (distinct ?v_82 ?v_83)) (distinct ?v_82 ?v_84)) (distinct ?v_82 ?v_85)) (distinct ?v_82 ?v_86)) (distinct ?v_82 ?v_87)) (distinct ?v_82 ?v_88)) (distinct ?v_82 ?v_89)) (distinct ?v_83 ?v_84)) (distinct ?v_83 ?v_85)) (distinct ?v_83 ?v_86)) (distinct ?v_83 ?v_87)) (distinct ?v_83 ?v_88)) (distinct ?v_83 ?v_89)) (distinct ?v_84 ?v_85)) (distinct ?v_84 ?v_86)) (distinct ?v_84 ?v_87)) (distinct ?v_84 ?v_88)) (distinct ?v_84 ?v_89)) (distinct ?v_85 ?v_86)) (distinct ?v_85 ?v_87)) (distinct ?v_85 ?v_88)) (distinct ?v_85 ?v_89)) (distinct ?v_86 ?v_87)) (distinct ?v_86 ?v_88)) (distinct ?v_86 ?v_89)) (distinct ?v_87 ?v_88)) (distinct ?v_87 ?v_89)) (distinct ?v_88 ?v_89)) (distinct ?v_90 ?v_91)) (distinct ?v_90 ?v_92)) (distinct ?v_90 ?v_93)) (distinct ?v_90 ?v_94)) (distinct ?v_90 ?v_95)) (distinct ?v_90 ?v_96)) (distinct ?v_90 ?v_97)) (distinct ?v_90 ?v_98)) (distinct ?v_91 ?v_92)) (distinct ?v_91 ?v_93)) (distinct ?v_91 ?v_94)) (distinct ?v_91 ?v_95)) (distinct ?v_91 ?v_96)) (distinct ?v_91 ?v_97)) (distinct ?v_91 ?v_98)) (distinct ?v_92 ?v_93)) (distinct ?v_92 ?v_94)) (distinct ?v_92 ?v_95)) (distinct ?v_92 ?v_96)) (distinct ?v_92 ?v_97)) (distinct ?v_92 ?v_98)) (distinct ?v_93 ?v_94)) (distinct ?v_93 ?v_95)) (distinct ?v_93 ?v_96)) (distinct ?v_93 ?v_97)) (distinct ?v_93 ?v_98)) (distinct ?v_94 ?v_95)) (distinct ?v_94 ?v_96)) (distinct ?v_94 ?v_97)) (distinct ?v_94 ?v_98)) (distinct ?v_95 ?v_96)) (distinct ?v_95 ?v_97)) (distinct ?v_95 ?v_98)) (distinct ?v_96 ?v_97)) (distinct ?v_96 ?v_98)) (distinct ?v_97 ?v_98)) (distinct ?v_99 ?v_100)) (distinct ?v_99 ?v_101)) (distinct ?v_99 ?v_102)) (distinct ?v_99 ?v_103)) (distinct ?v_99 ?v_104)) (distinct ?v_99 ?v_105)) (distinct ?v_99 ?v_106)) (distinct ?v_99 ?v_107)) (distinct ?v_100 ?v_101)) (distinct ?v_100 ?v_102)) (distinct ?v_100 ?v_103)) (distinct ?v_100 ?v_104)) (distinct ?v_100 ?v_105)) (distinct ?v_100 ?v_106)) (distinct ?v_100 ?v_107)) (distinct ?v_101 ?v_102)) (distinct ?v_101 ?v_103)) (distinct ?v_101 ?v_104)) (distinct ?v_101 ?v_105)) (distinct ?v_101 ?v_106)) (distinct ?v_101 ?v_107)) (distinct ?v_102 ?v_103)) (distinct ?v_102 ?v_104)) (distinct ?v_102 ?v_105)) (distinct ?v_102 ?v_106)) (distinct ?v_102 ?v_107)) (distinct ?v_103 ?v_104)) (distinct ?v_103 ?v_105)) (distinct ?v_103 ?v_106)) (distinct ?v_103 ?v_107)) (distinct ?v_104 ?v_105)) (distinct ?v_104 ?v_106)) (distinct ?v_104 ?v_107)) (distinct ?v_105 ?v_106)) (distinct ?v_105 ?v_107)) (distinct ?v_106 ?v_107)) (distinct ?v_108 ?v_109)) (distinct ?v_108 ?v_110)) (distinct ?v_108 ?v_111)) (distinct ?v_108 ?v_112)) (distinct ?v_108 ?v_113)) (distinct ?v_108 ?v_114)) (distinct ?v_108 ?v_115)) (distinct ?v_108 ?v_116)) (distinct ?v_109 ?v_110)) (distinct ?v_109 ?v_111)) (distinct ?v_109 ?v_112)) (distinct ?v_109 ?v_113)) (distinct ?v_109 ?v_114)) (distinct ?v_109 ?v_115)) (distinct ?v_109 ?v_116)) (distinct ?v_110 ?v_111)) (distinct ?v_110 ?v_112)) (distinct ?v_110 ?v_113)) (distinct ?v_110 ?v_114)) (distinct ?v_110 ?v_115)) (distinct ?v_110 ?v_116)) (distinct ?v_111 ?v_112)) (distinct ?v_111 ?v_113)) (distinct ?v_111 ?v_114)) (distinct ?v_111 ?v_115)) (distinct ?v_111 ?v_116)) (distinct ?v_112 ?v_113)) (distinct ?v_112 ?v_114)) (distinct ?v_112 ?v_115)) (distinct ?v_112 ?v_116)) (distinct ?v_113 ?v_114)) (distinct ?v_113 ?v_115)) (distinct ?v_113 ?v_116)) (distinct ?v_114 ?v_115)) (distinct ?v_114 ?v_116)) (distinct ?v_115 ?v_116)) (or (or (or (or (or (or (or (or (= ?v_0 x1) (= ?v_0 x2)) (= ?v_0 x3)) (= ?v_0 x4)) (= ?v_0 x5)) (= ?v_0 x6)) (= ?v_0 x7)) (= ?v_0 x8)) (= ?v_0 x9))) (or (or (or (or (or (or (or (or (= ?v_1 x1) (= ?v_1 x2)) (= ?v_1 x3)) (= ?v_1 x4)) (= ?v_1 x5)) (= ?v_1 x6)) (= ?v_1 x7)) (= ?v_1 x8)) (= ?v_1 x9))) (or (or (or (or (or (or (or (or (= ?v_2 x1) (= ?v_2 x2)) (= ?v_2 x3)) (= ?v_2 x4)) (= ?v_2 x5)) (= ?v_2 x6)) (= ?v_2 x7)) (= ?v_2 x8)) (= ?v_2 x9))) (or (or (or (or (or (or (or (or (= ?v_3 x1) (= ?v_3 x2)) (= ?v_3 x3)) (= ?v_3 x4)) (= ?v_3 x5)) (= ?v_3 x6)) (= ?v_3 x7)) (= ?v_3 x8)) (= ?v_3 x9))) (or (or (or (or (or (or (or (or (= ?v_4 x1) (= ?v_4 x2)) (= ?v_4 x3)) (= ?v_4 x4)) (= ?v_4 x5)) (= ?v_4 x6)) (= ?v_4 x7)) (= ?v_4 x8)) (= ?v_4 x9))) (or (or (or (or (or (or (or (or (= ?v_5 x1) (= ?v_5 x2)) (= ?v_5 x3)) (= ?v_5 x4)) (= ?v_5 x5)) (= ?v_5 x6)) (= ?v_5 x7)) (= ?v_5 x8)) (= ?v_5 x9))) (or (or (or (or (or (or (or (or (= ?v_6 x1) (= ?v_6 x2)) (= ?v_6 x3)) (= ?v_6 x4)) (= ?v_6 x5)) (= ?v_6 x6)) (= ?v_6 x7)) (= ?v_6 x8)) (= ?v_6 x9))) (or (or (or (or (or (or (or (or (= ?v_7 x1) (= ?v_7 x2)) (= ?v_7 x3)) (= ?v_7 x4)) (= ?v_7 x5)) (= ?v_7 x6)) (= ?v_7 x7)) (= ?v_7 x8)) (= ?v_7 x9))) (or (or (or (or (or (or (or (or (= ?v_8 x1) (= ?v_8 x2)) (= ?v_8 x3)) (= ?v_8 x4)) (= ?v_8 x5)) (= ?v_8 x6)) (= ?v_8 x7)) (= ?v_8 x8)) (= ?v_8 x9))) (or (or (or (or (or (or (or (or (= ?v_9 x1) (= ?v_9 x2)) (= ?v_9 x3)) (= ?v_9 x4)) (= ?v_9 x5)) (= ?v_9 x6)) (= ?v_9 x7)) (= ?v_9 x8)) (= ?v_9 x9))) (or (or (or (or (or (or (or (or (= ?v_10 x1) (= ?v_10 x2)) (= ?v_10 x3)) (= ?v_10 x4)) (= ?v_10 x5)) (= ?v_10 x6)) (= ?v_10 x7)) (= ?v_10 x8)) (= ?v_10 x9))) (or (or (or (or (or (or (or (or (= ?v_11 x1) (= ?v_11 x2)) (= ?v_11 x3)) (= ?v_11 x4)) (= ?v_11 x5)) (= ?v_11 x6)) (= ?v_11 x7)) (= ?v_11 x8)) (= ?v_11 x9))) (or (or (or (or (or (or (or (or (= ?v_12 x1) (= ?v_12 x2)) (= ?v_12 x3)) (= ?v_12 x4)) (= ?v_12 x5)) (= ?v_12 x6)) (= ?v_12 x7)) (= ?v_12 x8)) (= ?v_12 x9))) (or (or (or (or (or (or (or (or (= ?v_13 x1) (= ?v_13 x2)) (= ?v_13 x3)) (= ?v_13 x4)) (= ?v_13 x5)) (= ?v_13 x6)) (= ?v_13 x7)) (= ?v_13 x8)) (= ?v_13 x9))) (or (or (or (or (or (or (or (or (= ?v_14 x1) (= ?v_14 x2)) (= ?v_14 x3)) (= ?v_14 x4)) (= ?v_14 x5)) (= ?v_14 x6)) (= ?v_14 x7)) (= ?v_14 x8)) (= ?v_14 x9))) (or (or (or (or (or (or (or (or (= ?v_15 x1) (= ?v_15 x2)) (= ?v_15 x3)) (= ?v_15 x4)) (= ?v_15 x5)) (= ?v_15 x6)) (= ?v_15 x7)) (= ?v_15 x8)) (= ?v_15 x9))) (or (or (or (or (or (or (or (or (= ?v_16 x1) (= ?v_16 x2)) (= ?v_16 x3)) (= ?v_16 x4)) (= ?v_16 x5)) (= ?v_16 x6)) (= ?v_16 x7)) (= ?v_16 x8)) (= ?v_16 x9))) (or (or (or (or (or (or (or (or (= ?v_17 x1) (= ?v_17 x2)) (= ?v_17 x3)) (= ?v_17 x4)) (= ?v_17 x5)) (= ?v_17 x6)) (= ?v_17 x7)) (= ?v_17 x8)) (= ?v_17 x9))) (or (or (or (or (or (or (or (or (= ?v_18 x1) (= ?v_18 x2)) (= ?v_18 x3)) (= ?v_18 x4)) (= ?v_18 x5)) (= ?v_18 x6)) (= ?v_18 x7)) (= ?v_18 x8)) (= ?v_18 x9))) (or (or (or (or (or (or (or (or (= ?v_19 x1) (= ?v_19 x2)) (= ?v_19 x3)) (= ?v_19 x4)) (= ?v_19 x5)) (= ?v_19 x6)) (= ?v_19 x7)) (= ?v_19 x8)) (= ?v_19 x9))) (or (or (or (or (or (or (or (or (= ?v_20 x1) (= ?v_20 x2)) (= ?v_20 x3)) (= ?v_20 x4)) (= ?v_20 x5)) (= ?v_20 x6)) (= ?v_20 x7)) (= ?v_20 x8)) (= ?v_20 x9))) (or (or (or (or (or (or (or (or (= ?v_21 x1) (= ?v_21 x2)) (= ?v_21 x3)) (= ?v_21 x4)) (= ?v_21 x5)) (= ?v_21 x6)) (= ?v_21 x7)) (= ?v_21 x8)) (= ?v_21 x9))) (or (or (or (or (or (or (or (or (= ?v_22 x1) (= ?v_22 x2)) (= ?v_22 x3)) (= ?v_22 x4)) (= ?v_22 x5)) (= ?v_22 x6)) (= ?v_22 x7)) (= ?v_22 x8)) (= ?v_22 x9))) (or (or (or (or (or (or (or (or (= ?v_23 x1) (= ?v_23 x2)) (= ?v_23 x3)) (= ?v_23 x4)) (= ?v_23 x5)) (= ?v_23 x6)) (= ?v_23 x7)) (= ?v_23 x8)) (= ?v_23 x9))) (or (or (or (or (or (or (or (or (= ?v_24 x1) (= ?v_24 x2)) (= ?v_24 x3)) (= ?v_24 x4)) (= ?v_24 x5)) (= ?v_24 x6)) (= ?v_24 x7)) (= ?v_24 x8)) (= ?v_24 x9))) (or (or (or (or (or (or (or (or (= ?v_25 x1) (= ?v_25 x2)) (= ?v_25 x3)) (= ?v_25 x4)) (= ?v_25 x5)) (= ?v_25 x6)) (= ?v_25 x7)) (= ?v_25 x8)) (= ?v_25 x9))) (or (or (or (or (or (or (or (or (= ?v_26 x1) (= ?v_26 x2)) (= ?v_26 x3)) (= ?v_26 x4)) (= ?v_26 x5)) (= ?v_26 x6)) (= ?v_26 x7)) (= ?v_26 x8)) (= ?v_26 x9))) (or (or (or (or (or (or (or (or (= ?v_27 x1) (= ?v_27 x2)) (= ?v_27 x3)) (= ?v_27 x4)) (= ?v_27 x5)) (= ?v_27 x6)) (= ?v_27 x7)) (= ?v_27 x8)) (= ?v_27 x9))) (or (or (or (or (or (or (or (or (= ?v_28 x1) (= ?v_28 x2)) (= ?v_28 x3)) (= ?v_28 x4)) (= ?v_28 x5)) (= ?v_28 x6)) (= ?v_28 x7)) (= ?v_28 x8)) (= ?v_28 x9))) (or (or (or (or (or (or (or (or (= ?v_29 x1) (= ?v_29 x2)) (= ?v_29 x3)) (= ?v_29 x4)) (= ?v_29 x5)) (= ?v_29 x6)) (= ?v_29 x7)) (= ?v_29 x8)) (= ?v_29 x9))) (or (or (or (or (or (or (or (or (= ?v_30 x1) (= ?v_30 x2)) (= ?v_30 x3)) (= ?v_30 x4)) (= ?v_30 x5)) (= ?v_30 x6)) (= ?v_30 x7)) (= ?v_30 x8)) (= ?v_30 x9))) (or (or (or (or (or (or (or (or (= ?v_31 x1) (= ?v_31 x2)) (= ?v_31 x3)) (= ?v_31 x4)) (= ?v_31 x5)) (= ?v_31 x6)) (= ?v_31 x7)) (= ?v_31 x8)) (= ?v_31 x9))) (or (or (or (or (or (or (or (or (= ?v_32 x1) (= ?v_32 x2)) (= ?v_32 x3)) (= ?v_32 x4)) (= ?v_32 x5)) (= ?v_32 x6)) (= ?v_32 x7)) (= ?v_32 x8)) (= ?v_32 x9))) (or (or (or (or (or (or (or (or (= ?v_33 x1) (= ?v_33 x2)) (= ?v_33 x3)) (= ?v_33 x4)) (= ?v_33 x5)) (= ?v_33 x6)) (= ?v_33 x7)) (= ?v_33 x8)) (= ?v_33 x9))) (or (or (or (or (or (or (or (or (= ?v_34 x1) (= ?v_34 x2)) (= ?v_34 x3)) (= ?v_34 x4)) (= ?v_34 x5)) (= ?v_34 x6)) (= ?v_34 x7)) (= ?v_34 x8)) (= ?v_34 x9))) (or (or (or (or (or (or (or (or (= ?v_35 x1) (= ?v_35 x2)) (= ?v_35 x3)) (= ?v_35 x4)) (= ?v_35 x5)) (= ?v_35 x6)) (= ?v_35 x7)) (= ?v_35 x8)) (= ?v_35 x9))) (or (or (or (or (or (or (or (or (= ?v_36 x1) (= ?v_36 x2)) (= ?v_36 x3)) (= ?v_36 x4)) (= ?v_36 x5)) (= ?v_36 x6)) (= ?v_36 x7)) (= ?v_36 x8)) (= ?v_36 x9))) (or (or (or (or (or (or (or (or (= ?v_37 x1) (= ?v_37 x2)) (= ?v_37 x3)) (= ?v_37 x4)) (= ?v_37 x5)) (= ?v_37 x6)) (= ?v_37 x7)) (= ?v_37 x8)) (= ?v_37 x9))) (or (or (or (or (or (or (or (or (= ?v_38 x1) (= ?v_38 x2)) (= ?v_38 x3)) (= ?v_38 x4)) (= ?v_38 x5)) (= ?v_38 x6)) (= ?v_38 x7)) (= ?v_38 x8)) (= ?v_38 x9))) (or (or (or (or (or (or (or (or (= ?v_39 x1) (= ?v_39 x2)) (= ?v_39 x3)) (= ?v_39 x4)) (= ?v_39 x5)) (= ?v_39 x6)) (= ?v_39 x7)) (= ?v_39 x8)) (= ?v_39 x9))) (or (or (or (or (or (or (or (or (= ?v_40 x1) (= ?v_40 x2)) (= ?v_40 x3)) (= ?v_40 x4)) (= ?v_40 x5)) (= ?v_40 x6)) (= ?v_40 x7)) (= ?v_40 x8)) (= ?v_40 x9))) (or (or (or (or (or (or (or (or (= ?v_41 x1) (= ?v_41 x2)) (= ?v_41 x3)) (= ?v_41 x4)) (= ?v_41 x5)) (= ?v_41 x6)) (= ?v_41 x7)) (= ?v_41 x8)) (= ?v_41 x9))) (or (or (or (or (or (or (or (or (= ?v_42 x1) (= ?v_42 x2)) (= ?v_42 x3)) (= ?v_42 x4)) (= ?v_42 x5)) (= ?v_42 x6)) (= ?v_42 x7)) (= ?v_42 x8)) (= ?v_42 x9))) (or (or (or (or (or (or (or (or (= ?v_43 x1) (= ?v_43 x2)) (= ?v_43 x3)) (= ?v_43 x4)) (= ?v_43 x5)) (= ?v_43 x6)) (= ?v_43 x7)) (= ?v_43 x8)) (= ?v_43 x9))) (or (or (or (or (or (or (or (or (= ?v_44 x1) (= ?v_44 x2)) (= ?v_44 x3)) (= ?v_44 x4)) (= ?v_44 x5)) (= ?v_44 x6)) (= ?v_44 x7)) (= ?v_44 x8)) (= ?v_44 x9))) (or (or (or (or (or (or (or (or (= ?v_45 x1) (= ?v_45 x2)) (= ?v_45 x3)) (= ?v_45 x4)) (= ?v_45 x5)) (= ?v_45 x6)) (= ?v_45 x7)) (= ?v_45 x8)) (= ?v_45 x9))) (or (or (or (or (or (or (or (or (= ?v_46 x1) (= ?v_46 x2)) (= ?v_46 x3)) (= ?v_46 x4)) (= ?v_46 x5)) (= ?v_46 x6)) (= ?v_46 x7)) (= ?v_46 x8)) (= ?v_46 x9))) (or (or (or (or (or (or (or (or (= ?v_47 x1) (= ?v_47 x2)) (= ?v_47 x3)) (= ?v_47 x4)) (= ?v_47 x5)) (= ?v_47 x6)) (= ?v_47 x7)) (= ?v_47 x8)) (= ?v_47 x9))) (or (or (or (or (or (or (or (or (= ?v_48 x1) (= ?v_48 x2)) (= ?v_48 x3)) (= ?v_48 x4)) (= ?v_48 x5)) (= ?v_48 x6)) (= ?v_48 x7)) (= ?v_48 x8)) (= ?v_48 x9))) (or (or (or (or (or (or (or (or (= ?v_49 x1) (= ?v_49 x2)) (= ?v_49 x3)) (= ?v_49 x4)) (= ?v_49 x5)) (= ?v_49 x6)) (= ?v_49 x7)) (= ?v_49 x8)) (= ?v_49 x9))) (or (or (or (or (or (or (or (or (= ?v_50 x1) (= ?v_50 x2)) (= ?v_50 x3)) (= ?v_50 x4)) (= ?v_50 x5)) (= ?v_50 x6)) (= ?v_50 x7)) (= ?v_50 x8)) (= ?v_50 x9))) (or (or (or (or (or (or (or (or (= ?v_51 x1) (= ?v_51 x2)) (= ?v_51 x3)) (= ?v_51 x4)) (= ?v_51 x5)) (= ?v_51 x6)) (= ?v_51 x7)) (= ?v_51 x8)) (= ?v_51 x9))) (or (or (or (or (or (or (or (or (= ?v_52 x1) (= ?v_52 x2)) (= ?v_52 x3)) (= ?v_52 x4)) (= ?v_52 x5)) (= ?v_52 x6)) (= ?v_52 x7)) (= ?v_52 x8)) (= ?v_52 x9))) (or (or (or (or (or (or (or (or (= ?v_53 x1) (= ?v_53 x2)) (= ?v_53 x3)) (= ?v_53 x4)) (= ?v_53 x5)) (= ?v_53 x6)) (= ?v_53 x7)) (= ?v_53 x8)) (= ?v_53 x9))) (or (or (or (or (or (or (or (or (= ?v_54 x1) (= ?v_54 x2)) (= ?v_54 x3)) (= ?v_54 x4)) (= ?v_54 x5)) (= ?v_54 x6)) (= ?v_54 x7)) (= ?v_54 x8)) (= ?v_54 x9))) (or (or (or (or (or (or (or (or (= ?v_55 x1) (= ?v_55 x2)) (= ?v_55 x3)) (= ?v_55 x4)) (= ?v_55 x5)) (= ?v_55 x6)) (= ?v_55 x7)) (= ?v_55 x8)) (= ?v_55 x9))) (or (or (or (or (or (or (or (or (= ?v_56 x1) (= ?v_56 x2)) (= ?v_56 x3)) (= ?v_56 x4)) (= ?v_56 x5)) (= ?v_56 x6)) (= ?v_56 x7)) (= ?v_56 x8)) (= ?v_56 x9))) (or (or (or (or (or (or (or (or (= ?v_57 x1) (= ?v_57 x2)) (= ?v_57 x3)) (= ?v_57 x4)) (= ?v_57 x5)) (= ?v_57 x6)) (= ?v_57 x7)) (= ?v_57 x8)) (= ?v_57 x9))) (or (or (or (or (or (or (or (or (= ?v_58 x1) (= ?v_58 x2)) (= ?v_58 x3)) (= ?v_58 x4)) (= ?v_58 x5)) (= ?v_58 x6)) (= ?v_58 x7)) (= ?v_58 x8)) (= ?v_58 x9))) (or (or (or (or (or (or (or (or (= ?v_59 x1) (= ?v_59 x2)) (= ?v_59 x3)) (= ?v_59 x4)) (= ?v_59 x5)) (= ?v_59 x6)) (= ?v_59 x7)) (= ?v_59 x8)) (= ?v_59 x9))) (or (or (or (or (or (or (or (or (= ?v_60 x1) (= ?v_60 x2)) (= ?v_60 x3)) (= ?v_60 x4)) (= ?v_60 x5)) (= ?v_60 x6)) (= ?v_60 x7)) (= ?v_60 x8)) (= ?v_60 x9))) (or (or (or (or (or (or (or (or (= ?v_61 x1) (= ?v_61 x2)) (= ?v_61 x3)) (= ?v_61 x4)) (= ?v_61 x5)) (= ?v_61 x6)) (= ?v_61 x7)) (= ?v_61 x8)) (= ?v_61 x9))) (or (or (or (or (or (or (or (or (= ?v_62 x1) (= ?v_62 x2)) (= ?v_62 x3)) (= ?v_62 x4)) (= ?v_62 x5)) (= ?v_62 x6)) (= ?v_62 x7)) (= ?v_62 x8)) (= ?v_62 x9))) (or (or (or (or (or (or (or (or (= ?v_63 x1) (= ?v_63 x2)) (= ?v_63 x3)) (= ?v_63 x4)) (= ?v_63 x5)) (= ?v_63 x6)) (= ?v_63 x7)) (= ?v_63 x8)) (= ?v_63 x9))) (or (or (or (or (or (or (or (or (= ?v_64 x1) (= ?v_64 x2)) (= ?v_64 x3)) (= ?v_64 x4)) (= ?v_64 x5)) (= ?v_64 x6)) (= ?v_64 x7)) (= ?v_64 x8)) (= ?v_64 x9))) (or (or (or (or (or (or (or (or (= ?v_65 x1) (= ?v_65 x2)) (= ?v_65 x3)) (= ?v_65 x4)) (= ?v_65 x5)) (= ?v_65 x6)) (= ?v_65 x7)) (= ?v_65 x8)) (= ?v_65 x9))) (or (or (or (or (or (or (or (or (= ?v_66 x1) (= ?v_66 x2)) (= ?v_66 x3)) (= ?v_66 x4)) (= ?v_66 x5)) (= ?v_66 x6)) (= ?v_66 x7)) (= ?v_66 x8)) (= ?v_66 x9))) (or (or (or (or (or (or (or (or (= ?v_67 x1) (= ?v_67 x2)) (= ?v_67 x3)) (= ?v_67 x4)) (= ?v_67 x5)) (= ?v_67 x6)) (= ?v_67 x7)) (= ?v_67 x8)) (= ?v_67 x9))) (or (or (or (or (or (or (or (or (= ?v_68 x1) (= ?v_68 x2)) (= ?v_68 x3)) (= ?v_68 x4)) (= ?v_68 x5)) (= ?v_68 x6)) (= ?v_68 x7)) (= ?v_68 x8)) (= ?v_68 x9))) (or (or (or (or (or (or (or (or (= ?v_69 x1) (= ?v_69 x2)) (= ?v_69 x3)) (= ?v_69 x4)) (= ?v_69 x5)) (= ?v_69 x6)) (= ?v_69 x7)) (= ?v_69 x8)) (= ?v_69 x9))) (or (or (or (or (or (or (or (or (= ?v_70 x1) (= ?v_70 x2)) (= ?v_70 x3)) (= ?v_70 x4)) (= ?v_70 x5)) (= ?v_70 x6)) (= ?v_70 x7)) (= ?v_70 x8)) (= ?v_70 x9))) (or (or (or (or (or (or (or (or (= ?v_71 x1) (= ?v_71 x2)) (= ?v_71 x3)) (= ?v_71 x4)) (= ?v_71 x5)) (= ?v_71 x6)) (= ?v_71 x7)) (= ?v_71 x8)) (= ?v_71 x9))) (or (or (or (or (or (or (or (or (= ?v_72 x1) (= ?v_72 x2)) (= ?v_72 x3)) (= ?v_72 x4)) (= ?v_72 x5)) (= ?v_72 x6)) (= ?v_72 x7)) (= ?v_72 x8)) (= ?v_72 x9))) (or (or (or (or (or (or (or (or (= ?v_73 x1) (= ?v_73 x2)) (= ?v_73 x3)) (= ?v_73 x4)) (= ?v_73 x5)) (= ?v_73 x6)) (= ?v_73 x7)) (= ?v_73 x8)) (= ?v_73 x9))) (or (or (or (or (or (or (or (or (= ?v_74 x1) (= ?v_74 x2)) (= ?v_74 x3)) (= ?v_74 x4)) (= ?v_74 x5)) (= ?v_74 x6)) (= ?v_74 x7)) (= ?v_74 x8)) (= ?v_74 x9))) (or (or (or (or (or (or (or (or (= ?v_75 x1) (= ?v_75 x2)) (= ?v_75 x3)) (= ?v_75 x4)) (= ?v_75 x5)) (= ?v_75 x6)) (= ?v_75 x7)) (= ?v_75 x8)) (= ?v_75 x9))) (or (or (or (or (or (or (or (or (= ?v_76 x1) (= ?v_76 x2)) (= ?v_76 x3)) (= ?v_76 x4)) (= ?v_76 x5)) (= ?v_76 x6)) (= ?v_76 x7)) (= ?v_76 x8)) (= ?v_76 x9))) (or (or (or (or (or (or (or (or (= ?v_77 x1) (= ?v_77 x2)) (= ?v_77 x3)) (= ?v_77 x4)) (= ?v_77 x5)) (= ?v_77 x6)) (= ?v_77 x7)) (= ?v_77 x8)) (= ?v_77 x9))) (or (or (or (or (or (or (or (or (= ?v_78 x1) (= ?v_78 x2)) (= ?v_78 x3)) (= ?v_78 x4)) (= ?v_78 x5)) (= ?v_78 x6)) (= ?v_78 x7)) (= ?v_78 x8)) (= ?v_78 x9))) (or (or (or (or (or (or (or (or (= ?v_79 x1) (= ?v_79 x2)) (= ?v_79 x3)) (= ?v_79 x4)) (= ?v_79 x5)) (= ?v_79 x6)) (= ?v_79 x7)) (= ?v_79 x8)) (= ?v_79 x9))) (or (or (or (or (or (or (or (or (= ?v_80 x1) (= ?v_80 x2)) (= ?v_80 x3)) (= ?v_80 x4)) (= ?v_80 x5)) (= ?v_80 x6)) (= ?v_80 x7)) (= ?v_80 x8)) (= ?v_80 x9))) (or (or (or (or (or (or (or (or (= ?v_81 x1) (= ?v_81 x2)) (= ?v_81 x3)) (= ?v_81 x4)) (= ?v_81 x5)) (= ?v_81 x6)) (= ?v_81 x7)) (= ?v_81 x8)) (= ?v_81 x9))) (or (or (or (or (or (or (or (or (= ?v_82 x1) (= ?v_82 x2)) (= ?v_82 x3)) (= ?v_82 x4)) (= ?v_82 x5)) (= ?v_82 x6)) (= ?v_82 x7)) (= ?v_82 x8)) (= ?v_82 x9))) (or (or (or (or (or (or (or (or (= ?v_83 x1) (= ?v_83 x2)) (= ?v_83 x3)) (= ?v_83 x4)) (= ?v_83 x5)) (= ?v_83 x6)) (= ?v_83 x7)) (= ?v_83 x8)) (= ?v_83 x9))) (or (or (or (or (or (or (or (or (= ?v_84 x1) (= ?v_84 x2)) (= ?v_84 x3)) (= ?v_84 x4)) (= ?v_84 x5)) (= ?v_84 x6)) (= ?v_84 x7)) (= ?v_84 x8)) (= ?v_84 x9))) (or (or (or (or (or (or (or (or (= ?v_85 x1) (= ?v_85 x2)) (= ?v_85 x3)) (= ?v_85 x4)) (= ?v_85 x5)) (= ?v_85 x6)) (= ?v_85 x7)) (= ?v_85 x8)) (= ?v_85 x9))) (or (or (or (or (or (or (or (or (= ?v_86 x1) (= ?v_86 x2)) (= ?v_86 x3)) (= ?v_86 x4)) (= ?v_86 x5)) (= ?v_86 x6)) (= ?v_86 x7)) (= ?v_86 x8)) (= ?v_86 x9))) (or (or (or (or (or (or (or (or (= ?v_87 x1) (= ?v_87 x2)) (= ?v_87 x3)) (= ?v_87 x4)) (= ?v_87 x5)) (= ?v_87 x6)) (= ?v_87 x7)) (= ?v_87 x8)) (= ?v_87 x9))) (or (or (or (or (or (or (or (or (= ?v_88 x1) (= ?v_88 x2)) (= ?v_88 x3)) (= ?v_88 x4)) (= ?v_88 x5)) (= ?v_88 x6)) (= ?v_88 x7)) (= ?v_88 x8)) (= ?v_88 x9))) (or (or (or (or (or (or (or (or (= ?v_89 x1) (= ?v_89 x2)) (= ?v_89 x3)) (= ?v_89 x4)) (= ?v_89 x5)) (= ?v_89 x6)) (= ?v_89 x7)) (= ?v_89 x8)) (= ?v_89 x9))) (or (or (or (or (or (or (or (or (= ?v_90 x1) (= ?v_90 x2)) (= ?v_90 x3)) (= ?v_90 x4)) (= ?v_90 x5)) (= ?v_90 x6)) (= ?v_90 x7)) (= ?v_90 x8)) (= ?v_90 x9))) (or (or (or (or (or (or (or (or (= ?v_91 x1) (= ?v_91 x2)) (= ?v_91 x3)) (= ?v_91 x4)) (= ?v_91 x5)) (= ?v_91 x6)) (= ?v_91 x7)) (= ?v_91 x8)) (= ?v_91 x9))) (or (or (or (or (or (or (or (or (= ?v_92 x1) (= ?v_92 x2)) (= ?v_92 x3)) (= ?v_92 x4)) (= ?v_92 x5)) (= ?v_92 x6)) (= ?v_92 x7)) (= ?v_92 x8)) (= ?v_92 x9))) (or (or (or (or (or (or (or (or (= ?v_93 x1) (= ?v_93 x2)) (= ?v_93 x3)) (= ?v_93 x4)) (= ?v_93 x5)) (= ?v_93 x6)) (= ?v_93 x7)) (= ?v_93 x8)) (= ?v_93 x9))) (or (or (or (or (or (or (or (or (= ?v_94 x1) (= ?v_94 x2)) (= ?v_94 x3)) (= ?v_94 x4)) (= ?v_94 x5)) (= ?v_94 x6)) (= ?v_94 x7)) (= ?v_94 x8)) (= ?v_94 x9))) (or (or (or (or (or (or (or (or (= ?v_95 x1) (= ?v_95 x2)) (= ?v_95 x3)) (= ?v_95 x4)) (= ?v_95 x5)) (= ?v_95 x6)) (= ?v_95 x7)) (= ?v_95 x8)) (= ?v_95 x9))) (or (or (or (or (or (or (or (or (= ?v_96 x1) (= ?v_96 x2)) (= ?v_96 x3)) (= ?v_96 x4)) (= ?v_96 x5)) (= ?v_96 x6)) (= ?v_96 x7)) (= ?v_96 x8)) (= ?v_96 x9))) (or (or (or (or (or (or (or (or (= ?v_97 x1) (= ?v_97 x2)) (= ?v_97 x3)) (= ?v_97 x4)) (= ?v_97 x5)) (= ?v_97 x6)) (= ?v_97 x7)) (= ?v_97 x8)) (= ?v_97 x9))) (or (or (or (or (or (or (or (or (= ?v_98 x1) (= ?v_98 x2)) (= ?v_98 x3)) (= ?v_98 x4)) (= ?v_98 x5)) (= ?v_98 x6)) (= ?v_98 x7)) (= ?v_98 x8)) (= ?v_98 x9))) (or (or (or (or (or (or (or (or (= ?v_99 x1) (= ?v_99 x2)) (= ?v_99 x3)) (= ?v_99 x4)) (= ?v_99 x5)) (= ?v_99 x6)) (= ?v_99 x7)) (= ?v_99 x8)) (= ?v_99 x9))) (or (or (or (or (or (or (or (or (= ?v_100 x1) (= ?v_100 x2)) (= ?v_100 x3)) (= ?v_100 x4)) (= ?v_100 x5)) (= ?v_100 x6)) (= ?v_100 x7)) (= ?v_100 x8)) (= ?v_100 x9))) (or (or (or (or (or (or (or (or (= ?v_101 x1) (= ?v_101 x2)) (= ?v_101 x3)) (= ?v_101 x4)) (= ?v_101 x5)) (= ?v_101 x6)) (= ?v_101 x7)) (= ?v_101 x8)) (= ?v_101 x9))) (or (or (or (or (or (or (or (or (= ?v_102 x1) (= ?v_102 x2)) (= ?v_102 x3)) (= ?v_102 x4)) (= ?v_102 x5)) (= ?v_102 x6)) (= ?v_102 x7)) (= ?v_102 x8)) (= ?v_102 x9))) (or (or (or (or (or (or (or (or (= ?v_103 x1) (= ?v_103 x2)) (= ?v_103 x3)) (= ?v_103 x4)) (= ?v_103 x5)) (= ?v_103 x6)) (= ?v_103 x7)) (= ?v_103 x8)) (= ?v_103 x9))) (or (or (or (or (or (or (or (or (= ?v_104 x1) (= ?v_104 x2)) (= ?v_104 x3)) (= ?v_104 x4)) (= ?v_104 x5)) (= ?v_104 x6)) (= ?v_104 x7)) (= ?v_104 x8)) (= ?v_104 x9))) (or (or (or (or (or (or (or (or (= ?v_105 x1) (= ?v_105 x2)) (= ?v_105 x3)) (= ?v_105 x4)) (= ?v_105 x5)) (= ?v_105 x6)) (= ?v_105 x7)) (= ?v_105 x8)) (= ?v_105 x9))) (or (or (or (or (or (or (or (or (= ?v_106 x1) (= ?v_106 x2)) (= ?v_106 x3)) (= ?v_106 x4)) (= ?v_106 x5)) (= ?v_106 x6)) (= ?v_106 x7)) (= ?v_106 x8)) (= ?v_106 x9))) (or (or (or (or (or (or (or (or (= ?v_107 x1) (= ?v_107 x2)) (= ?v_107 x3)) (= ?v_107 x4)) (= ?v_107 x5)) (= ?v_107 x6)) (= ?v_107 x7)) (= ?v_107 x8)) (= ?v_107 x9))) (or (or (or (or (or (or (or (or (= ?v_108 x1) (= ?v_108 x2)) (= ?v_108 x3)) (= ?v_108 x4)) (= ?v_108 x5)) (= ?v_108 x6)) (= ?v_108 x7)) (= ?v_108 x8)) (= ?v_108 x9))) (or (or (or (or (or (or (or (or (= ?v_109 x1) (= ?v_109 x2)) (= ?v_109 x3)) (= ?v_109 x4)) (= ?v_109 x5)) (= ?v_109 x6)) (= ?v_109 x7)) (= ?v_109 x8)) (= ?v_109 x9))) (or (or (or (or (or (or (or (or (= ?v_110 x1) (= ?v_110 x2)) (= ?v_110 x3)) (= ?v_110 x4)) (= ?v_110 x5)) (= ?v_110 x6)) (= ?v_110 x7)) (= ?v_110 x8)) (= ?v_110 x9))) (or (or (or (or (or (or (or (or (= ?v_111 x1) (= ?v_111 x2)) (= ?v_111 x3)) (= ?v_111 x4)) (= ?v_111 x5)) (= ?v_111 x6)) (= ?v_111 x7)) (= ?v_111 x8)) (= ?v_111 x9))) (or (or (or (or (or (or (or (or (= ?v_112 x1) (= ?v_112 x2)) (= ?v_112 x3)) (= ?v_112 x4)) (= ?v_112 x5)) (= ?v_112 x6)) (= ?v_112 x7)) (= ?v_112 x8)) (= ?v_112 x9))) (or (or (or (or (or (or (or (or (= ?v_113 x1) (= ?v_113 x2)) (= ?v_113 x3)) (= ?v_113 x4)) (= ?v_113 x5)) (= ?v_113 x6)) (= ?v_113 x7)) (= ?v_113 x8)) (= ?v_113 x9))) (or (or (or (or (or (or (or (or (= ?v_114 x1) (= ?v_114 x2)) (= ?v_114 x3)) (= ?v_114 x4)) (= ?v_114 x5)) (= ?v_114 x6)) (= ?v_114 x7)) (= ?v_114 x8)) (= ?v_114 x9))) (or (or (or (or (or (or (or (or (= ?v_115 x1) (= ?v_115 x2)) (= ?v_115 x3)) (= ?v_115 x4)) (= ?v_115 x5)) (= ?v_115 x6)) (= ?v_115 x7)) (= ?v_115 x8)) (= ?v_115 x9))) (or (or (or (or (or (or (or (or (= ?v_116 x1) (= ?v_116 x2)) (= ?v_116 x3)) (= ?v_116 x4)) (= ?v_116 x5)) (= ?v_116 x6)) (= ?v_116 x7)) (= ?v_116 x8)) (= ?v_116 x9))) (distinct x1 x2)) (distinct x1 x3)) (distinct x1 x4)) (distinct x1 x5)) (distinct x1 x6)) (distinct x1 x7)) (distinct x1 x8)) (distinct x1 x9)) (distinct x2 x3)) (distinct x2 x4)) (distinct x2 x5)) (distinct x2 x6)) (distinct x2 x7)) (distinct x2 x8)) (distinct x2 x9)) (distinct x3 x4)) (distinct x3 x5)) (distinct x3 x6)) (distinct x3 x7)) (distinct x3 x8)) (distinct x3 x9)) (distinct x4 x5)) (distinct x4 x6)) (distinct x4 x7)) (distinct x4 x8)) (distinct x4 x9)) (distinct x5 x6)) (distinct x5 x7)) (distinct x5 x8)) (distinct x5 x9)) (distinct x6 x7)) (distinct x6 x8)) (distinct x6 x9)) (distinct x7 x8)) (distinct x7 x9)) (distinct x8 x9)) (<= 0 x1)) (< x1 10)) (<= 0 x2)) (< x2 10)) (<= 0 x3)) (< x3 10)) (<= 0 x4)) (< x4 10)) (<= 0 x5)) (< x5 10)) (<= 0 x6)) (< x6 10)) (<= 0 x7)) (< x7 10)) (<= 0 x8)) (< x8 10)) (<= 0 x9)) (< x9 10)) (= (hash_1 (hash_1 (hash_13 (ite (< ?v_117 10) ?v_117 x1)))) (hash_1 (hash_1 (hash_13 (ite (< ?v_118 10) ?v_118 x1))))))))
(check-sat)
(exit)
