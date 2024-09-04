(set-info :smt-lib-version 2.6)
(set-logic SLHV)
(declare-hvar emp IntHeap)
(declare-locvar nil IntLoc)
(declare-datatype pt_record_0 ((Pt_R_0 (loc IntLoc))))
(declare-datatype pt_record_1 ((Pt_R_1 (data Int))))(set-info :source |
Benchmarks from Leonardo de Moura <demoura@csl.sri.com>

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x_0 () Int)
(declare-fun x_1 () Int)
(declare-fun x_2 () (Array Int Int))
(declare-fun x_3 () Int)
(declare-fun x_4 () Int)
(declare-fun x_5 () Bool)
(declare-fun x_6 () (Array Int Int))
(declare-fun x_7 () (Array Int Int))
(declare-fun x_8 () Int)
(declare-fun x_9 () Bool)
(declare-fun x_10 () Int)
(declare-fun x_11 () Int)
(declare-fun x_12 () Int)
(declare-fun x_13 () Int)
(declare-fun x_14 () (Array Int Int))
(declare-fun x_15 () Int)
(declare-fun x_16 () Int)
(declare-fun x_17 () Int)
(declare-fun x_18 () Int)
(declare-fun x_19 () (Array Int Int))
(declare-fun x_20 () Int)
(declare-fun x_21 () Bool)
(declare-fun x_22 () Int)
(declare-fun x_23 () Int)
(declare-fun x_24 () Int)
(declare-fun x_25 () Int)
(declare-fun x_26 () (Array Int Int))
(declare-fun x_27 () Int)
(declare-fun x_28 () Int)
(declare-fun x_29 () Int)
(declare-fun x_30 () Int)
(declare-fun x_31 () (Array Int Int))
(declare-fun x_32 () Int)
(declare-fun x_33 () Bool)
(declare-fun x_34 () Int)
(declare-fun x_35 () Int)
(declare-fun x_36 () Int)
(declare-fun x_37 () Int)
(declare-fun x_38 () (Array Int Int))
(declare-fun x_39 () Int)
(declare-fun x_40 () Int)
(declare-fun x_41 () Int)
(declare-fun x_42 () Int)
(declare-fun x_43 () (Array Int Int))
(declare-fun x_44 () Int)
(declare-fun x_45 () Bool)
(declare-fun x_46 () Int)
(declare-fun x_47 () Int)
(declare-fun x_48 () Int)
(declare-fun x_49 () Int)
(declare-fun x_50 () (Array Int Int))
(declare-fun x_51 () Int)
(declare-fun x_52 () Int)
(declare-fun x_53 () Int)
(declare-fun x_54 () Int)
(declare-fun x_55 () (Array Int Int))
(declare-fun x_56 () Int)
(declare-fun x_57 () Bool)
(declare-fun x_58 () Int)
(declare-fun x_59 () Int)
(declare-fun x_60 () Int)
(declare-fun x_61 () Int)
(declare-fun x_62 () (Array Int Int))
(declare-fun x_63 () Int)
(declare-fun x_64 () Int)
(declare-fun x_65 () Int)
(declare-fun x_66 () Int)
(declare-fun x_67 () (Array Int Int))
(declare-fun x_68 () Int)
(declare-fun x_69 () Bool)
(declare-fun x_70 () Int)
(declare-fun x_71 () Int)
(declare-fun x_72 () Int)
(declare-fun x_73 () Int)
(declare-fun x_74 () (Array Int Int))
(declare-fun x_75 () Int)
(declare-fun x_76 () Int)
(declare-fun x_77 () Int)
(declare-fun x_78 () Int)
(declare-fun x_79 () (Array Int Int))
(declare-fun x_80 () Int)
(declare-fun x_81 () Bool)
(declare-fun x_82 () Int)
(declare-fun x_83 () Int)
(declare-fun x_84 () Int)
(declare-fun x_85 () Int)
(declare-fun x_86 () (Array Int Int))
(declare-fun x_87 () Int)
(declare-fun x_88 () Int)
(declare-fun x_89 () Int)
(declare-fun x_90 () Int)
(declare-fun x_91 () (Array Int Int))
(declare-fun x_92 () Int)
(declare-fun x_93 () Bool)
(declare-fun x_94 () Int)
(declare-fun x_95 () Int)
(declare-fun x_96 () Int)
(declare-fun x_97 () Int)
(declare-fun x_98 () (Array Int Int))
(declare-fun x_99 () Int)
(declare-fun x_100 () Int)
(declare-fun x_101 () Int)
(declare-fun x_102 () Int)
(declare-fun x_103 () (Array Int Int))
(declare-fun x_104 () Int)
(declare-fun x_105 () Bool)
(declare-fun x_106 () Int)
(declare-fun x_107 () Int)
(declare-fun x_108 () Int)
(declare-fun x_109 () Int)
(declare-fun x_110 () (Array Int Int))
(declare-fun x_111 () Int)
(declare-fun x_112 () Int)
(declare-fun x_113 () Int)
(declare-fun x_114 () Int)
(declare-fun x_115 () (Array Int Int))
(declare-fun x_116 () Int)
(declare-fun x_117 () Bool)
(declare-fun x_118 () Int)
(declare-fun x_119 () Int)
(declare-fun x_120 () Int)
(declare-fun x_121 () Int)
(declare-fun x_122 () (Array Int Int))
(declare-fun x_123 () Int)
(declare-fun x_124 () Int)
(declare-fun x_125 () Int)
(declare-fun x_126 () Int)
(declare-fun x_127 () Int)
(declare-fun x_128 () Int)
(declare-fun x_129 () Int)
(declare-fun x_130 () Int)
(declare-fun x_131 () Int)
(declare-fun x_132 () Int)
(declare-fun x_133 () Int)
(declare-fun x_134 () Int)
(declare-fun x_135 () Int)
(declare-fun x_136 () Int)
(declare-fun x_137 () Int)
(declare-fun x_138 () Int)
(declare-fun x_139 () Int)
(declare-fun x_140 () Int)
(declare-fun x_141 () Int)
(declare-fun x_142 () Int)
(declare-fun x_143 () Int)
(declare-fun x_144 () Int)
(declare-fun x_145 () Int)
(declare-fun x_146 () Int)
(declare-fun x_147 () Int)
(declare-fun x_148 () Int)
(declare-fun x_149 () Int)
(declare-fun x_150 () Int)
(declare-fun x_151 () Int)
(declare-fun x_152 () Int)
(declare-fun x_153 () Int)
(declare-fun x_154 () Int)
(declare-fun x_155 () Int)
(declare-fun x_156 () Int)
(declare-fun x_157 () Int)
(declare-fun x_158 () Int)
(declare-fun x_159 () Int)
(declare-fun x_160 () Int)
(declare-fun x_161 () Int)
(declare-fun x_162 () Int)
(declare-fun x_163 () Int)
(declare-fun x_164 () Int)
(declare-fun x_165 () Int)
(declare-fun x_166 () Int)
(declare-fun x_167 () Int)
(declare-fun x_168 () Int)
(declare-fun x_169 () Int)
(declare-fun x_170 () Int)
(declare-fun x_171 () Int)
(declare-fun x_172 () Int)
(declare-fun x_173 () Int)
(declare-fun x_174 () Int)
(declare-fun x_175 () Int)
(declare-fun x_176 () Int)
(declare-fun x_177 () Int)
(declare-fun x_178 () Int)
(declare-fun x_179 () Int)
(declare-fun x_180 () Int)
(declare-fun x_181 () Int)
(declare-fun x_182 () Int)
(declare-fun x_183 () Int)
(declare-fun x_184 () Int)
(declare-fun x_185 () Int)
(declare-fun x_186 () Int)
(declare-fun x_187 () Int)
(declare-fun x_188 () Int)
(declare-fun x_189 () Int)
(declare-fun x_190 () Int)
(assert (let ((?v_48 (= x_6 x_7)) (?v_45 (= x_8 x_0)) (?v_46 (= x_9 x_5)) (?v_49 (= x_10 x_1)) (?v_47 (not (<= x_1 x_0))) (?v_43 (= x_19 x_6)) (?v_40 (= x_20 x_8)) (?v_41 (= x_21 x_9)) (?v_44 (= x_22 x_10)) (?v_42 (not (<= x_10 x_8))) (?v_38 (= x_31 x_19)) (?v_35 (= x_32 x_20)) (?v_36 (= x_33 x_21)) (?v_39 (= x_34 x_22)) (?v_37 (not (<= x_22 x_20))) (?v_33 (= x_43 x_31)) (?v_30 (= x_44 x_32)) (?v_31 (= x_45 x_33)) (?v_34 (= x_46 x_34)) (?v_32 (not (<= x_34 x_32))) (?v_28 (= x_55 x_43)) (?v_25 (= x_56 x_44)) (?v_26 (= x_57 x_45)) (?v_29 (= x_58 x_46)) (?v_27 (not (<= x_46 x_44))) (?v_23 (= x_67 x_55)) (?v_20 (= x_68 x_56)) (?v_21 (= x_69 x_57)) (?v_24 (= x_70 x_58)) (?v_22 (not (<= x_58 x_56))) (?v_18 (= x_79 x_67)) (?v_15 (= x_80 x_68)) (?v_16 (= x_81 x_69)) (?v_19 (= x_82 x_70)) (?v_17 (not (<= x_70 x_68))) (?v_13 (= x_91 x_79)) (?v_10 (= x_92 x_80)) (?v_11 (= x_93 x_81)) (?v_14 (= x_94 x_82)) (?v_12 (not (<= x_82 x_80))) (?v_8 (= x_103 x_91)) (?v_5 (= x_104 x_92)) (?v_6 (= x_105 x_93)) (?v_9 (= x_106 x_94)) (?v_7 (not (<= x_94 x_92))) (?v_3 (= x_115 x_103)) (?v_0 (= x_116 x_104)) (?v_1 (= x_117 x_105)) (?v_4 (= x_118 x_106)) (?v_2 (not (<= x_106 x_104))) (?v_50 (select x_2 x_3)) (?v_51 (select x_2 x_4))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= x_4 x_3)) (= x_0 0)) (= x_1 0)) (= x_127 ?v_50)) (= x_127 1)) (= x_128 ?v_51)) (= x_128 1)) x_5) (= x_129 (select x_110 x_120))) (= x_130 (select x_110 x_123))) (= x_131 (select x_103 x_104))) (= x_132 (select x_110 x_125))) (or (or (or (and (and (and (and (and (and (and (= x_119 0) (= x_118 (+ x_106 1))) ?v_0) ?v_1) (= x_121 x_120)) (= x_129 1)) (= x_122 (store x_110 x_120 2))) (= x_115 (store x_103 x_106 x_120))) (and (and (and (and (and (and (and (and (and (= x_119 1) ?v_2) ?v_0) ?v_1) ?v_3) ?v_4) (= x_124 x_123)) (= x_130 2)) (= x_131 x_123)) (= x_122 (store x_110 x_123 3)))) (and (and (and (and (and (and (and (and (= x_119 2) ?v_2) (= x_116 (+ x_104 1))) ?v_1) ?v_3) ?v_4) (= x_126 x_125)) (= x_132 3)) (= x_122 (store x_110 x_125 1)))) (and (and (and (and (and (= x_119 3) ?v_3) ?v_0) ?v_1) (= x_122 x_110)) ?v_4))) (= x_133 (select x_98 x_108))) (= x_134 (select x_98 x_111))) (= x_135 (select x_91 x_92))) (= x_136 (select x_98 x_113))) (or (or (or (and (and (and (and (and (and (and (= x_107 0) (= x_106 (+ x_94 1))) ?v_5) ?v_6) (= x_109 x_108)) (= x_133 1)) (= x_110 (store x_98 x_108 2))) (= x_103 (store x_91 x_94 x_108))) (and (and (and (and (and (and (and (and (and (= x_107 1) ?v_7) ?v_5) ?v_6) ?v_8) ?v_9) (= x_112 x_111)) (= x_134 2)) (= x_135 x_111)) (= x_110 (store x_98 x_111 3)))) (and (and (and (and (and (and (and (and (= x_107 2) ?v_7) (= x_104 (+ x_92 1))) ?v_6) ?v_8) ?v_9) (= x_114 x_113)) (= x_136 3)) (= x_110 (store x_98 x_113 1)))) (and (and (and (and (and (= x_107 3) ?v_8) ?v_5) ?v_6) (= x_110 x_98)) ?v_9))) (= x_137 (select x_86 x_96))) (= x_138 (select x_86 x_99))) (= x_139 (select x_79 x_80))) (= x_140 (select x_86 x_101))) (or (or (or (and (and (and (and (and (and (and (= x_95 0) (= x_94 (+ x_82 1))) ?v_10) ?v_11) (= x_97 x_96)) (= x_137 1)) (= x_98 (store x_86 x_96 2))) (= x_91 (store x_79 x_82 x_96))) (and (and (and (and (and (and (and (and (and (= x_95 1) ?v_12) ?v_10) ?v_11) ?v_13) ?v_14) (= x_100 x_99)) (= x_138 2)) (= x_139 x_99)) (= x_98 (store x_86 x_99 3)))) (and (and (and (and (and (and (and (and (= x_95 2) ?v_12) (= x_92 (+ x_80 1))) ?v_11) ?v_13) ?v_14) (= x_102 x_101)) (= x_140 3)) (= x_98 (store x_86 x_101 1)))) (and (and (and (and (and (= x_95 3) ?v_13) ?v_10) ?v_11) (= x_98 x_86)) ?v_14))) (= x_141 (select x_74 x_84))) (= x_142 (select x_74 x_87))) (= x_143 (select x_67 x_68))) (= x_144 (select x_74 x_89))) (or (or (or (and (and (and (and (and (and (and (= x_83 0) (= x_82 (+ x_70 1))) ?v_15) ?v_16) (= x_85 x_84)) (= x_141 1)) (= x_86 (store x_74 x_84 2))) (= x_79 (store x_67 x_70 x_84))) (and (and (and (and (and (and (and (and (and (= x_83 1) ?v_17) ?v_15) ?v_16) ?v_18) ?v_19) (= x_88 x_87)) (= x_142 2)) (= x_143 x_87)) (= x_86 (store x_74 x_87 3)))) (and (and (and (and (and (and (and (and (= x_83 2) ?v_17) (= x_80 (+ x_68 1))) ?v_16) ?v_18) ?v_19) (= x_90 x_89)) (= x_144 3)) (= x_86 (store x_74 x_89 1)))) (and (and (and (and (and (= x_83 3) ?v_18) ?v_15) ?v_16) (= x_86 x_74)) ?v_19))) (= x_145 (select x_62 x_72))) (= x_146 (select x_62 x_75))) (= x_147 (select x_55 x_56))) (= x_148 (select x_62 x_77))) (or (or (or (and (and (and (and (and (and (and (= x_71 0) (= x_70 (+ x_58 1))) ?v_20) ?v_21) (= x_73 x_72)) (= x_145 1)) (= x_74 (store x_62 x_72 2))) (= x_67 (store x_55 x_58 x_72))) (and (and (and (and (and (and (and (and (and (= x_71 1) ?v_22) ?v_20) ?v_21) ?v_23) ?v_24) (= x_76 x_75)) (= x_146 2)) (= x_147 x_75)) (= x_74 (store x_62 x_75 3)))) (and (and (and (and (and (and (and (and (= x_71 2) ?v_22) (= x_68 (+ x_56 1))) ?v_21) ?v_23) ?v_24) (= x_78 x_77)) (= x_148 3)) (= x_74 (store x_62 x_77 1)))) (and (and (and (and (and (= x_71 3) ?v_23) ?v_20) ?v_21) (= x_74 x_62)) ?v_24))) (= x_149 (select x_50 x_60))) (= x_150 (select x_50 x_63))) (= x_151 (select x_43 x_44))) (= x_152 (select x_50 x_65))) (or (or (or (and (and (and (and (and (and (and (= x_59 0) (= x_58 (+ x_46 1))) ?v_25) ?v_26) (= x_61 x_60)) (= x_149 1)) (= x_62 (store x_50 x_60 2))) (= x_55 (store x_43 x_46 x_60))) (and (and (and (and (and (and (and (and (and (= x_59 1) ?v_27) ?v_25) ?v_26) ?v_28) ?v_29) (= x_64 x_63)) (= x_150 2)) (= x_151 x_63)) (= x_62 (store x_50 x_63 3)))) (and (and (and (and (and (and (and (and (= x_59 2) ?v_27) (= x_56 (+ x_44 1))) ?v_26) ?v_28) ?v_29) (= x_66 x_65)) (= x_152 3)) (= x_62 (store x_50 x_65 1)))) (and (and (and (and (and (= x_59 3) ?v_28) ?v_25) ?v_26) (= x_62 x_50)) ?v_29))) (= x_153 (select x_38 x_48))) (= x_154 (select x_38 x_51))) (= x_155 (select x_31 x_32))) (= x_156 (select x_38 x_53))) (or (or (or (and (and (and (and (and (and (and (= x_47 0) (= x_46 (+ x_34 1))) ?v_30) ?v_31) (= x_49 x_48)) (= x_153 1)) (= x_50 (store x_38 x_48 2))) (= x_43 (store x_31 x_34 x_48))) (and (and (and (and (and (and (and (and (and (= x_47 1) ?v_32) ?v_30) ?v_31) ?v_33) ?v_34) (= x_52 x_51)) (= x_154 2)) (= x_155 x_51)) (= x_50 (store x_38 x_51 3)))) (and (and (and (and (and (and (and (and (= x_47 2) ?v_32) (= x_44 (+ x_32 1))) ?v_31) ?v_33) ?v_34) (= x_54 x_53)) (= x_156 3)) (= x_50 (store x_38 x_53 1)))) (and (and (and (and (and (= x_47 3) ?v_33) ?v_30) ?v_31) (= x_50 x_38)) ?v_34))) (= x_157 (select x_26 x_36))) (= x_158 (select x_26 x_39))) (= x_159 (select x_19 x_20))) (= x_160 (select x_26 x_41))) (or (or (or (and (and (and (and (and (and (and (= x_35 0) (= x_34 (+ x_22 1))) ?v_35) ?v_36) (= x_37 x_36)) (= x_157 1)) (= x_38 (store x_26 x_36 2))) (= x_31 (store x_19 x_22 x_36))) (and (and (and (and (and (and (and (and (and (= x_35 1) ?v_37) ?v_35) ?v_36) ?v_38) ?v_39) (= x_40 x_39)) (= x_158 2)) (= x_159 x_39)) (= x_38 (store x_26 x_39 3)))) (and (and (and (and (and (and (and (and (= x_35 2) ?v_37) (= x_32 (+ x_20 1))) ?v_36) ?v_38) ?v_39) (= x_42 x_41)) (= x_160 3)) (= x_38 (store x_26 x_41 1)))) (and (and (and (and (and (= x_35 3) ?v_38) ?v_35) ?v_36) (= x_38 x_26)) ?v_39))) (= x_161 (select x_14 x_24))) (= x_162 (select x_14 x_27))) (= x_163 (select x_6 x_8))) (= x_164 (select x_14 x_29))) (or (or (or (and (and (and (and (and (and (and (= x_23 0) (= x_22 (+ x_10 1))) ?v_40) ?v_41) (= x_25 x_24)) (= x_161 1)) (= x_26 (store x_14 x_24 2))) (= x_19 (store x_6 x_10 x_24))) (and (and (and (and (and (and (and (and (and (= x_23 1) ?v_42) ?v_40) ?v_41) ?v_43) ?v_44) (= x_28 x_27)) (= x_162 2)) (= x_163 x_27)) (= x_26 (store x_14 x_27 3)))) (and (and (and (and (and (and (and (and (= x_23 2) ?v_42) (= x_20 (+ x_8 1))) ?v_41) ?v_43) ?v_44) (= x_30 x_29)) (= x_164 3)) (= x_26 (store x_14 x_29 1)))) (and (and (and (and (and (= x_23 3) ?v_43) ?v_40) ?v_41) (= x_26 x_14)) ?v_44))) (= x_165 (select x_2 x_12))) (= x_166 (select x_2 x_15))) (= x_167 (select x_7 x_0))) (= x_168 (select x_2 x_17))) (or (or (or (and (and (and (and (and (and (and (= x_11 0) (= x_10 (+ x_1 1))) ?v_45) ?v_46) (= x_13 x_12)) (= x_165 1)) (= x_14 (store x_2 x_12 2))) (= x_6 (store x_7 x_1 x_12))) (and (and (and (and (and (and (and (and (and (= x_11 1) ?v_47) ?v_45) ?v_46) ?v_48) ?v_49) (= x_16 x_15)) (= x_166 2)) (= x_167 x_15)) (= x_14 (store x_2 x_15 3)))) (and (and (and (and (and (and (and (and (= x_11 2) ?v_47) (= x_8 (+ x_0 1))) ?v_46) ?v_48) ?v_49) (= x_18 x_17)) (= x_168 3)) (= x_14 (store x_2 x_17 1)))) (and (and (and (and (and (= x_11 3) ?v_48) ?v_45) ?v_46) (= x_14 x_2)) ?v_49))) (= x_169 (select x_122 x_3))) (= x_170 (select x_122 x_4))) (= x_171 (select x_110 x_3))) (= x_172 (select x_110 x_4))) (= x_173 (select x_98 x_3))) (= x_174 (select x_98 x_4))) (= x_175 (select x_86 x_3))) (= x_176 (select x_86 x_4))) (= x_177 (select x_74 x_3))) (= x_178 (select x_74 x_4))) (= x_179 (select x_62 x_3))) (= x_180 (select x_62 x_4))) (= x_181 (select x_50 x_3))) (= x_182 (select x_50 x_4))) (= x_183 (select x_38 x_3))) (= x_184 (select x_38 x_4))) (= x_185 (select x_26 x_3))) (= x_186 (select x_26 x_4))) (= x_187 (select x_14 x_3))) (= x_188 (select x_14 x_4))) (= x_189 ?v_50)) (= x_190 ?v_51)) (or (or (or (or (or (or (or (or (or (or (and (= x_169 3) (= x_170 3)) (and (= x_171 3) (= x_172 3))) (and (= x_173 3) (= x_174 3))) (and (= x_175 3) (= x_176 3))) (and (= x_177 3) (= x_178 3))) (and (= x_179 3) (= x_180 3))) (and (= x_181 3) (= x_182 3))) (and (= x_183 3) (= x_184 3))) (and (= x_185 3) (= x_186 3))) (and (= x_187 3) (= x_188 3))) (and (= x_189 3) (= x_190 3))))))
(check-sat)
(exit)
