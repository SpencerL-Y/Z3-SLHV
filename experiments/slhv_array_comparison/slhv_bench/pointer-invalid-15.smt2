(set-info :smt-lib-version 2.6)
(set-logic SLHV)
(set-info :source |
Benchmarks from Leonardo de Moura <demoura@csl.sri.com>

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x_0 () Int)
(declare-fun x_1 () Int)
(declare-fun x_2 () Int)
(declare-fun x_3 () Int)
(declare-fun x_4 () (Array Int Int))
(declare-fun x_5 () Int)
(declare-fun x_6 () Int)
(declare-fun x_7 () Int)
(declare-fun x_8 () Int)
(declare-fun x_9 () Int)
(declare-fun x_10 () (Array Int Int))
(declare-fun x_11 () (Array Int Int))
(declare-fun x_12 () Int)
(declare-fun x_13 () Int)
(declare-fun x_14 () Int)
(declare-fun x_15 () Int)
(declare-fun x_16 () (Array Int Int))
(declare-fun x_17 () Int)
(declare-fun x_18 () Int)
(declare-fun x_19 () Int)
(declare-fun x_20 () Int)
(declare-fun x_21 () Int)
(declare-fun x_22 () Int)
(declare-fun x_23 () Int)
(declare-fun x_24 () (Array Int Int))
(declare-fun x_25 () Int)
(declare-fun x_26 () Int)
(declare-fun x_27 () Int)
(declare-fun x_28 () (Array Int Int))
(declare-fun x_29 () Int)
(declare-fun x_30 () Int)
(declare-fun x_31 () Int)
(declare-fun x_32 () Int)
(declare-fun x_33 () Int)
(declare-fun x_34 () Int)
(declare-fun x_35 () (Array Int Int))
(declare-fun x_36 () Int)
(declare-fun x_37 () Int)
(declare-fun x_38 () Int)
(declare-fun x_39 () (Array Int Int))
(declare-fun x_40 () Int)
(declare-fun x_41 () Int)
(declare-fun x_42 () Int)
(declare-fun x_43 () Int)
(declare-fun x_44 () Int)
(declare-fun x_45 () Int)
(declare-fun x_46 () (Array Int Int))
(declare-fun x_47 () Int)
(declare-fun x_48 () Int)
(declare-fun x_49 () Int)
(declare-fun x_50 () (Array Int Int))
(declare-fun x_51 () Int)
(declare-fun x_52 () Int)
(declare-fun x_53 () Int)
(declare-fun x_54 () Int)
(declare-fun x_55 () Int)
(declare-fun x_56 () Int)
(declare-fun x_57 () (Array Int Int))
(declare-fun x_58 () Int)
(declare-fun x_59 () Int)
(declare-fun x_60 () Int)
(declare-fun x_61 () (Array Int Int))
(declare-fun x_62 () Int)
(declare-fun x_63 () Int)
(declare-fun x_64 () Int)
(declare-fun x_65 () Int)
(declare-fun x_66 () Int)
(declare-fun x_67 () Int)
(declare-fun x_68 () (Array Int Int))
(declare-fun x_69 () Int)
(declare-fun x_70 () Int)
(declare-fun x_71 () Int)
(declare-fun x_72 () (Array Int Int))
(declare-fun x_73 () Int)
(declare-fun x_74 () Int)
(declare-fun x_75 () Int)
(declare-fun x_76 () Int)
(declare-fun x_77 () Int)
(declare-fun x_78 () Int)
(declare-fun x_79 () (Array Int Int))
(declare-fun x_80 () Int)
(declare-fun x_81 () Int)
(declare-fun x_82 () Int)
(declare-fun x_83 () (Array Int Int))
(declare-fun x_84 () Int)
(declare-fun x_85 () Int)
(declare-fun x_86 () Int)
(declare-fun x_87 () Int)
(declare-fun x_88 () Int)
(declare-fun x_89 () Int)
(declare-fun x_90 () (Array Int Int))
(declare-fun x_91 () Int)
(declare-fun x_92 () Int)
(declare-fun x_93 () Int)
(declare-fun x_94 () (Array Int Int))
(declare-fun x_95 () Int)
(declare-fun x_96 () Int)
(declare-fun x_97 () Int)
(declare-fun x_98 () Int)
(declare-fun x_99 () Int)
(declare-fun x_100 () Int)
(declare-fun x_101 () (Array Int Int))
(declare-fun x_102 () Int)
(declare-fun x_103 () Int)
(declare-fun x_104 () Int)
(declare-fun x_105 () (Array Int Int))
(declare-fun x_106 () Int)
(declare-fun x_107 () Int)
(declare-fun x_108 () Int)
(declare-fun x_109 () Int)
(declare-fun x_110 () Int)
(declare-fun x_111 () Int)
(declare-fun x_112 () (Array Int Int))
(declare-fun x_113 () Int)
(declare-fun x_114 () Int)
(declare-fun x_115 () Int)
(declare-fun x_116 () (Array Int Int))
(declare-fun x_117 () Int)
(declare-fun x_118 () Int)
(declare-fun x_119 () Int)
(declare-fun x_120 () Int)
(declare-fun x_121 () Int)
(declare-fun x_122 () Int)
(declare-fun x_123 () (Array Int Int))
(declare-fun x_124 () Int)
(declare-fun x_125 () Int)
(declare-fun x_126 () Int)
(declare-fun x_127 () (Array Int Int))
(declare-fun x_128 () Int)
(declare-fun x_129 () Int)
(declare-fun x_130 () Int)
(declare-fun x_131 () Int)
(declare-fun x_132 () Int)
(declare-fun x_133 () Int)
(declare-fun x_134 () (Array Int Int))
(declare-fun x_135 () Int)
(declare-fun x_136 () Int)
(declare-fun x_137 () Int)
(declare-fun x_138 () (Array Int Int))
(declare-fun x_139 () Int)
(declare-fun x_140 () Int)
(declare-fun x_141 () Int)
(declare-fun x_142 () Int)
(declare-fun x_143 () Int)
(declare-fun x_144 () Int)
(declare-fun x_145 () (Array Int Int))
(declare-fun x_146 () Int)
(declare-fun x_147 () Int)
(declare-fun x_148 () Int)
(declare-fun x_149 () (Array Int Int))
(declare-fun x_150 () Int)
(declare-fun x_151 () Int)
(declare-fun x_152 () Int)
(declare-fun x_153 () Int)
(declare-fun x_154 () Int)
(declare-fun x_155 () Int)
(declare-fun x_156 () (Array Int Int))
(declare-fun x_157 () Int)
(declare-fun x_158 () Int)
(declare-fun x_159 () Int)
(declare-fun x_160 () (Array Int Int))
(declare-fun x_161 () Int)
(declare-fun x_162 () Int)
(declare-fun x_163 () Int)
(declare-fun x_164 () Int)
(declare-fun x_165 () Int)
(declare-fun x_166 () Int)
(declare-fun x_167 () (Array Int Int))
(declare-fun x_168 () Int)
(declare-fun x_169 () Int)
(declare-fun x_170 () Int)
(declare-fun x_171 () (Array Int Int))
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
(assert (let ((?v_115 (= x_6 (+ x_0 1))) (?v_121 (= x_9 x_2)) (?v_117 (= x_10 x_11)) (?v_116 (= x_12 x_13)) (?v_118 (= x_14 x_1)) (?v_119 (= x_15 x_3)) (?v_122 (= x_16 x_4)) (?v_120 (= x_17 x_18)) (?v_106 (= x_21 (+ x_6 1))) (?v_112 (= x_23 x_9)) (?v_108 (= x_24 x_10)) (?v_107 (= x_25 x_12)) (?v_109 (= x_26 x_14)) (?v_110 (= x_27 x_15)) (?v_113 (= x_28 x_16)) (?v_111 (= x_29 x_17)) (?v_98 (= x_32 (+ x_21 1))) (?v_104 (= x_34 x_23)) (?v_100 (= x_35 x_24)) (?v_99 (= x_36 x_25)) (?v_101 (= x_37 x_26)) (?v_102 (= x_38 x_27)) (?v_105 (= x_39 x_28)) (?v_103 (= x_40 x_29)) (?v_90 (= x_43 (+ x_32 1))) (?v_96 (= x_45 x_34)) (?v_92 (= x_46 x_35)) (?v_91 (= x_47 x_36)) (?v_93 (= x_48 x_37)) (?v_94 (= x_49 x_38)) (?v_97 (= x_50 x_39)) (?v_95 (= x_51 x_40)) (?v_82 (= x_54 (+ x_43 1))) (?v_88 (= x_56 x_45)) (?v_84 (= x_57 x_46)) (?v_83 (= x_58 x_47)) (?v_85 (= x_59 x_48)) (?v_86 (= x_60 x_49)) (?v_89 (= x_61 x_50)) (?v_87 (= x_62 x_51)) (?v_74 (= x_65 (+ x_54 1))) (?v_80 (= x_67 x_56)) (?v_76 (= x_68 x_57)) (?v_75 (= x_69 x_58)) (?v_77 (= x_70 x_59)) (?v_78 (= x_71 x_60)) (?v_81 (= x_72 x_61)) (?v_79 (= x_73 x_62)) (?v_66 (= x_76 (+ x_65 1))) (?v_72 (= x_78 x_67)) (?v_68 (= x_79 x_68)) (?v_67 (= x_80 x_69)) (?v_69 (= x_81 x_70)) (?v_70 (= x_82 x_71)) (?v_73 (= x_83 x_72)) (?v_71 (= x_84 x_73)) (?v_58 (= x_87 (+ x_76 1))) (?v_64 (= x_89 x_78)) (?v_60 (= x_90 x_79)) (?v_59 (= x_91 x_80)) (?v_61 (= x_92 x_81)) (?v_62 (= x_93 x_82)) (?v_65 (= x_94 x_83)) (?v_63 (= x_95 x_84)) (?v_50 (= x_98 (+ x_87 1))) (?v_56 (= x_100 x_89)) (?v_52 (= x_101 x_90)) (?v_51 (= x_102 x_91)) (?v_53 (= x_103 x_92)) (?v_54 (= x_104 x_93)) (?v_57 (= x_105 x_94)) (?v_55 (= x_106 x_95)) (?v_42 (= x_109 (+ x_98 1))) (?v_48 (= x_111 x_100)) (?v_44 (= x_112 x_101)) (?v_43 (= x_113 x_102)) (?v_45 (= x_114 x_103)) (?v_46 (= x_115 x_104)) (?v_49 (= x_116 x_105)) (?v_47 (= x_117 x_106)) (?v_34 (= x_120 (+ x_109 1))) (?v_40 (= x_122 x_111)) (?v_36 (= x_123 x_112)) (?v_35 (= x_124 x_113)) (?v_37 (= x_125 x_114)) (?v_38 (= x_126 x_115)) (?v_41 (= x_127 x_116)) (?v_39 (= x_128 x_117)) (?v_26 (= x_131 (+ x_120 1))) (?v_32 (= x_133 x_122)) (?v_28 (= x_134 x_123)) (?v_27 (= x_135 x_124)) (?v_29 (= x_136 x_125)) (?v_30 (= x_137 x_126)) (?v_33 (= x_138 x_127)) (?v_31 (= x_139 x_128)) (?v_18 (= x_142 (+ x_131 1))) (?v_24 (= x_144 x_133)) (?v_20 (= x_145 x_134)) (?v_19 (= x_146 x_135)) (?v_21 (= x_147 x_136)) (?v_22 (= x_148 x_137)) (?v_25 (= x_149 x_138)) (?v_23 (= x_150 x_139)) (?v_9 (= x_153 (+ x_142 1))) (?v_16 (= x_155 x_144)) (?v_12 (= x_156 x_145)) (?v_10 (= x_157 x_146)) (?v_13 (= x_158 x_147)) (?v_14 (= x_159 x_148)) (?v_17 (= x_160 x_149)) (?v_15 (= x_161 x_150)) (?v_1 (= x_164 (+ x_153 1))) (?v_7 (= x_166 x_155)) (?v_3 (= x_167 x_156)) (?v_2 (= x_168 x_157)) (?v_4 (= x_169 x_158)) (?v_5 (= x_170 x_159)) (?v_8 (= x_171 x_160)) (?v_6 (= x_172 x_161)) (?v_0 (+ x_7 2)) (?v_11 (+ x_7 1)) (?v_114 (= x_2 (- 1))) (?v_123 (= x_155 (- 1))) (?v_124 (= x_144 (- 1))) (?v_125 (= x_133 (- 1))) (?v_126 (= x_122 (- 1))) (?v_127 (= x_111 (- 1))) (?v_128 (= x_100 (- 1))) (?v_129 (= x_89 (- 1))) (?v_130 (= x_78 (- 1))) (?v_131 (= x_67 (- 1))) (?v_132 (= x_56 (- 1))) (?v_133 (= x_45 (- 1))) (?v_134 (= x_34 (- 1))) (?v_135 (= x_23 (- 1))) (?v_136 (= x_9 (- 1)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (<= x_7 0)) (= x_0 0)) (= x_1 0)) ?v_114) (= x_3 0)) (= x_174 (select x_4 x_2))) (= x_5 x_174)) (= x_8 ?v_0)) (= x_175 (select x_16 x_9))) (= x_20 x_175)) (= x_22 ?v_0)) (= x_176 (select x_28 x_23))) (= x_31 x_176)) (= x_33 ?v_0)) (= x_177 (select x_39 x_34))) (= x_42 x_177)) (= x_44 ?v_0)) (= x_178 (select x_50 x_45))) (= x_53 x_178)) (= x_55 ?v_0)) (= x_179 (select x_61 x_56))) (= x_64 x_179)) (= x_66 ?v_0)) (= x_180 (select x_72 x_67))) (= x_75 x_180)) (= x_77 ?v_0)) (= x_181 (select x_83 x_78))) (= x_86 x_181)) (= x_88 ?v_0)) (= x_182 (select x_94 x_89))) (= x_97 x_182)) (= x_99 ?v_0)) (= x_183 (select x_105 x_100))) (= x_108 x_183)) (= x_110 ?v_0)) (= x_184 (select x_116 x_111))) (= x_119 x_184)) (= x_121 ?v_0)) (= x_185 (select x_127 x_122))) (= x_130 x_185)) (= x_132 ?v_0)) (= x_186 (select x_138 x_133))) (= x_141 x_186)) (= x_143 ?v_0)) (= x_187 (select x_149 x_144))) (= x_152 x_187)) (= x_154 ?v_0)) (= x_188 (select x_160 x_155))) (= x_163 x_188)) (= x_165 ?v_0)) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_173 0) (< x_153 x_7)) ?v_1) (= x_170 (+ x_159 1))) (= x_166 x_158)) (= x_169 (+ x_158 1))) (= x_167 (store x_156 x_158 x_153))) ?v_2) (= x_171 (store x_160 x_158 x_155))) ?v_6) (and (and (and (and (and (and (and (and (and (and (= x_173 1) (= x_153 x_7)) (not ?v_123)) (= x_172 x_155)) (= x_166 x_163)) ?v_1) ?v_3) ?v_2) ?v_4) ?v_5) ?v_8)) (and (and (and (and (and (and (and (and (and (= x_173 2) (= x_153 ?v_11)) ?v_1) ?v_7) ?v_3) ?v_2) ?v_4) ?v_5) (= x_171 (store x_160 x_161 x_163))) ?v_6)) (and (and (and (and (and (and (and (and (and (= x_173 3) (= x_153 x_165)) ?v_1) ?v_7) ?v_3) ?v_2) ?v_4) ?v_5) (= x_171 (store x_160 x_155 x_161))) ?v_6)) (and (and (and (and (and (and (and (and (and (= x_173 4) (not (<= x_153 x_165))) ?v_7) ?v_3) ?v_2) ?v_4) ?v_5) ?v_8) ?v_6) (= x_164 x_153)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_162 0) (< x_142 x_7)) ?v_9) (= x_159 (+ x_148 1))) (= x_155 x_147)) (= x_158 (+ x_147 1))) (= x_156 (store x_145 x_147 x_142))) ?v_10) (= x_160 (store x_149 x_147 x_144))) ?v_15) (and (and (and (and (and (and (and (and (and (and (= x_162 1) (= x_142 x_7)) (not ?v_124)) (= x_161 x_144)) (= x_155 x_152)) ?v_9) ?v_12) ?v_10) ?v_13) ?v_14) ?v_17)) (and (and (and (and (and (and (and (and (and (= x_162 2) (= x_142 ?v_11)) ?v_9) ?v_16) ?v_12) ?v_10) ?v_13) ?v_14) (= x_160 (store x_149 x_150 x_152))) ?v_15)) (and (and (and (and (and (and (and (and (and (= x_162 3) (= x_142 x_154)) ?v_9) ?v_16) ?v_12) ?v_10) ?v_13) ?v_14) (= x_160 (store x_149 x_144 x_150))) ?v_15)) (and (and (and (and (and (and (and (and (and (= x_162 4) (not (<= x_142 x_154))) ?v_16) ?v_12) ?v_10) ?v_13) ?v_14) ?v_17) ?v_15) (= x_153 x_142)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_151 0) (< x_131 x_7)) ?v_18) (= x_148 (+ x_137 1))) (= x_144 x_136)) (= x_147 (+ x_136 1))) (= x_145 (store x_134 x_136 x_131))) ?v_19) (= x_149 (store x_138 x_136 x_133))) ?v_23) (and (and (and (and (and (and (and (and (and (and (= x_151 1) (= x_131 x_7)) (not ?v_125)) (= x_150 x_133)) (= x_144 x_141)) ?v_18) ?v_20) ?v_19) ?v_21) ?v_22) ?v_25)) (and (and (and (and (and (and (and (and (and (= x_151 2) (= x_131 ?v_11)) ?v_18) ?v_24) ?v_20) ?v_19) ?v_21) ?v_22) (= x_149 (store x_138 x_139 x_141))) ?v_23)) (and (and (and (and (and (and (and (and (and (= x_151 3) (= x_131 x_143)) ?v_18) ?v_24) ?v_20) ?v_19) ?v_21) ?v_22) (= x_149 (store x_138 x_133 x_139))) ?v_23)) (and (and (and (and (and (and (and (and (and (= x_151 4) (not (<= x_131 x_143))) ?v_24) ?v_20) ?v_19) ?v_21) ?v_22) ?v_25) ?v_23) (= x_142 x_131)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_140 0) (< x_120 x_7)) ?v_26) (= x_137 (+ x_126 1))) (= x_133 x_125)) (= x_136 (+ x_125 1))) (= x_134 (store x_123 x_125 x_120))) ?v_27) (= x_138 (store x_127 x_125 x_122))) ?v_31) (and (and (and (and (and (and (and (and (and (and (= x_140 1) (= x_120 x_7)) (not ?v_126)) (= x_139 x_122)) (= x_133 x_130)) ?v_26) ?v_28) ?v_27) ?v_29) ?v_30) ?v_33)) (and (and (and (and (and (and (and (and (and (= x_140 2) (= x_120 ?v_11)) ?v_26) ?v_32) ?v_28) ?v_27) ?v_29) ?v_30) (= x_138 (store x_127 x_128 x_130))) ?v_31)) (and (and (and (and (and (and (and (and (and (= x_140 3) (= x_120 x_132)) ?v_26) ?v_32) ?v_28) ?v_27) ?v_29) ?v_30) (= x_138 (store x_127 x_122 x_128))) ?v_31)) (and (and (and (and (and (and (and (and (and (= x_140 4) (not (<= x_120 x_132))) ?v_32) ?v_28) ?v_27) ?v_29) ?v_30) ?v_33) ?v_31) (= x_131 x_120)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_129 0) (< x_109 x_7)) ?v_34) (= x_126 (+ x_115 1))) (= x_122 x_114)) (= x_125 (+ x_114 1))) (= x_123 (store x_112 x_114 x_109))) ?v_35) (= x_127 (store x_116 x_114 x_111))) ?v_39) (and (and (and (and (and (and (and (and (and (and (= x_129 1) (= x_109 x_7)) (not ?v_127)) (= x_128 x_111)) (= x_122 x_119)) ?v_34) ?v_36) ?v_35) ?v_37) ?v_38) ?v_41)) (and (and (and (and (and (and (and (and (and (= x_129 2) (= x_109 ?v_11)) ?v_34) ?v_40) ?v_36) ?v_35) ?v_37) ?v_38) (= x_127 (store x_116 x_117 x_119))) ?v_39)) (and (and (and (and (and (and (and (and (and (= x_129 3) (= x_109 x_121)) ?v_34) ?v_40) ?v_36) ?v_35) ?v_37) ?v_38) (= x_127 (store x_116 x_111 x_117))) ?v_39)) (and (and (and (and (and (and (and (and (and (= x_129 4) (not (<= x_109 x_121))) ?v_40) ?v_36) ?v_35) ?v_37) ?v_38) ?v_41) ?v_39) (= x_120 x_109)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_118 0) (< x_98 x_7)) ?v_42) (= x_115 (+ x_104 1))) (= x_111 x_103)) (= x_114 (+ x_103 1))) (= x_112 (store x_101 x_103 x_98))) ?v_43) (= x_116 (store x_105 x_103 x_100))) ?v_47) (and (and (and (and (and (and (and (and (and (and (= x_118 1) (= x_98 x_7)) (not ?v_128)) (= x_117 x_100)) (= x_111 x_108)) ?v_42) ?v_44) ?v_43) ?v_45) ?v_46) ?v_49)) (and (and (and (and (and (and (and (and (and (= x_118 2) (= x_98 ?v_11)) ?v_42) ?v_48) ?v_44) ?v_43) ?v_45) ?v_46) (= x_116 (store x_105 x_106 x_108))) ?v_47)) (and (and (and (and (and (and (and (and (and (= x_118 3) (= x_98 x_110)) ?v_42) ?v_48) ?v_44) ?v_43) ?v_45) ?v_46) (= x_116 (store x_105 x_100 x_106))) ?v_47)) (and (and (and (and (and (and (and (and (and (= x_118 4) (not (<= x_98 x_110))) ?v_48) ?v_44) ?v_43) ?v_45) ?v_46) ?v_49) ?v_47) (= x_109 x_98)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_107 0) (< x_87 x_7)) ?v_50) (= x_104 (+ x_93 1))) (= x_100 x_92)) (= x_103 (+ x_92 1))) (= x_101 (store x_90 x_92 x_87))) ?v_51) (= x_105 (store x_94 x_92 x_89))) ?v_55) (and (and (and (and (and (and (and (and (and (and (= x_107 1) (= x_87 x_7)) (not ?v_129)) (= x_106 x_89)) (= x_100 x_97)) ?v_50) ?v_52) ?v_51) ?v_53) ?v_54) ?v_57)) (and (and (and (and (and (and (and (and (and (= x_107 2) (= x_87 ?v_11)) ?v_50) ?v_56) ?v_52) ?v_51) ?v_53) ?v_54) (= x_105 (store x_94 x_95 x_97))) ?v_55)) (and (and (and (and (and (and (and (and (and (= x_107 3) (= x_87 x_99)) ?v_50) ?v_56) ?v_52) ?v_51) ?v_53) ?v_54) (= x_105 (store x_94 x_89 x_95))) ?v_55)) (and (and (and (and (and (and (and (and (and (= x_107 4) (not (<= x_87 x_99))) ?v_56) ?v_52) ?v_51) ?v_53) ?v_54) ?v_57) ?v_55) (= x_98 x_87)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_96 0) (< x_76 x_7)) ?v_58) (= x_93 (+ x_82 1))) (= x_89 x_81)) (= x_92 (+ x_81 1))) (= x_90 (store x_79 x_81 x_76))) ?v_59) (= x_94 (store x_83 x_81 x_78))) ?v_63) (and (and (and (and (and (and (and (and (and (and (= x_96 1) (= x_76 x_7)) (not ?v_130)) (= x_95 x_78)) (= x_89 x_86)) ?v_58) ?v_60) ?v_59) ?v_61) ?v_62) ?v_65)) (and (and (and (and (and (and (and (and (and (= x_96 2) (= x_76 ?v_11)) ?v_58) ?v_64) ?v_60) ?v_59) ?v_61) ?v_62) (= x_94 (store x_83 x_84 x_86))) ?v_63)) (and (and (and (and (and (and (and (and (and (= x_96 3) (= x_76 x_88)) ?v_58) ?v_64) ?v_60) ?v_59) ?v_61) ?v_62) (= x_94 (store x_83 x_78 x_84))) ?v_63)) (and (and (and (and (and (and (and (and (and (= x_96 4) (not (<= x_76 x_88))) ?v_64) ?v_60) ?v_59) ?v_61) ?v_62) ?v_65) ?v_63) (= x_87 x_76)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_85 0) (< x_65 x_7)) ?v_66) (= x_82 (+ x_71 1))) (= x_78 x_70)) (= x_81 (+ x_70 1))) (= x_79 (store x_68 x_70 x_65))) ?v_67) (= x_83 (store x_72 x_70 x_67))) ?v_71) (and (and (and (and (and (and (and (and (and (and (= x_85 1) (= x_65 x_7)) (not ?v_131)) (= x_84 x_67)) (= x_78 x_75)) ?v_66) ?v_68) ?v_67) ?v_69) ?v_70) ?v_73)) (and (and (and (and (and (and (and (and (and (= x_85 2) (= x_65 ?v_11)) ?v_66) ?v_72) ?v_68) ?v_67) ?v_69) ?v_70) (= x_83 (store x_72 x_73 x_75))) ?v_71)) (and (and (and (and (and (and (and (and (and (= x_85 3) (= x_65 x_77)) ?v_66) ?v_72) ?v_68) ?v_67) ?v_69) ?v_70) (= x_83 (store x_72 x_67 x_73))) ?v_71)) (and (and (and (and (and (and (and (and (and (= x_85 4) (not (<= x_65 x_77))) ?v_72) ?v_68) ?v_67) ?v_69) ?v_70) ?v_73) ?v_71) (= x_76 x_65)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_74 0) (< x_54 x_7)) ?v_74) (= x_71 (+ x_60 1))) (= x_67 x_59)) (= x_70 (+ x_59 1))) (= x_68 (store x_57 x_59 x_54))) ?v_75) (= x_72 (store x_61 x_59 x_56))) ?v_79) (and (and (and (and (and (and (and (and (and (and (= x_74 1) (= x_54 x_7)) (not ?v_132)) (= x_73 x_56)) (= x_67 x_64)) ?v_74) ?v_76) ?v_75) ?v_77) ?v_78) ?v_81)) (and (and (and (and (and (and (and (and (and (= x_74 2) (= x_54 ?v_11)) ?v_74) ?v_80) ?v_76) ?v_75) ?v_77) ?v_78) (= x_72 (store x_61 x_62 x_64))) ?v_79)) (and (and (and (and (and (and (and (and (and (= x_74 3) (= x_54 x_66)) ?v_74) ?v_80) ?v_76) ?v_75) ?v_77) ?v_78) (= x_72 (store x_61 x_56 x_62))) ?v_79)) (and (and (and (and (and (and (and (and (and (= x_74 4) (not (<= x_54 x_66))) ?v_80) ?v_76) ?v_75) ?v_77) ?v_78) ?v_81) ?v_79) (= x_65 x_54)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_63 0) (< x_43 x_7)) ?v_82) (= x_60 (+ x_49 1))) (= x_56 x_48)) (= x_59 (+ x_48 1))) (= x_57 (store x_46 x_48 x_43))) ?v_83) (= x_61 (store x_50 x_48 x_45))) ?v_87) (and (and (and (and (and (and (and (and (and (and (= x_63 1) (= x_43 x_7)) (not ?v_133)) (= x_62 x_45)) (= x_56 x_53)) ?v_82) ?v_84) ?v_83) ?v_85) ?v_86) ?v_89)) (and (and (and (and (and (and (and (and (and (= x_63 2) (= x_43 ?v_11)) ?v_82) ?v_88) ?v_84) ?v_83) ?v_85) ?v_86) (= x_61 (store x_50 x_51 x_53))) ?v_87)) (and (and (and (and (and (and (and (and (and (= x_63 3) (= x_43 x_55)) ?v_82) ?v_88) ?v_84) ?v_83) ?v_85) ?v_86) (= x_61 (store x_50 x_45 x_51))) ?v_87)) (and (and (and (and (and (and (and (and (and (= x_63 4) (not (<= x_43 x_55))) ?v_88) ?v_84) ?v_83) ?v_85) ?v_86) ?v_89) ?v_87) (= x_54 x_43)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_52 0) (< x_32 x_7)) ?v_90) (= x_49 (+ x_38 1))) (= x_45 x_37)) (= x_48 (+ x_37 1))) (= x_46 (store x_35 x_37 x_32))) ?v_91) (= x_50 (store x_39 x_37 x_34))) ?v_95) (and (and (and (and (and (and (and (and (and (and (= x_52 1) (= x_32 x_7)) (not ?v_134)) (= x_51 x_34)) (= x_45 x_42)) ?v_90) ?v_92) ?v_91) ?v_93) ?v_94) ?v_97)) (and (and (and (and (and (and (and (and (and (= x_52 2) (= x_32 ?v_11)) ?v_90) ?v_96) ?v_92) ?v_91) ?v_93) ?v_94) (= x_50 (store x_39 x_40 x_42))) ?v_95)) (and (and (and (and (and (and (and (and (and (= x_52 3) (= x_32 x_44)) ?v_90) ?v_96) ?v_92) ?v_91) ?v_93) ?v_94) (= x_50 (store x_39 x_34 x_40))) ?v_95)) (and (and (and (and (and (and (and (and (and (= x_52 4) (not (<= x_32 x_44))) ?v_96) ?v_92) ?v_91) ?v_93) ?v_94) ?v_97) ?v_95) (= x_43 x_32)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_41 0) (< x_21 x_7)) ?v_98) (= x_38 (+ x_27 1))) (= x_34 x_26)) (= x_37 (+ x_26 1))) (= x_35 (store x_24 x_26 x_21))) ?v_99) (= x_39 (store x_28 x_26 x_23))) ?v_103) (and (and (and (and (and (and (and (and (and (and (= x_41 1) (= x_21 x_7)) (not ?v_135)) (= x_40 x_23)) (= x_34 x_31)) ?v_98) ?v_100) ?v_99) ?v_101) ?v_102) ?v_105)) (and (and (and (and (and (and (and (and (and (= x_41 2) (= x_21 ?v_11)) ?v_98) ?v_104) ?v_100) ?v_99) ?v_101) ?v_102) (= x_39 (store x_28 x_29 x_31))) ?v_103)) (and (and (and (and (and (and (and (and (and (= x_41 3) (= x_21 x_33)) ?v_98) ?v_104) ?v_100) ?v_99) ?v_101) ?v_102) (= x_39 (store x_28 x_23 x_29))) ?v_103)) (and (and (and (and (and (and (and (and (and (= x_41 4) (not (<= x_21 x_33))) ?v_104) ?v_100) ?v_99) ?v_101) ?v_102) ?v_105) ?v_103) (= x_32 x_21)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_30 0) (< x_6 x_7)) ?v_106) (= x_27 (+ x_15 1))) (= x_23 x_14)) (= x_26 (+ x_14 1))) (= x_24 (store x_10 x_14 x_6))) ?v_107) (= x_28 (store x_16 x_14 x_9))) ?v_111) (and (and (and (and (and (and (and (and (and (and (= x_30 1) (= x_6 x_7)) (not ?v_136)) (= x_29 x_9)) (= x_23 x_20)) ?v_106) ?v_108) ?v_107) ?v_109) ?v_110) ?v_113)) (and (and (and (and (and (and (and (and (and (= x_30 2) (= x_6 ?v_11)) ?v_106) ?v_112) ?v_108) ?v_107) ?v_109) ?v_110) (= x_28 (store x_16 x_17 x_20))) ?v_111)) (and (and (and (and (and (and (and (and (and (= x_30 3) (= x_6 x_22)) ?v_106) ?v_112) ?v_108) ?v_107) ?v_109) ?v_110) (= x_28 (store x_16 x_9 x_17))) ?v_111)) (and (and (and (and (and (and (and (and (and (= x_30 4) (not (<= x_6 x_22))) ?v_112) ?v_108) ?v_107) ?v_109) ?v_110) ?v_113) ?v_111) (= x_21 x_6)))) (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_19 0) (< x_0 x_7)) ?v_115) (= x_15 (+ x_3 1))) (= x_9 x_1)) (= x_14 (+ x_1 1))) (= x_10 (store x_11 x_1 x_0))) ?v_116) (= x_16 (store x_4 x_1 x_2))) ?v_120) (and (and (and (and (and (and (and (and (and (and (= x_19 1) (= x_0 x_7)) (not ?v_114)) (= x_17 x_2)) (= x_9 x_5)) ?v_115) ?v_117) ?v_116) ?v_118) ?v_119) ?v_122)) (and (and (and (and (and (and (and (and (and (= x_19 2) (= x_0 ?v_11)) ?v_115) ?v_121) ?v_117) ?v_116) ?v_118) ?v_119) (= x_16 (store x_4 x_18 x_5))) ?v_120)) (and (and (and (and (and (and (and (and (and (= x_19 3) (= x_0 x_8)) ?v_115) ?v_121) ?v_117) ?v_116) ?v_118) ?v_119) (= x_16 (store x_4 x_2 x_18))) ?v_120)) (and (and (and (and (and (and (and (and (and (= x_19 4) (not (<= x_0 x_8))) ?v_121) ?v_117) ?v_116) ?v_118) ?v_119) ?v_122) ?v_120) (= x_6 x_0)))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (not (<= x_164 0)) (= x_166 (- 1))) (and (not (<= x_153 0)) ?v_123)) (and (not (<= x_142 0)) ?v_124)) (and (not (<= x_131 0)) ?v_125)) (and (not (<= x_120 0)) ?v_126)) (and (not (<= x_109 0)) ?v_127)) (and (not (<= x_98 0)) ?v_128)) (and (not (<= x_87 0)) ?v_129)) (and (not (<= x_76 0)) ?v_130)) (and (not (<= x_65 0)) ?v_131)) (and (not (<= x_54 0)) ?v_132)) (and (not (<= x_43 0)) ?v_133)) (and (not (<= x_32 0)) ?v_134)) (and (not (<= x_21 0)) ?v_135)) (and (not (<= x_6 0)) ?v_136)) (and (not (<= x_0 0)) ?v_114)))))
(check-sat)
(exit)
