// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHSubInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstNegInt___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_inc(x_1);
x_62 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8, x_11);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_cleanupAnnotations(x_63);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_inc(x_65);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_68 = l_Lean_Expr_isApp(x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_inc(x_67);
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
lean_inc(x_69);
x_73 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_74 = lean_mk_string_unchecked("Neg", 3, 3);
x_75 = lean_mk_string_unchecked("neg", 3, 3);
x_76 = l_Lean_Name_mkStr2(x_74, x_75);
x_77 = l_Lean_Expr_isConstOf(x_73, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_mk_string_unchecked("OfNat", 5, 5);
x_79 = lean_mk_string_unchecked("ofNat", 5, 5);
x_80 = l_Lean_Name_mkStr2(x_78, x_79);
x_81 = l_Lean_Expr_isConstOf(x_73, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Expr_isApp(x_73);
if (x_82 == 0)
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Expr_appFnCleanup___redArg(x_73);
x_84 = l_Lean_Expr_isApp(x_83);
if (x_84 == 0)
{
lean_dec(x_83);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Expr_appFnCleanup___redArg(x_83);
x_86 = l_Lean_Expr_isApp(x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
lean_dec(x_69);
x_88 = l_Lean_Expr_appFnCleanup___redArg(x_85);
x_89 = lean_mk_string_unchecked("HMul", 4, 4);
x_90 = lean_mk_string_unchecked("hMul", 4, 4);
x_91 = l_Lean_Name_mkStr2(x_89, x_90);
x_92 = l_Lean_Expr_isConstOf(x_88, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_mk_string_unchecked("HSub", 4, 4);
x_94 = lean_mk_string_unchecked("hSub", 4, 4);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = l_Lean_Expr_isConstOf(x_88, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_mk_string_unchecked("HAdd", 4, 4);
x_98 = lean_mk_string_unchecked("hAdd", 4, 4);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = l_Lean_Expr_isConstOf(x_88, x_99);
lean_dec(x_99);
lean_dec(x_88);
if (x_100 == 0)
{
lean_dec(x_87);
lean_dec(x_72);
lean_dec(x_71);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_64;
goto block_61;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_Meta_isInstHAddInt___redArg(x_87, x_8, x_64);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_72);
lean_dec(x_71);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_104;
goto block_61;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_72, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_105);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_113);
lean_ctor_set(x_111, 0, x_107);
return x_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_111);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_free_object(x_107);
lean_dec(x_109);
return x_111;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_107, 0);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_107);
x_119 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_120);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_dec(x_117);
return x_119;
}
}
}
else
{
lean_dec(x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_107;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_88);
x_125 = l_Lean_Meta_isInstHSubInt___redArg(x_87, x_8, x_64);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_72);
lean_dec(x_71);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_128;
goto block_61;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_72, x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
x_135 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_ctor_set_tag(x_131, 3);
lean_ctor_set(x_131, 1, x_137);
lean_ctor_set(x_135, 0, x_131);
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_135);
lean_ctor_set_tag(x_131, 3);
lean_ctor_set(x_131, 1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
else
{
lean_free_object(x_131);
lean_dec(x_133);
return x_135;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_144);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
else
{
lean_dec(x_141);
return x_143;
}
}
}
else
{
lean_dec(x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_131;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_dec(x_88);
x_149 = l_Lean_Meta_isInstHMulInt___redArg(x_87, x_8, x_64);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_72);
lean_dec(x_71);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_152;
goto block_61;
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_149);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_149, 1);
x_155 = lean_ctor_get(x_149, 0);
lean_dec(x_155);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_72);
x_156 = l_Lean_Meta_getIntValue_x3f(x_72, x_7, x_8, x_9, x_10, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_159 = l_Lean_Meta_getIntValue_x3f(x_71, x_7, x_8, x_9, x_10, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_free_object(x_149);
lean_dec(x_72);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_161;
goto block_61;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_unsigned_to_nat(0u);
x_165 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_72, x_164, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_162);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_165, 0);
lean_ctor_set_tag(x_149, 6);
lean_ctor_set(x_149, 1, x_163);
lean_ctor_set(x_149, 0, x_167);
lean_ctor_set(x_165, 0, x_149);
return x_165;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_165, 0);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_165);
lean_ctor_set_tag(x_149, 6);
lean_ctor_set(x_149, 1, x_163);
lean_ctor_set(x_149, 0, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_149);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_dec(x_163);
lean_free_object(x_149);
return x_165;
}
}
}
else
{
uint8_t x_171; 
lean_free_object(x_149);
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_159);
if (x_171 == 0)
{
return x_159;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_159, 0);
x_173 = lean_ctor_get(x_159, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_159);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_72);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_ctor_get(x_156, 1);
lean_inc(x_175);
lean_dec(x_156);
x_176 = lean_ctor_get(x_157, 0);
lean_inc(x_176);
lean_dec(x_157);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_177, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_175);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_178, 0);
lean_ctor_set_tag(x_149, 5);
lean_ctor_set(x_149, 1, x_180);
lean_ctor_set(x_149, 0, x_176);
lean_ctor_set(x_178, 0, x_149);
return x_178;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_178, 0);
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_178);
lean_ctor_set_tag(x_149, 5);
lean_ctor_set(x_149, 1, x_181);
lean_ctor_set(x_149, 0, x_176);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_149);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
else
{
lean_dec(x_176);
lean_free_object(x_149);
return x_178;
}
}
}
else
{
uint8_t x_184; 
lean_free_object(x_149);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_156);
if (x_184 == 0)
{
return x_156;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_156, 0);
x_186 = lean_ctor_get(x_156, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_156);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_149, 1);
lean_inc(x_188);
lean_dec(x_149);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_72);
x_189 = l_Lean_Meta_getIntValue_x3f(x_72, x_7, x_8, x_9, x_10, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_192 = l_Lean_Meta_getIntValue_x3f(x_71, x_7, x_8, x_9, x_10, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
lean_dec(x_72);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_194;
goto block_61;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_unsigned_to_nat(0u);
x_198 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_72, x_197, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_195);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
x_202 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_196);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
return x_203;
}
else
{
lean_dec(x_196);
return x_198;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_192, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_192, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_206 = x_192;
} else {
 lean_dec_ref(x_192);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_72);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_ctor_get(x_189, 1);
lean_inc(x_208);
lean_dec(x_189);
x_209 = lean_ctor_get(x_190, 0);
lean_inc(x_209);
lean_dec(x_190);
x_210 = lean_unsigned_to_nat(0u);
x_211 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_210, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_208);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_215, 0, x_209);
lean_ctor_set(x_215, 1, x_212);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
else
{
lean_dec(x_209);
return x_211;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_189, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_189, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_219 = x_189;
} else {
 lean_dec_ref(x_189);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
}
}
}
}
}
else
{
lean_object* x_221; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_221 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_223;
goto block_61;
}
else
{
uint8_t x_224; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_221);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_221, 0);
lean_dec(x_225);
x_226 = !lean_is_exclusive(x_222);
if (x_226 == 0)
{
lean_ctor_set_tag(x_222, 0);
return x_221;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_222, 0);
lean_inc(x_227);
lean_dec(x_222);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_221, 0, x_228);
return x_221;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_221, 1);
lean_inc(x_229);
lean_dec(x_221);
x_230 = lean_ctor_get(x_222, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_231 = x_222;
} else {
 lean_dec_ref(x_222);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_231;
 lean_ctor_set_tag(x_232, 0);
}
lean_ctor_set(x_232, 0, x_230);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_229);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_221);
if (x_234 == 0)
{
return x_221;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_221, 0);
x_236 = lean_ctor_get(x_221, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_221);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_dec(x_73);
lean_dec(x_69);
x_238 = l_Lean_Meta_isInstNegInt___redArg(x_72, x_8, x_64);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_71);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_241;
goto block_61;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_2);
lean_dec(x_1);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_unsigned_to_nat(0u);
x_244 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_71, x_243, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_242);
if (lean_obj_tag(x_244) == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_244, 0, x_247);
return x_244;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_244, 0);
x_249 = lean_ctor_get(x_244, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_244);
x_250 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_250, 0, x_248);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
return x_244;
}
}
}
}
}
}
block_61:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = l_Lean_Meta_Grind_shareCommon___redArg(x_12, x_16, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_23, x_13, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_30 = lean_grind_internalize(x_23, x_2, x_29, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_grind_cutsat_mk_var(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_dec(x_25);
x_49 = lean_grind_cutsat_mk_var(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
