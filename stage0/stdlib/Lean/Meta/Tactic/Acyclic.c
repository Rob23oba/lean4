// Lean compiler output
// Module: Lean.Meta.Tactic.Acyclic
// Imports: Lean.Meta.MatchUtil Lean.Meta.Tactic.Simp.Main
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_856_(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isFVar(x_1);
if (x_11 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_10;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Expr_occurs(x_1, x_2);
if (x_12 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_10;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Meta_isConstructorApp_x27(x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_43; lean_object* x_44; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_mk_string_unchecked("SizeOf", 6, 6);
x_49 = lean_mk_string_unchecked("sizeOf", 6, 6);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_mk_empty_array_with_capacity(x_51);
lean_inc(x_52);
x_53 = lean_array_push(x_52, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
x_54 = l_Lean_Meta_mkAppM(x_50, x_53, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_52);
x_57 = lean_array_push(x_52, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_58 = l_Lean_Meta_mkAppM(x_50, x_57, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_61 = l_Lean_Meta_mkLT(x_55, x_59, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_box(0);
lean_inc(x_5);
x_65 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_64, x_5, x_6, x_7, x_8, x_63);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = l_Lean_Meta_getSimpTheorems___redArg(x_8, x_68);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; uint8_t x_113; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_unsigned_to_nat(100000u);
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_box(0);
x_76 = lean_box(1);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_74);
x_79 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_79);
x_80 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 1, x_80);
x_81 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 2, x_81);
x_82 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 3, x_82);
x_83 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 4, x_83);
x_84 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 5, x_84);
x_85 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 6, x_85);
x_86 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 7, x_86);
x_87 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 8, x_87);
x_88 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 9, x_88);
x_89 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 10, x_89);
x_90 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 11, x_90);
x_91 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 12, x_91);
x_92 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 13, x_92);
x_93 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 14, x_93);
x_94 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 15, x_94);
x_95 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 16, x_95);
x_96 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 17, x_96);
x_97 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 18, x_97);
x_98 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2 + 19, x_98);
lean_inc(x_52);
x_99 = lean_array_push(x_52, x_71);
x_100 = lean_unsigned_to_nat(8u);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_nat_shiftl(x_100, x_74);
x_103 = lean_unsigned_to_nat(3u);
x_104 = lean_nat_div(x_102, x_103);
lean_dec(x_102);
x_105 = l_Nat_nextPowerOfTwo(x_104);
lean_dec(x_104);
x_106 = lean_box(0);
x_107 = lean_mk_array(x_105, x_106);
lean_ctor_set(x_69, 1, x_107);
lean_ctor_set(x_69, 0, x_101);
x_108 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_108);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_110, 0, x_69);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_unbox(x_76);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_111);
x_112 = l_Lean_Meta_Simp_mkContext(x_78, x_99, x_110, x_5, x_6, x_7, x_8, x_72);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; lean_object* x_123; lean_object* x_124; size_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
x_116 = l_Lean_Expr_mvarId_x21(x_67);
x_117 = l_Array_empty(lean_box(0));
x_118 = lean_box(0);
lean_inc(x_108);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_108);
lean_inc(x_119);
lean_ctor_set(x_112, 1, x_101);
lean_ctor_set(x_112, 0, x_119);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_108);
x_121 = lean_unsigned_to_nat(5u);
x_122 = lean_usize_of_nat(x_121);
x_123 = lean_usize_to_nat(x_122);
x_124 = lean_nat_pow(x_74, x_123);
lean_dec(x_123);
x_125 = lean_usize_of_nat(x_124);
lean_dec(x_124);
x_126 = lean_usize_to_nat(x_125);
x_127 = lean_mk_empty_array_with_capacity(x_126);
lean_dec(x_126);
lean_inc(x_127);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_101);
lean_ctor_set(x_129, 3, x_101);
lean_ctor_set_usize(x_129, 4, x_122);
lean_inc(x_119);
x_130 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_130, 0, x_119);
lean_ctor_set(x_130, 1, x_119);
lean_ctor_set(x_130, 2, x_120);
lean_ctor_set(x_130, 3, x_129);
lean_ctor_set(x_65, 1, x_130);
lean_ctor_set(x_65, 0, x_112);
x_131 = lean_unbox(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_132 = l_Lean_Meta_simpTarget(x_116, x_114, x_117, x_118, x_131, x_65, x_5, x_6, x_7, x_8, x_115);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Expr_appFn_x21(x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_140 = l_Lean_Meta_mkCongrArg(x_139, x_137, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_mk_string_unchecked("Nat", 3, 3);
x_144 = lean_mk_string_unchecked("lt_of_lt_of_eq", 14, 14);
lean_inc(x_143);
x_145 = l_Lean_Name_mkStr2(x_143, x_144);
x_146 = lean_mk_empty_array_with_capacity(x_74);
x_147 = lean_array_push(x_146, x_67);
x_148 = lean_array_push(x_147, x_141);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_149 = l_Lean_Meta_mkAppM(x_145, x_148, x_5, x_6, x_7, x_8, x_142);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_mk_string_unchecked("lt_irrefl", 9, 9);
x_153 = l_Lean_Name_mkStr2(x_143, x_152);
x_154 = lean_array_push(x_52, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_155 = l_Lean_Meta_mkAppM(x_153, x_154, x_5, x_6, x_7, x_8, x_151);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_1);
x_158 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Expr_app___override(x_156, x_150);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_162 = l_Lean_Meta_mkFalseElim(x_159, x_161, x_5, x_6, x_7, x_8, x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_163, x_6, x_164);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_mk_string_unchecked("Meta", 4, 4);
x_168 = lean_mk_string_unchecked("Tactic", 6, 6);
x_169 = lean_mk_string_unchecked("acyclic", 7, 7);
x_170 = l_Lean_Name_mkStr3(x_167, x_168, x_169);
lean_inc(x_170);
x_171 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_170, x_5, x_6, x_7, x_8, x_166);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_174 = !lean_is_exclusive(x_171);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_171, 0);
lean_dec(x_175);
lean_ctor_set(x_171, 0, x_76);
return x_171;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_76);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_171, 1);
lean_inc(x_178);
lean_dec(x_171);
x_179 = lean_mk_string_unchecked("succeeded", 9, 9);
x_180 = l_Lean_stringToMessageData(x_179);
lean_dec(x_179);
x_181 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_170, x_180, x_5, x_6, x_7, x_8, x_178);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_181, 0);
lean_dec(x_183);
lean_ctor_set(x_181, 0, x_76);
return x_181;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_76);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_1);
x_186 = lean_ctor_get(x_162, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_162, 1);
lean_inc(x_187);
lean_dec(x_162);
x_43 = x_186;
x_44 = x_187;
goto block_47;
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_156);
lean_dec(x_150);
lean_dec(x_1);
x_188 = lean_ctor_get(x_158, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_158, 1);
lean_inc(x_189);
lean_dec(x_158);
x_43 = x_188;
x_44 = x_189;
goto block_47;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_150);
lean_dec(x_1);
x_190 = lean_ctor_get(x_155, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_155, 1);
lean_inc(x_191);
lean_dec(x_155);
x_43 = x_190;
x_44 = x_191;
goto block_47;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_143);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_192 = lean_ctor_get(x_149, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_149, 1);
lean_inc(x_193);
lean_dec(x_149);
x_43 = x_192;
x_44 = x_193;
goto block_47;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_194 = lean_ctor_get(x_140, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_140, 1);
lean_inc(x_195);
lean_dec(x_140);
x_43 = x_194;
x_44 = x_195;
goto block_47;
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_196 = lean_ctor_get(x_136, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_136, 1);
lean_inc(x_197);
lean_dec(x_136);
x_43 = x_196;
x_44 = x_197;
goto block_47;
}
}
else
{
uint8_t x_198; 
lean_dec(x_134);
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_132);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_132, 0);
lean_dec(x_199);
lean_ctor_set(x_132, 0, x_75);
return x_132;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_132, 1);
lean_inc(x_200);
lean_dec(x_132);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_75);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_ctor_get(x_132, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_132, 1);
lean_inc(x_203);
lean_dec(x_132);
x_43 = x_202;
x_44 = x_203;
goto block_47;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; size_t x_213; lean_object* x_214; lean_object* x_215; size_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_204 = lean_ctor_get(x_112, 0);
x_205 = lean_ctor_get(x_112, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_112);
x_206 = l_Lean_Expr_mvarId_x21(x_67);
x_207 = l_Array_empty(lean_box(0));
x_208 = lean_box(0);
lean_inc(x_108);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_108);
lean_inc(x_209);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_101);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_108);
x_212 = lean_unsigned_to_nat(5u);
x_213 = lean_usize_of_nat(x_212);
x_214 = lean_usize_to_nat(x_213);
x_215 = lean_nat_pow(x_74, x_214);
lean_dec(x_214);
x_216 = lean_usize_of_nat(x_215);
lean_dec(x_215);
x_217 = lean_usize_to_nat(x_216);
x_218 = lean_mk_empty_array_with_capacity(x_217);
lean_dec(x_217);
lean_inc(x_218);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
lean_ctor_set(x_220, 2, x_101);
lean_ctor_set(x_220, 3, x_101);
lean_ctor_set_usize(x_220, 4, x_213);
lean_inc(x_209);
x_221 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_221, 0, x_209);
lean_ctor_set(x_221, 1, x_209);
lean_ctor_set(x_221, 2, x_211);
lean_ctor_set(x_221, 3, x_220);
lean_ctor_set(x_65, 1, x_221);
lean_ctor_set(x_65, 0, x_210);
x_222 = lean_unbox(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_223 = l_Lean_Meta_simpTarget(x_206, x_204, x_207, x_208, x_222, x_65, x_5, x_6, x_7, x_8, x_205);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec(x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_227 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Expr_appFn_x21(x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_231 = l_Lean_Meta_mkCongrArg(x_230, x_228, x_5, x_6, x_7, x_8, x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_mk_string_unchecked("Nat", 3, 3);
x_235 = lean_mk_string_unchecked("lt_of_lt_of_eq", 14, 14);
lean_inc(x_234);
x_236 = l_Lean_Name_mkStr2(x_234, x_235);
x_237 = lean_mk_empty_array_with_capacity(x_74);
x_238 = lean_array_push(x_237, x_67);
x_239 = lean_array_push(x_238, x_232);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_240 = l_Lean_Meta_mkAppM(x_236, x_239, x_5, x_6, x_7, x_8, x_233);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_mk_string_unchecked("lt_irrefl", 9, 9);
x_244 = l_Lean_Name_mkStr2(x_234, x_243);
x_245 = lean_array_push(x_52, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_246 = l_Lean_Meta_mkAppM(x_244, x_245, x_5, x_6, x_7, x_8, x_242);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
lean_inc(x_1);
x_249 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_Lean_Expr_app___override(x_247, x_241);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_253 = l_Lean_Meta_mkFalseElim(x_250, x_252, x_5, x_6, x_7, x_8, x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_254, x_6, x_255);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_mk_string_unchecked("Meta", 4, 4);
x_259 = lean_mk_string_unchecked("Tactic", 6, 6);
x_260 = lean_mk_string_unchecked("acyclic", 7, 7);
x_261 = l_Lean_Name_mkStr3(x_258, x_259, x_260);
lean_inc(x_261);
x_262 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_261, x_5, x_6, x_7, x_8, x_257);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_261);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_266 = x_262;
} else {
 lean_dec_ref(x_262);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_76);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_268 = lean_ctor_get(x_262, 1);
lean_inc(x_268);
lean_dec(x_262);
x_269 = lean_mk_string_unchecked("succeeded", 9, 9);
x_270 = l_Lean_stringToMessageData(x_269);
lean_dec(x_269);
x_271 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_261, x_270, x_5, x_6, x_7, x_8, x_268);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_76);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_1);
x_275 = lean_ctor_get(x_253, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_253, 1);
lean_inc(x_276);
lean_dec(x_253);
x_43 = x_275;
x_44 = x_276;
goto block_47;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_247);
lean_dec(x_241);
lean_dec(x_1);
x_277 = lean_ctor_get(x_249, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_249, 1);
lean_inc(x_278);
lean_dec(x_249);
x_43 = x_277;
x_44 = x_278;
goto block_47;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_241);
lean_dec(x_1);
x_279 = lean_ctor_get(x_246, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_246, 1);
lean_inc(x_280);
lean_dec(x_246);
x_43 = x_279;
x_44 = x_280;
goto block_47;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_234);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_281 = lean_ctor_get(x_240, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_240, 1);
lean_inc(x_282);
lean_dec(x_240);
x_43 = x_281;
x_44 = x_282;
goto block_47;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_283 = lean_ctor_get(x_231, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_231, 1);
lean_inc(x_284);
lean_dec(x_231);
x_43 = x_283;
x_44 = x_284;
goto block_47;
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_285 = lean_ctor_get(x_227, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_227, 1);
lean_inc(x_286);
lean_dec(x_227);
x_43 = x_285;
x_44 = x_286;
goto block_47;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_225);
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_287 = lean_ctor_get(x_223, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_288 = x_223;
} else {
 lean_dec_ref(x_223);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_75);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_290 = lean_ctor_get(x_223, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_223, 1);
lean_inc(x_291);
lean_dec(x_223);
x_43 = x_290;
x_44 = x_291;
goto block_47;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; uint8_t x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; uint8_t x_317; uint8_t x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; size_t x_345; lean_object* x_346; lean_object* x_347; size_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; 
x_292 = lean_ctor_get(x_69, 0);
x_293 = lean_ctor_get(x_69, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_69);
x_294 = lean_unsigned_to_nat(100000u);
x_295 = lean_unsigned_to_nat(2u);
x_296 = lean_box(0);
x_297 = lean_box(1);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_299, 0, x_294);
lean_ctor_set(x_299, 1, x_295);
x_300 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_300);
x_301 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 1, x_301);
x_302 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 2, x_302);
x_303 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 3, x_303);
x_304 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 4, x_304);
x_305 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 5, x_305);
x_306 = lean_unbox(x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 6, x_306);
x_307 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 7, x_307);
x_308 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 8, x_308);
x_309 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 9, x_309);
x_310 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 10, x_310);
x_311 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 11, x_311);
x_312 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 12, x_312);
x_313 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 13, x_313);
x_314 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 14, x_314);
x_315 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 15, x_315);
x_316 = lean_unbox(x_296);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 16, x_316);
x_317 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 17, x_317);
x_318 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 18, x_318);
x_319 = lean_unbox(x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*2 + 19, x_319);
lean_inc(x_52);
x_320 = lean_array_push(x_52, x_292);
x_321 = lean_unsigned_to_nat(8u);
x_322 = lean_unsigned_to_nat(0u);
x_323 = lean_nat_shiftl(x_321, x_295);
x_324 = lean_unsigned_to_nat(3u);
x_325 = lean_nat_div(x_323, x_324);
lean_dec(x_323);
x_326 = l_Nat_nextPowerOfTwo(x_325);
lean_dec(x_325);
x_327 = lean_box(0);
x_328 = lean_mk_array(x_326, x_327);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_330);
x_331 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_331, 0, x_330);
x_332 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_unbox(x_297);
lean_ctor_set_uint8(x_332, sizeof(void*)*2, x_333);
x_334 = l_Lean_Meta_Simp_mkContext(x_299, x_320, x_332, x_5, x_6, x_7, x_8, x_293);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
x_338 = l_Lean_Expr_mvarId_x21(x_67);
x_339 = l_Array_empty(lean_box(0));
x_340 = lean_box(0);
lean_inc(x_330);
x_341 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_341, 0, x_330);
lean_inc(x_341);
if (lean_is_scalar(x_337)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_337;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_322);
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_330);
x_344 = lean_unsigned_to_nat(5u);
x_345 = lean_usize_of_nat(x_344);
x_346 = lean_usize_to_nat(x_345);
x_347 = lean_nat_pow(x_295, x_346);
lean_dec(x_346);
x_348 = lean_usize_of_nat(x_347);
lean_dec(x_347);
x_349 = lean_usize_to_nat(x_348);
x_350 = lean_mk_empty_array_with_capacity(x_349);
lean_dec(x_349);
lean_inc(x_350);
x_351 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_351, 0, x_350);
x_352 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
lean_ctor_set(x_352, 2, x_322);
lean_ctor_set(x_352, 3, x_322);
lean_ctor_set_usize(x_352, 4, x_345);
lean_inc(x_341);
x_353 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_353, 0, x_341);
lean_ctor_set(x_353, 1, x_341);
lean_ctor_set(x_353, 2, x_343);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set(x_65, 1, x_353);
lean_ctor_set(x_65, 0, x_342);
x_354 = lean_unbox(x_297);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_355 = l_Lean_Meta_simpTarget(x_338, x_335, x_339, x_340, x_354, x_65, x_5, x_6, x_7, x_8, x_336);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
lean_dec(x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_dec(x_355);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_359 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_Expr_appFn_x21(x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_363 = l_Lean_Meta_mkCongrArg(x_362, x_360, x_5, x_6, x_7, x_8, x_361);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_mk_string_unchecked("Nat", 3, 3);
x_367 = lean_mk_string_unchecked("lt_of_lt_of_eq", 14, 14);
lean_inc(x_366);
x_368 = l_Lean_Name_mkStr2(x_366, x_367);
x_369 = lean_mk_empty_array_with_capacity(x_295);
x_370 = lean_array_push(x_369, x_67);
x_371 = lean_array_push(x_370, x_364);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_372 = l_Lean_Meta_mkAppM(x_368, x_371, x_5, x_6, x_7, x_8, x_365);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
x_375 = lean_mk_string_unchecked("lt_irrefl", 9, 9);
x_376 = l_Lean_Name_mkStr2(x_366, x_375);
x_377 = lean_array_push(x_52, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_378 = l_Lean_Meta_mkAppM(x_376, x_377, x_5, x_6, x_7, x_8, x_374);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
lean_inc(x_1);
x_381 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_380);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = l_Lean_Expr_app___override(x_379, x_373);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_385 = l_Lean_Meta_mkFalseElim(x_382, x_384, x_5, x_6, x_7, x_8, x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_386, x_6, x_387);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
x_390 = lean_mk_string_unchecked("Meta", 4, 4);
x_391 = lean_mk_string_unchecked("Tactic", 6, 6);
x_392 = lean_mk_string_unchecked("acyclic", 7, 7);
x_393 = l_Lean_Name_mkStr3(x_390, x_391, x_392);
lean_inc(x_393);
x_394 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_393, x_5, x_6, x_7, x_8, x_389);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_unbox(x_395);
lean_dec(x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_393);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_397 = lean_ctor_get(x_394, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_398 = x_394;
} else {
 lean_dec_ref(x_394);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_297);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_400 = lean_ctor_get(x_394, 1);
lean_inc(x_400);
lean_dec(x_394);
x_401 = lean_mk_string_unchecked("succeeded", 9, 9);
x_402 = l_Lean_stringToMessageData(x_401);
lean_dec(x_401);
x_403 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_393, x_402, x_5, x_6, x_7, x_8, x_400);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_405 = x_403;
} else {
 lean_dec_ref(x_403);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_297);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; 
lean_dec(x_1);
x_407 = lean_ctor_get(x_385, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_385, 1);
lean_inc(x_408);
lean_dec(x_385);
x_43 = x_407;
x_44 = x_408;
goto block_47;
}
}
else
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_379);
lean_dec(x_373);
lean_dec(x_1);
x_409 = lean_ctor_get(x_381, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_381, 1);
lean_inc(x_410);
lean_dec(x_381);
x_43 = x_409;
x_44 = x_410;
goto block_47;
}
}
else
{
lean_object* x_411; lean_object* x_412; 
lean_dec(x_373);
lean_dec(x_1);
x_411 = lean_ctor_get(x_378, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_378, 1);
lean_inc(x_412);
lean_dec(x_378);
x_43 = x_411;
x_44 = x_412;
goto block_47;
}
}
else
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_366);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_413 = lean_ctor_get(x_372, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_372, 1);
lean_inc(x_414);
lean_dec(x_372);
x_43 = x_413;
x_44 = x_414;
goto block_47;
}
}
else
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_415 = lean_ctor_get(x_363, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_363, 1);
lean_inc(x_416);
lean_dec(x_363);
x_43 = x_415;
x_44 = x_416;
goto block_47;
}
}
else
{
lean_object* x_417; lean_object* x_418; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_417 = lean_ctor_get(x_359, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_359, 1);
lean_inc(x_418);
lean_dec(x_359);
x_43 = x_417;
x_44 = x_418;
goto block_47;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_357);
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_419 = lean_ctor_get(x_355, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_420 = x_355;
} else {
 lean_dec_ref(x_355);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_296);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lean_ctor_get(x_355, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_355, 1);
lean_inc(x_423);
lean_dec(x_355);
x_43 = x_422;
x_44 = x_423;
goto block_47;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; uint8_t x_437; uint8_t x_438; uint8_t x_439; uint8_t x_440; uint8_t x_441; uint8_t x_442; uint8_t x_443; uint8_t x_444; uint8_t x_445; uint8_t x_446; uint8_t x_447; uint8_t x_448; uint8_t x_449; uint8_t x_450; uint8_t x_451; uint8_t x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; size_t x_481; lean_object* x_482; lean_object* x_483; size_t x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; 
x_424 = lean_ctor_get(x_65, 0);
x_425 = lean_ctor_get(x_65, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_65);
x_426 = l_Lean_Meta_getSimpTheorems___redArg(x_8, x_425);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_429 = x_426;
} else {
 lean_dec_ref(x_426);
 x_429 = lean_box(0);
}
x_430 = lean_unsigned_to_nat(100000u);
x_431 = lean_unsigned_to_nat(2u);
x_432 = lean_box(0);
x_433 = lean_box(1);
x_434 = lean_box(0);
x_435 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
x_436 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2, x_436);
x_437 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 1, x_437);
x_438 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 2, x_438);
x_439 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 3, x_439);
x_440 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 4, x_440);
x_441 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 5, x_441);
x_442 = lean_unbox(x_434);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 6, x_442);
x_443 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 7, x_443);
x_444 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 8, x_444);
x_445 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 9, x_445);
x_446 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 10, x_446);
x_447 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 11, x_447);
x_448 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 12, x_448);
x_449 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 13, x_449);
x_450 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 14, x_450);
x_451 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 15, x_451);
x_452 = lean_unbox(x_432);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 16, x_452);
x_453 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 17, x_453);
x_454 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 18, x_454);
x_455 = lean_unbox(x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*2 + 19, x_455);
lean_inc(x_52);
x_456 = lean_array_push(x_52, x_427);
x_457 = lean_unsigned_to_nat(8u);
x_458 = lean_unsigned_to_nat(0u);
x_459 = lean_nat_shiftl(x_457, x_431);
x_460 = lean_unsigned_to_nat(3u);
x_461 = lean_nat_div(x_459, x_460);
lean_dec(x_459);
x_462 = l_Nat_nextPowerOfTwo(x_461);
lean_dec(x_461);
x_463 = lean_box(0);
x_464 = lean_mk_array(x_462, x_463);
if (lean_is_scalar(x_429)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_429;
}
lean_ctor_set(x_465, 0, x_458);
lean_ctor_set(x_465, 1, x_464);
x_466 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_466);
x_467 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_467, 0, x_466);
x_468 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_unbox(x_433);
lean_ctor_set_uint8(x_468, sizeof(void*)*2, x_469);
x_470 = l_Lean_Meta_Simp_mkContext(x_435, x_456, x_468, x_5, x_6, x_7, x_8, x_428);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
x_474 = l_Lean_Expr_mvarId_x21(x_424);
x_475 = l_Array_empty(lean_box(0));
x_476 = lean_box(0);
lean_inc(x_466);
x_477 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_477, 0, x_466);
lean_inc(x_477);
if (lean_is_scalar(x_473)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_473;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_458);
x_479 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_479, 0, x_466);
x_480 = lean_unsigned_to_nat(5u);
x_481 = lean_usize_of_nat(x_480);
x_482 = lean_usize_to_nat(x_481);
x_483 = lean_nat_pow(x_431, x_482);
lean_dec(x_482);
x_484 = lean_usize_of_nat(x_483);
lean_dec(x_483);
x_485 = lean_usize_to_nat(x_484);
x_486 = lean_mk_empty_array_with_capacity(x_485);
lean_dec(x_485);
lean_inc(x_486);
x_487 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_486);
lean_ctor_set(x_488, 2, x_458);
lean_ctor_set(x_488, 3, x_458);
lean_ctor_set_usize(x_488, 4, x_481);
lean_inc(x_477);
x_489 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_489, 0, x_477);
lean_ctor_set(x_489, 1, x_477);
lean_ctor_set(x_489, 2, x_479);
lean_ctor_set(x_489, 3, x_488);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_478);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_unbox(x_433);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_492 = l_Lean_Meta_simpTarget(x_474, x_471, x_475, x_476, x_491, x_490, x_5, x_6, x_7, x_8, x_472);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec(x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_dec(x_492);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_496 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = l_Lean_Expr_appFn_x21(x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_500 = l_Lean_Meta_mkCongrArg(x_499, x_497, x_5, x_6, x_7, x_8, x_498);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_mk_string_unchecked("Nat", 3, 3);
x_504 = lean_mk_string_unchecked("lt_of_lt_of_eq", 14, 14);
lean_inc(x_503);
x_505 = l_Lean_Name_mkStr2(x_503, x_504);
x_506 = lean_mk_empty_array_with_capacity(x_431);
x_507 = lean_array_push(x_506, x_424);
x_508 = lean_array_push(x_507, x_501);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_509 = l_Lean_Meta_mkAppM(x_505, x_508, x_5, x_6, x_7, x_8, x_502);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_512 = lean_mk_string_unchecked("lt_irrefl", 9, 9);
x_513 = l_Lean_Name_mkStr2(x_503, x_512);
x_514 = lean_array_push(x_52, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_515 = l_Lean_Meta_mkAppM(x_513, x_514, x_5, x_6, x_7, x_8, x_511);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
lean_inc(x_1);
x_518 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = l_Lean_Expr_app___override(x_516, x_510);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_522 = l_Lean_Meta_mkFalseElim(x_519, x_521, x_5, x_6, x_7, x_8, x_520);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_523, x_6, x_524);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
lean_dec(x_525);
x_527 = lean_mk_string_unchecked("Meta", 4, 4);
x_528 = lean_mk_string_unchecked("Tactic", 6, 6);
x_529 = lean_mk_string_unchecked("acyclic", 7, 7);
x_530 = l_Lean_Name_mkStr3(x_527, x_528, x_529);
lean_inc(x_530);
x_531 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_530, x_5, x_6, x_7, x_8, x_526);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_unbox(x_532);
lean_dec(x_532);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_530);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_534 = lean_ctor_get(x_531, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_535 = x_531;
} else {
 lean_dec_ref(x_531);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_433);
lean_ctor_set(x_536, 1, x_534);
return x_536;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_537 = lean_ctor_get(x_531, 1);
lean_inc(x_537);
lean_dec(x_531);
x_538 = lean_mk_string_unchecked("succeeded", 9, 9);
x_539 = l_Lean_stringToMessageData(x_538);
lean_dec(x_538);
x_540 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_530, x_539, x_5, x_6, x_7, x_8, x_537);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_541 = lean_ctor_get(x_540, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_542 = x_540;
} else {
 lean_dec_ref(x_540);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_433);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; 
lean_dec(x_1);
x_544 = lean_ctor_get(x_522, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_522, 1);
lean_inc(x_545);
lean_dec(x_522);
x_43 = x_544;
x_44 = x_545;
goto block_47;
}
}
else
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_516);
lean_dec(x_510);
lean_dec(x_1);
x_546 = lean_ctor_get(x_518, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_518, 1);
lean_inc(x_547);
lean_dec(x_518);
x_43 = x_546;
x_44 = x_547;
goto block_47;
}
}
else
{
lean_object* x_548; lean_object* x_549; 
lean_dec(x_510);
lean_dec(x_1);
x_548 = lean_ctor_get(x_515, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_515, 1);
lean_inc(x_549);
lean_dec(x_515);
x_43 = x_548;
x_44 = x_549;
goto block_47;
}
}
else
{
lean_object* x_550; lean_object* x_551; 
lean_dec(x_503);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_550 = lean_ctor_get(x_509, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_509, 1);
lean_inc(x_551);
lean_dec(x_509);
x_43 = x_550;
x_44 = x_551;
goto block_47;
}
}
else
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_424);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_552 = lean_ctor_get(x_500, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_500, 1);
lean_inc(x_553);
lean_dec(x_500);
x_43 = x_552;
x_44 = x_553;
goto block_47;
}
}
else
{
lean_object* x_554; lean_object* x_555; 
lean_dec(x_424);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_1);
x_554 = lean_ctor_get(x_496, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_496, 1);
lean_inc(x_555);
lean_dec(x_496);
x_43 = x_554;
x_44 = x_555;
goto block_47;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_494);
lean_dec(x_424);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_556 = lean_ctor_get(x_492, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_557 = x_492;
} else {
 lean_dec_ref(x_492);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_432);
lean_ctor_set(x_558, 1, x_556);
return x_558;
}
}
else
{
lean_object* x_559; lean_object* x_560; 
lean_dec(x_424);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_559 = lean_ctor_get(x_492, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_492, 1);
lean_inc(x_560);
lean_dec(x_492);
x_43 = x_559;
x_44 = x_560;
goto block_47;
}
}
}
else
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_561 = lean_ctor_get(x_61, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_61, 1);
lean_inc(x_562);
lean_dec(x_61);
x_43 = x_561;
x_44 = x_562;
goto block_47;
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
x_563 = lean_ctor_get(x_58, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_58, 1);
lean_inc(x_564);
lean_dec(x_58);
x_43 = x_563;
x_44 = x_564;
goto block_47;
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_565 = lean_ctor_get(x_54, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_54, 1);
lean_inc(x_566);
lean_dec(x_54);
x_43 = x_565;
x_44 = x_566;
goto block_47;
}
block_42:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_mk_string_unchecked("Meta", 4, 4);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("acyclic", 7, 7);
x_16 = l_Lean_Name_mkStr3(x_13, x_14, x_15);
lean_inc(x_16);
x_17 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_16, x_5, x_6, x_7, x_8, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(x_12);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_mk_string_unchecked("failed with\n", 12, 12);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_Exception_toMessageData(x_10);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_16, x_33, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(x_12);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
block_47:
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isInterrupt(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Exception_isRuntime(x_43);
x_10 = x_43;
x_11 = x_44;
x_12 = x_46;
goto block_42;
}
else
{
x_10 = x_43;
x_11 = x_44;
x_12 = x_45;
goto block_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_whnfD(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_48 = lean_mk_string_unchecked("Meta", 4, 4);
x_49 = lean_mk_string_unchecked("Tactic", 6, 6);
x_50 = lean_mk_string_unchecked("acyclic", 7, 7);
x_51 = l_Lean_Name_mkStr3(x_48, x_49, x_50);
lean_inc(x_51);
x_52 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_51, x_3, x_4, x_5, x_6, x_13);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_55;
goto block_47;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_52, 1);
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
x_59 = lean_mk_string_unchecked("type: ", 6, 6);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
lean_inc(x_12);
x_61 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_60);
x_62 = lean_mk_string_unchecked("", 0, 0);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_51, x_64, x_3, x_4, x_5, x_6, x_57);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_66;
goto block_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_dec(x_52);
x_68 = lean_mk_string_unchecked("type: ", 6, 6);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
lean_inc(x_12);
x_70 = l_Lean_MessageData_ofExpr(x_12);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_51, x_74, x_3, x_4, x_5, x_6, x_67);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_76;
goto block_47;
}
}
block_47:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_mk_string_unchecked("Eq", 2, 2);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Expr_isAppOfArity(x_12, x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(x_23);
if (lean_is_scalar(x_14)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_14;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_26 = l_Lean_Expr_appFn_x21(x_12);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_28);
lean_inc(x_27);
x_29 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(x_27, x_28, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_27);
lean_inc(x_28);
x_33 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(x_28, x_27, x_15, x_16, x_17, x_18, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_37 = l_Lean_Meta_mkEqSymm(x_1, x_15, x_16, x_17, x_18, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MVarId_acyclic_go(x_2, x_38, x_28, x_27, x_15, x_16, x_17, x_18, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_46 = l_Lean_MVarId_acyclic_go(x_2, x_1, x_27, x_28, x_15, x_16, x_17, x_18, x_45);
return x_46;
}
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_11);
if (x_77 == 0)
{
return x_11;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_11, 0);
x_79 = lean_ctor_get(x_11, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_11);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_8);
if (x_81 == 0)
{
return x_8;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_8, 0);
x_83 = lean_ctor_get(x_8, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_8);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_acyclic(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_856_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("acyclic", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("MVarId", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_8);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_3);
x_19 = lean_mk_string_unchecked("Acyclic", 7, 7);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(856u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_6);
x_26 = l_Lean_registerTraceClass(x_5, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_856_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
