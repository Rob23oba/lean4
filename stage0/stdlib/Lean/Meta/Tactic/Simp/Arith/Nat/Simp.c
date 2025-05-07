// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Simp
// Imports: Lean.Meta.Tactic.Simp.Arith.Util Lean.Meta.Tactic.Simp.Arith.Nat.Basic
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
uint8_t l___private_Init_Data_Nat_Linear_0__Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear___hyg_120_(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Nat_Linear_Poly_norm(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_withAbstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
extern lean_object* l_Lean_reflBoolTrue;
lean_object* l_Nat_Linear_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_9 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = l_Nat_Linear_ExprCnstr_toPoly(x_1);
x_14 = l_Nat_Linear_PolyCnstr_norm(x_13);
x_15 = l_Nat_Linear_PolyCnstr_isUnsat(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Nat_Linear_PolyCnstr_isValid(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Nat_Linear_PolyCnstr_toExpr(x_14);
lean_inc(x_17);
x_18 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(x_3, x_17, x_4, x_5, x_6, x_7, x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_61; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_61 = lean_expr_eqv(x_20, x_10);
if (x_61 == 0)
{
lean_free_object(x_18);
goto block_60;
}
else
{
if (x_16 == 0)
{
lean_object* x_62; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
lean_ctor_set(x_18, 0, x_62);
return x_18;
}
else
{
lean_free_object(x_18);
goto block_60;
}
}
block_60:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_mk_string_unchecked("Linear", 6, 6);
x_26 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_27 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
x_28 = l_Lean_Name_mkStr4(x_2, x_25, x_26, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_32 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_17);
x_33 = l_Lean_reflBoolTrue;
x_34 = l_Lean_mkApp4(x_30, x_24, x_31, x_32, x_33);
lean_inc(x_20);
x_35 = l_Lean_mkPropEq(x_10, x_20);
x_36 = l_Lean_Meta_mkExpectedPropHint(x_34, x_35);
if (lean_is_scalar(x_12)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_12;
}
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_22, 0, x_38);
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_mk_string_unchecked("Linear", 6, 6);
x_42 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_43 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
x_44 = l_Lean_Name_mkStr4(x_2, x_41, x_42, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_const___override(x_44, x_45);
x_47 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_48 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_17);
x_49 = l_Lean_reflBoolTrue;
x_50 = l_Lean_mkApp4(x_46, x_39, x_47, x_48, x_49);
lean_inc(x_20);
x_51 = l_Lean_mkPropEq(x_10, x_20);
x_52 = l_Lean_Meta_mkExpectedPropHint(x_50, x_51);
if (lean_is_scalar(x_12)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_12;
}
lean_ctor_set(x_53, 0, x_20);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_40);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_89; 
x_63 = lean_ctor_get(x_18, 0);
x_64 = lean_ctor_get(x_18, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_18);
x_89 = lean_expr_eqv(x_63, x_10);
if (x_89 == 0)
{
goto block_88;
}
else
{
if (x_16 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_64);
return x_91;
}
else
{
goto block_88;
}
}
block_88:
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_mk_string_unchecked("Linear", 6, 6);
x_70 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_71 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
x_72 = l_Lean_Name_mkStr4(x_2, x_69, x_70, x_71);
x_73 = lean_box(0);
x_74 = l_Lean_Expr_const___override(x_72, x_73);
x_75 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_76 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_17);
x_77 = l_Lean_reflBoolTrue;
x_78 = l_Lean_mkApp4(x_74, x_66, x_75, x_76, x_77);
lean_inc(x_63);
x_79 = l_Lean_mkPropEq(x_10, x_63);
x_80 = l_Lean_Meta_mkExpectedPropHint(x_78, x_79);
if (lean_is_scalar(x_12)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_12;
}
lean_ctor_set(x_81, 0, x_63);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_68)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_68;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_ctor_get(x_65, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_86 = x_65;
} else {
 lean_dec_ref(x_65);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_14);
x_92 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_mk_string_unchecked("True", 4, 4);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = lean_box(0);
x_98 = l_Lean_Expr_const___override(x_96, x_97);
x_99 = lean_mk_string_unchecked("Linear", 6, 6);
x_100 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_101 = lean_mk_string_unchecked("eq_true_of_isValid", 18, 18);
x_102 = l_Lean_Name_mkStr4(x_2, x_99, x_100, x_101);
x_103 = l_Lean_Expr_const___override(x_102, x_97);
x_104 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_105 = l_Lean_reflBoolTrue;
x_106 = l_Lean_mkApp3(x_103, x_94, x_104, x_105);
lean_inc(x_98);
x_107 = l_Lean_mkPropEq(x_10, x_98);
x_108 = l_Lean_Meta_mkExpectedPropHint(x_106, x_107);
if (lean_is_scalar(x_12)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_12;
}
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_92);
x_113 = lean_mk_string_unchecked("True", 4, 4);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = lean_box(0);
x_116 = l_Lean_Expr_const___override(x_114, x_115);
x_117 = lean_mk_string_unchecked("Linear", 6, 6);
x_118 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_119 = lean_mk_string_unchecked("eq_true_of_isValid", 18, 18);
x_120 = l_Lean_Name_mkStr4(x_2, x_117, x_118, x_119);
x_121 = l_Lean_Expr_const___override(x_120, x_115);
x_122 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_123 = l_Lean_reflBoolTrue;
x_124 = l_Lean_mkApp3(x_121, x_111, x_122, x_123);
lean_inc(x_116);
x_125 = l_Lean_mkPropEq(x_10, x_116);
x_126 = l_Lean_Meta_mkExpectedPropHint(x_124, x_125);
if (lean_is_scalar(x_12)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_12;
}
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_112);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_92);
if (x_130 == 0)
{
return x_92;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_92, 0);
x_132 = lean_ctor_get(x_92, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_92);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_14);
x_134 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_mk_string_unchecked("False", 5, 5);
x_138 = l_Lean_Name_mkStr1(x_137);
x_139 = lean_box(0);
x_140 = l_Lean_Expr_const___override(x_138, x_139);
x_141 = lean_mk_string_unchecked("Linear", 6, 6);
x_142 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_143 = lean_mk_string_unchecked("eq_false_of_isUnsat", 19, 19);
x_144 = l_Lean_Name_mkStr4(x_2, x_141, x_142, x_143);
x_145 = l_Lean_Expr_const___override(x_144, x_139);
x_146 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_147 = l_Lean_reflBoolTrue;
x_148 = l_Lean_mkApp3(x_145, x_136, x_146, x_147);
lean_inc(x_140);
x_149 = l_Lean_mkPropEq(x_10, x_140);
x_150 = l_Lean_Meta_mkExpectedPropHint(x_148, x_149);
if (lean_is_scalar(x_12)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_12;
}
lean_ctor_set(x_151, 0, x_140);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_134, 0, x_152);
return x_134;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_153 = lean_ctor_get(x_134, 0);
x_154 = lean_ctor_get(x_134, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_134);
x_155 = lean_mk_string_unchecked("False", 5, 5);
x_156 = l_Lean_Name_mkStr1(x_155);
x_157 = lean_box(0);
x_158 = l_Lean_Expr_const___override(x_156, x_157);
x_159 = lean_mk_string_unchecked("Linear", 6, 6);
x_160 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_161 = lean_mk_string_unchecked("eq_false_of_isUnsat", 19, 19);
x_162 = l_Lean_Name_mkStr4(x_2, x_159, x_160, x_161);
x_163 = l_Lean_Expr_const___override(x_162, x_157);
x_164 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
x_165 = l_Lean_reflBoolTrue;
x_166 = l_Lean_mkApp3(x_163, x_153, x_164, x_165);
lean_inc(x_158);
x_167 = l_Lean_mkPropEq(x_10, x_158);
x_168 = l_Lean_Meta_mkExpectedPropHint(x_166, x_167);
if (lean_is_scalar(x_12)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_12;
}
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_154);
return x_171;
}
}
else
{
uint8_t x_172; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_134);
if (x_172 == 0)
{
return x_134;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_134, 0);
x_174 = lean_ctor_get(x_134, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_134);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___lam__0), 8, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Name_mkStr1(x_19);
x_22 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_18, x_21, x_20, x_2, x_3, x_4, x_5, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Expr_getAppNumArgs(x_1);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_sub(x_20, x_19);
x_23 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_24 = lean_nat_sub(x_22, x_2);
lean_dec(x_22);
x_25 = lean_nat_sub(x_23, x_2);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l_Lean_Expr_const___override(x_5, x_26);
x_28 = l_Lean_Expr_getRevArg_x21(x_1, x_24);
x_29 = l_Lean_Expr_getRevArg_x21(x_1, x_25);
x_30 = l_Lean_mkAppB(x_27, x_28, x_29);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_31; 
lean_dec(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
uint8_t x_32; 
lean_free_object(x_4);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_mk_string_unchecked("Eq", 2, 2);
x_38 = lean_mk_string_unchecked("trans", 5, 5);
x_39 = l_Lean_Name_mkStr2(x_37, x_38);
x_40 = l_Lean_levelOne;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
x_42 = l_Lean_Expr_const___override(x_39, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Expr_sort___override(x_43);
lean_inc(x_35);
x_45 = l_Lean_mkApp6(x_42, x_44, x_3, x_15, x_35, x_30, x_36);
lean_ctor_set(x_33, 1, x_45);
return x_16;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_mk_string_unchecked("Eq", 2, 2);
x_49 = lean_mk_string_unchecked("trans", 5, 5);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_levelOne;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_26);
x_53 = l_Lean_Expr_const___override(x_50, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Expr_sort___override(x_54);
lean_inc(x_46);
x_56 = l_Lean_mkApp6(x_53, x_55, x_3, x_15, x_46, x_30, x_47);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_18, 0, x_57);
return x_16;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec(x_18);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_mk_string_unchecked("Eq", 2, 2);
x_63 = lean_mk_string_unchecked("trans", 5, 5);
x_64 = l_Lean_Name_mkStr2(x_62, x_63);
x_65 = l_Lean_levelOne;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_26);
x_67 = l_Lean_Expr_const___override(x_64, x_66);
x_68 = lean_box(0);
x_69 = l_Lean_Expr_sort___override(x_68);
lean_inc(x_59);
x_70 = l_Lean_mkApp6(x_67, x_69, x_3, x_15, x_59, x_30, x_60);
if (lean_is_scalar(x_61)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_16, 0, x_72);
return x_16;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_unsigned_to_nat(2u);
x_76 = l_Lean_Expr_getAppNumArgs(x_1);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_sub(x_76, x_75);
x_79 = lean_nat_sub(x_76, x_77);
lean_dec(x_76);
x_80 = lean_nat_sub(x_78, x_2);
lean_dec(x_78);
x_81 = lean_nat_sub(x_79, x_2);
lean_dec(x_79);
x_82 = lean_box(0);
x_83 = l_Lean_Expr_const___override(x_5, x_82);
x_84 = l_Lean_Expr_getRevArg_x21(x_1, x_80);
x_85 = l_Lean_Expr_getRevArg_x21(x_1, x_81);
x_86 = l_Lean_mkAppB(x_83, x_84, x_85);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_3);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_15);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_4, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_4);
lean_ctor_set(x_88, 1, x_74);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_4);
x_89 = lean_ctor_get(x_73, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_90 = x_73;
} else {
 lean_dec_ref(x_73);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_93 = x_89;
} else {
 lean_dec_ref(x_89);
 x_93 = lean_box(0);
}
x_94 = lean_mk_string_unchecked("Eq", 2, 2);
x_95 = lean_mk_string_unchecked("trans", 5, 5);
x_96 = l_Lean_Name_mkStr2(x_94, x_95);
x_97 = l_Lean_levelOne;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_82);
x_99 = l_Lean_Expr_const___override(x_96, x_98);
x_100 = lean_box(0);
x_101 = l_Lean_Expr_sort___override(x_100);
lean_inc(x_91);
x_102 = l_Lean_mkApp6(x_99, x_101, x_3, x_15, x_91, x_86, x_92);
if (lean_is_scalar(x_93)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_93;
}
lean_ctor_set(x_103, 0, x_91);
lean_ctor_set(x_103, 1, x_102);
if (lean_is_scalar(x_90)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_90;
}
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_74);
return x_105;
}
}
}
else
{
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_4, 0);
lean_inc(x_106);
lean_dec(x_4);
lean_inc(x_106);
x_107 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(x_106, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_unsigned_to_nat(2u);
x_112 = l_Lean_Expr_getAppNumArgs(x_1);
x_113 = lean_unsigned_to_nat(3u);
x_114 = lean_nat_sub(x_112, x_111);
x_115 = lean_nat_sub(x_112, x_113);
lean_dec(x_112);
x_116 = lean_nat_sub(x_114, x_2);
lean_dec(x_114);
x_117 = lean_nat_sub(x_115, x_2);
lean_dec(x_115);
x_118 = lean_box(0);
x_119 = l_Lean_Expr_const___override(x_5, x_118);
x_120 = l_Lean_Expr_getRevArg_x21(x_1, x_116);
x_121 = l_Lean_Expr_getRevArg_x21(x_1, x_117);
x_122 = l_Lean_mkAppB(x_119, x_120, x_121);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_106);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_110)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_110;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_109);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_126 = lean_ctor_get(x_108, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_127 = x_108;
} else {
 lean_dec_ref(x_108);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_mk_string_unchecked("Eq", 2, 2);
x_132 = lean_mk_string_unchecked("trans", 5, 5);
x_133 = l_Lean_Name_mkStr2(x_131, x_132);
x_134 = l_Lean_levelOne;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_118);
x_136 = l_Lean_Expr_const___override(x_133, x_135);
x_137 = lean_box(0);
x_138 = l_Lean_Expr_sort___override(x_137);
lean_inc(x_128);
x_139 = l_Lean_mkApp6(x_136, x_138, x_3, x_106, x_128, x_122, x_129);
if (lean_is_scalar(x_130)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_130;
}
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_139);
if (lean_is_scalar(x_127)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_127;
}
lean_ctor_set(x_141, 0, x_140);
if (lean_is_scalar(x_110)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_110;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_109);
return x_142;
}
}
else
{
lean_dec(x_106);
lean_dec(x_5);
lean_dec(x_3);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Not", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_12);
x_13 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_12, x_3, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_25 = l_Lean_Expr_cleanupAnnotations(x_14);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec(x_29);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = lean_mk_string_unchecked("GT", 2, 2);
x_36 = lean_mk_string_unchecked("gt", 2, 2);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
x_38 = l_Lean_Expr_isConstOf(x_34, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_mk_string_unchecked("LT", 2, 2);
x_40 = lean_mk_string_unchecked("lt", 2, 2);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_Expr_isConstOf(x_34, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_mk_string_unchecked("GE", 2, 2);
x_44 = lean_mk_string_unchecked("ge", 2, 2);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = l_Lean_Expr_isConstOf(x_34, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_mk_string_unchecked("LE", 2, 2);
x_48 = lean_mk_string_unchecked("le", 2, 2);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = l_Lean_Expr_isConstOf(x_34, x_49);
lean_dec(x_49);
lean_dec(x_34);
if (x_50 == 0)
{
lean_dec(x_33);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_51);
x_52 = l_Lean_Name_mkStr1(x_51);
x_53 = l_Lean_Expr_isConstOf(x_33, x_52);
lean_dec(x_52);
lean_dec(x_33);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_16, x_17, x_54, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_56 = lean_unsigned_to_nat(3u);
x_57 = l_Lean_Expr_getAppNumArgs(x_12);
x_58 = lean_nat_sub(x_57, x_56);
x_59 = lean_nat_sub(x_58, x_9);
lean_dec(x_58);
x_60 = l_Lean_Expr_getRevArg_x21(x_12, x_59);
x_61 = l_Lean_mkNatLit(x_9);
x_62 = l_Lean_mkNatAdd(x_60, x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_sub(x_57, x_63);
lean_dec(x_57);
x_65 = lean_nat_sub(x_64, x_9);
lean_dec(x_64);
x_66 = l_Lean_Expr_getRevArg_x21(x_12, x_65);
x_67 = l_Lean_mkNatLE(x_62, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_mk_string_unchecked("not_le_eq", 9, 9);
x_70 = l_Lean_Name_mkStr2(x_51, x_69);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_68, x_70, x_71, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_34);
x_73 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_73);
x_74 = l_Lean_Name_mkStr1(x_73);
x_75 = l_Lean_Expr_isConstOf(x_33, x_74);
lean_dec(x_74);
lean_dec(x_33);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
x_76 = lean_box(0);
x_77 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_16, x_17, x_76, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_78 = lean_unsigned_to_nat(2u);
x_79 = l_Lean_Expr_getAppNumArgs(x_12);
x_80 = lean_nat_sub(x_79, x_78);
x_81 = lean_nat_sub(x_80, x_9);
lean_dec(x_80);
x_82 = l_Lean_Expr_getRevArg_x21(x_12, x_81);
x_83 = l_Lean_mkNatLit(x_9);
x_84 = l_Lean_mkNatAdd(x_82, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_sub(x_79, x_85);
lean_dec(x_79);
x_87 = lean_nat_sub(x_86, x_9);
lean_dec(x_86);
x_88 = l_Lean_Expr_getRevArg_x21(x_12, x_87);
x_89 = l_Lean_mkNatLE(x_84, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
x_92 = l_Lean_Name_mkStr2(x_73, x_91);
x_93 = lean_box(0);
x_94 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_90, x_92, x_93, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_34);
x_95 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_95);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = l_Lean_Expr_isConstOf(x_33, x_96);
lean_dec(x_96);
lean_dec(x_33);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_95);
x_98 = lean_box(0);
x_99 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_16, x_17, x_98, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_100 = lean_unsigned_to_nat(3u);
x_101 = l_Lean_Expr_getAppNumArgs(x_12);
x_102 = lean_nat_sub(x_101, x_100);
x_103 = lean_nat_sub(x_102, x_9);
lean_dec(x_102);
x_104 = l_Lean_Expr_getRevArg_x21(x_12, x_103);
x_105 = lean_unsigned_to_nat(2u);
x_106 = lean_nat_sub(x_101, x_105);
lean_dec(x_101);
x_107 = lean_nat_sub(x_106, x_9);
lean_dec(x_106);
x_108 = l_Lean_Expr_getRevArg_x21(x_12, x_107);
x_109 = l_Lean_mkNatLE(x_104, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
x_112 = l_Lean_Name_mkStr2(x_95, x_111);
x_113 = lean_box(0);
x_114 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_110, x_112, x_113, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_34);
x_115 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_115);
x_116 = l_Lean_Name_mkStr1(x_115);
x_117 = l_Lean_Expr_isConstOf(x_33, x_116);
lean_dec(x_116);
lean_dec(x_33);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_115);
x_118 = lean_box(0);
x_119 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_16, x_17, x_118, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_unsigned_to_nat(2u);
x_121 = l_Lean_Expr_getAppNumArgs(x_12);
x_122 = lean_nat_sub(x_121, x_120);
x_123 = lean_nat_sub(x_122, x_9);
lean_dec(x_122);
x_124 = l_Lean_Expr_getRevArg_x21(x_12, x_123);
x_125 = lean_unsigned_to_nat(3u);
x_126 = lean_nat_sub(x_121, x_125);
lean_dec(x_121);
x_127 = lean_nat_sub(x_126, x_9);
lean_dec(x_126);
x_128 = l_Lean_Expr_getRevArg_x21(x_12, x_127);
x_129 = l_Lean_mkNatLE(x_124, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
x_132 = l_Lean_Name_mkStr2(x_115, x_131);
x_133 = lean_box(0);
x_134 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_130, x_132, x_133, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_12);
return x_134;
}
}
}
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_12, x_9, x_1, x_16, x_17, x_22, x_18, x_19, x_20, x_21, x_15);
lean_dec(x_12);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = l_Nat_Linear_Expr_toPoly(x_12);
x_15 = l_Nat_Linear_Poly_norm(x_14);
x_16 = l_Nat_Linear_Poly_toExpr(x_15);
x_17 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear___hyg_120_(x_16, x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_7);
lean_inc(x_13);
x_18 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_13, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_mk_string_unchecked("Nat", 3, 3);
x_22 = lean_mk_string_unchecked("Linear", 6, 6);
x_23 = lean_mk_string_unchecked("Expr", 4, 4);
x_24 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
lean_inc(x_16);
x_25 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_13, x_16, x_20);
lean_dec(x_13);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_12);
x_32 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_16);
x_33 = l_Lean_reflBoolTrue;
x_34 = l_Lean_mkApp4(x_30, x_19, x_31, x_32, x_33);
lean_inc(x_27);
x_35 = l_Lean_mkNatEq(x_1, x_27);
x_36 = l_Lean_Meta_mkExpectedPropHint(x_34, x_35);
lean_ctor_set(x_9, 1, x_36);
lean_ctor_set(x_9, 0, x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_25, 0, x_37);
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_const___override(x_40, x_41);
x_43 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_12);
x_44 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_16);
x_45 = l_Lean_reflBoolTrue;
x_46 = l_Lean_mkApp4(x_42, x_19, x_43, x_44, x_45);
lean_inc(x_38);
x_47 = l_Lean_mkNatEq(x_1, x_38);
x_48 = l_Lean_Meta_mkExpectedPropHint(x_46, x_47);
lean_ctor_set(x_9, 1, x_48);
lean_ctor_set(x_9, 0, x_38);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_16);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_16);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_7, 0, x_55);
return x_7;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_7, 1);
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = l_Nat_Linear_Expr_toPoly(x_57);
x_60 = l_Nat_Linear_Poly_norm(x_59);
x_61 = l_Nat_Linear_Poly_toExpr(x_60);
x_62 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear___hyg_120_(x_61, x_57);
if (x_62 == 0)
{
lean_object* x_63; 
lean_free_object(x_7);
lean_inc(x_58);
x_63 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_58, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_mk_string_unchecked("Nat", 3, 3);
x_67 = lean_mk_string_unchecked("Linear", 6, 6);
x_68 = lean_mk_string_unchecked("Expr", 4, 4);
x_69 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
lean_inc(x_61);
x_70 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_58, x_61, x_65);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Name_mkStr4(x_66, x_67, x_68, x_69);
x_75 = lean_box(0);
x_76 = l_Lean_Expr_const___override(x_74, x_75);
x_77 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_57);
x_78 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_61);
x_79 = l_Lean_reflBoolTrue;
x_80 = l_Lean_mkApp4(x_76, x_64, x_77, x_78, x_79);
lean_inc(x_71);
x_81 = l_Lean_mkNatEq(x_1, x_71);
x_82 = l_Lean_Meta_mkExpectedPropHint(x_80, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_1);
x_86 = lean_ctor_get(x_63, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_88 = x_63;
} else {
 lean_dec_ref(x_63);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
lean_ctor_set(x_7, 0, x_90);
return x_7;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_91 = lean_ctor_get(x_7, 0);
x_92 = lean_ctor_get(x_7, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_7);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = l_Nat_Linear_Expr_toPoly(x_93);
x_97 = l_Nat_Linear_Poly_norm(x_96);
x_98 = l_Nat_Linear_Poly_toExpr(x_97);
x_99 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear___hyg_120_(x_98, x_93);
if (x_99 == 0)
{
lean_object* x_100; 
lean_inc(x_94);
x_100 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_94, x_2, x_3, x_4, x_5, x_92);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_mk_string_unchecked("Nat", 3, 3);
x_104 = lean_mk_string_unchecked("Linear", 6, 6);
x_105 = lean_mk_string_unchecked("Expr", 4, 4);
x_106 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
lean_inc(x_98);
x_107 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_94, x_98, x_102);
lean_dec(x_94);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = l_Lean_Name_mkStr4(x_103, x_104, x_105, x_106);
x_112 = lean_box(0);
x_113 = l_Lean_Expr_const___override(x_111, x_112);
x_114 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_93);
x_115 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_98);
x_116 = l_Lean_reflBoolTrue;
x_117 = l_Lean_mkApp4(x_113, x_101, x_114, x_115, x_116);
lean_inc(x_108);
x_118 = l_Lean_mkNatEq(x_1, x_108);
x_119 = l_Lean_Meta_mkExpectedPropHint(x_117, x_118);
if (lean_is_scalar(x_95)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_95;
}
lean_ctor_set(x_120, 0, x_108);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
if (lean_is_scalar(x_110)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_110;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_109);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_123 = lean_ctor_get(x_100, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_100, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_125 = x_100;
} else {
 lean_dec_ref(x_100);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_92);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_7);
if (x_129 == 0)
{
return x_7;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_7, 0);
x_131 = lean_ctor_get(x_7, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_7);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
