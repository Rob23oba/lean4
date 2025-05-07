// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: Init.Data.Int.OfNat Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Simp.Arith.Nat.Basic Lean.Meta.Tactic.Grind.Arith.Cutsat.Foreign Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
lean_object* l_Lean_Meta_isInstHMulNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toIntEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toOfNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isInstLENat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr_go(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr___lam__0(lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_isInstHDivInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHDivNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toIntLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("Int", 3, 3);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("Expr", 4, 4);
x_6 = lean_mk_string_unchecked("num", 3, 3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = l_Lean_mkNatLit(x_2);
x_11 = l_Lean_Expr_app___override(x_9, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("Int", 3, 3);
x_14 = lean_mk_string_unchecked("OfNat", 5, 5);
x_15 = lean_mk_string_unchecked("Expr", 4, 4);
x_16 = lean_mk_string_unchecked("var", 3, 3);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_const___override(x_17, x_18);
x_20 = l_Lean_mkNatLit(x_12);
x_21 = l_Lean_Expr_app___override(x_19, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("Int", 3, 3);
x_25 = lean_mk_string_unchecked("OfNat", 5, 5);
x_26 = lean_mk_string_unchecked("Expr", 4, 4);
x_27 = lean_mk_string_unchecked("add", 3, 3);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = l_Int_OfNat_toExpr(x_22);
x_32 = l_Int_OfNat_toExpr(x_23);
x_33 = l_Lean_mkAppB(x_30, x_31, x_32);
return x_33;
}
case 3:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("Int", 3, 3);
x_37 = lean_mk_string_unchecked("OfNat", 5, 5);
x_38 = lean_mk_string_unchecked("Expr", 4, 4);
x_39 = lean_mk_string_unchecked("mul", 3, 3);
x_40 = l_Lean_Name_mkStr4(x_36, x_37, x_38, x_39);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_const___override(x_40, x_41);
x_43 = l_Int_OfNat_toExpr(x_34);
x_44 = l_Int_OfNat_toExpr(x_35);
x_45 = l_Lean_mkAppB(x_42, x_43, x_44);
return x_45;
}
case 4:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_mk_string_unchecked("Int", 3, 3);
x_49 = lean_mk_string_unchecked("OfNat", 5, 5);
x_50 = lean_mk_string_unchecked("Expr", 4, 4);
x_51 = lean_mk_string_unchecked("div", 3, 3);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_55 = l_Int_OfNat_toExpr(x_46);
x_56 = l_Int_OfNat_toExpr(x_47);
x_57 = l_Lean_mkAppB(x_54, x_55, x_56);
return x_57;
}
default: 
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_mk_string_unchecked("Int", 3, 3);
x_61 = lean_mk_string_unchecked("OfNat", 5, 5);
x_62 = lean_mk_string_unchecked("Expr", 4, 4);
x_63 = lean_mk_string_unchecked("mod", 3, 3);
x_64 = l_Lean_Name_mkStr4(x_60, x_61, x_62, x_63);
x_65 = lean_box(0);
x_66 = l_Lean_Expr_const___override(x_64, x_65);
x_67 = l_Int_OfNat_toExpr(x_58);
x_68 = l_Int_OfNat_toExpr(x_59);
x_69 = l_Lean_mkAppB(x_66, x_67, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_OfNat_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_alloc_closure((void*)(l_Int_OfNat_instToExprExpr___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("Expr", 4, 4);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_nat_to_int(x_3);
x_5 = l_Lean_mkIntLit(x_4);
lean_dec(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_instInhabitedExpr;
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = l_outOfBounds___redArg(x_7);
x_11 = l_Lean_mkIntNatCast(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_PersistentArray_get_x21___redArg(x_7, x_1, x_6);
lean_dec(x_6);
x_13 = l_Lean_mkIntNatCast(x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_14);
x_17 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_15);
x_18 = l_Lean_mkIntAdd(x_16, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_21 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_19);
x_22 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_20);
x_23 = l_Lean_mkIntMul(x_21, x_22);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_26 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_24);
x_27 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_25);
x_28 = l_Lean_mkIntDiv(x_26, x_27);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_1);
x_31 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_29);
x_32 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_30);
x_33 = l_Lean_mkIntMod(x_31, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_2);
x_6 = l_Lean_Meta_Grind_shareCommon___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_1, x_2, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_OfNat_Expr_denoteAsIntExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toOfNatExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_1);
x_35 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_cleanupAnnotations(x_36);
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_inc(x_38);
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_38);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_40);
x_42 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_inc(x_42);
x_44 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_45 = lean_mk_string_unchecked("OfNat", 5, 5);
x_46 = lean_mk_string_unchecked("ofNat", 5, 5);
x_47 = l_Lean_Name_mkStr2(x_45, x_46);
x_48 = l_Lean_Expr_isConstOf(x_44, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isApp(x_44);
if (x_49 == 0)
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Expr_appFnCleanup___redArg(x_44);
x_51 = l_Lean_Expr_isApp(x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_50);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_dec(x_42);
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_58 = lean_mk_string_unchecked("HMod", 4, 4);
x_59 = lean_mk_string_unchecked("hMod", 4, 4);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
x_61 = l_Lean_Expr_isConstOf(x_57, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_mk_string_unchecked("HDiv", 4, 4);
x_63 = lean_mk_string_unchecked("hDiv", 4, 4);
x_64 = l_Lean_Name_mkStr2(x_62, x_63);
x_65 = l_Lean_Expr_isConstOf(x_57, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_mk_string_unchecked("HMul", 4, 4);
x_67 = lean_mk_string_unchecked("hMul", 4, 4);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = l_Lean_Expr_isConstOf(x_57, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_mk_string_unchecked("HAdd", 4, 4);
x_71 = lean_mk_string_unchecked("hAdd", 4, 4);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
x_73 = l_Lean_Expr_isConstOf(x_57, x_72);
lean_dec(x_72);
lean_dec(x_57);
if (x_73 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = l_Lean_Meta_isInstHAddNat(x_56, x_6, x_7, x_8, x_9, x_37);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_55);
lean_dec(x_54);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_77;
goto block_34;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_79 = l_Int_OfNat_toOfNatExpr(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
x_83 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_ctor_set_tag(x_79, 2);
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_83, 0, x_79);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_83, 0);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_83);
lean_ctor_set_tag(x_79, 2);
lean_ctor_set(x_79, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_free_object(x_79);
lean_dec(x_81);
return x_83;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 0);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_79);
x_91 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_92);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_dec(x_89);
return x_91;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_79;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_57);
x_97 = l_Lean_Meta_isInstHMulNat___redArg(x_56, x_7, x_37);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_55);
lean_dec(x_54);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_100;
goto block_34;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_102 = l_Int_OfNat_toOfNatExpr(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
x_106 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_105);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_106, 0);
lean_ctor_set_tag(x_102, 3);
lean_ctor_set(x_102, 1, x_108);
lean_ctor_set(x_106, 0, x_102);
return x_106;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_106, 0);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_106);
lean_ctor_set_tag(x_102, 3);
lean_ctor_set(x_102, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_free_object(x_102);
lean_dec(x_104);
return x_106;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_102, 0);
x_113 = lean_ctor_get(x_102, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_102);
x_114 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_115);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_dec(x_112);
return x_114;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_102;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_57);
x_120 = l_Lean_Meta_isInstHDivNat___redArg(x_56, x_7, x_37);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_55);
lean_dec(x_54);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_123;
goto block_34;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_125 = l_Int_OfNat_toOfNatExpr(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
x_129 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_ctor_set_tag(x_125, 4);
lean_ctor_set(x_125, 1, x_131);
lean_ctor_set(x_129, 0, x_125);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
lean_ctor_set_tag(x_125, 4);
lean_ctor_set(x_125, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
lean_free_object(x_125);
lean_dec(x_127);
return x_129;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_125, 0);
x_136 = lean_ctor_get(x_125, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_125);
x_137 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_138);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
else
{
lean_dec(x_135);
return x_137;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_125;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_57);
x_143 = l_Lean_Meta_isInstHModNat___redArg(x_56, x_7, x_37);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_55);
lean_dec(x_54);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_146;
goto block_34;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_1);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_148 = l_Int_OfNat_toOfNatExpr(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_147);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_148, 1);
x_152 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_151);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_152, 0);
lean_ctor_set_tag(x_148, 5);
lean_ctor_set(x_148, 1, x_154);
lean_ctor_set(x_152, 0, x_148);
return x_152;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_152, 0);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_152);
lean_ctor_set_tag(x_148, 5);
lean_ctor_set(x_148, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
lean_free_object(x_148);
lean_dec(x_150);
return x_152;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_148, 0);
x_159 = lean_ctor_get(x_148, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_148);
x_160 = l_Int_OfNat_toOfNatExpr(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_161);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_dec(x_158);
return x_160;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_148;
}
}
}
}
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_166 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_168;
goto block_34;
}
else
{
uint8_t x_169; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_166);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_166, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_167);
if (x_171 == 0)
{
lean_ctor_set_tag(x_167, 0);
return x_166;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_167, 0);
lean_inc(x_172);
lean_dec(x_167);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_166, 0, x_173);
return x_166;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_166, 1);
lean_inc(x_174);
lean_dec(x_166);
x_175 = lean_ctor_get(x_167, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_176 = x_167;
} else {
 lean_dec_ref(x_167);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_176;
 lean_ctor_set_tag(x_177, 0);
}
lean_ctor_set(x_177, 0, x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_174);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_166);
if (x_179 == 0)
{
return x_166;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_166, 0);
x_181 = lean_ctor_get(x_166, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_166);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
}
}
block_34:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_11, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntLe_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("LE", 2, 2);
x_25 = lean_mk_string_unchecked("le", 2, 2);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = l_Lean_Expr_isConstOf(x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
if (x_27 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Meta_isInstLENat___redArg(x_28, x_7, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
x_44 = l_Int_OfNat_toOfNatExpr(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_41);
x_54 = !lean_is_exclusive(x_44);
if (x_54 == 0)
{
return x_44;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_44, 0);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_44);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_inc(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = lean_mk_string_unchecked("Dvd", 3, 3);
x_29 = lean_mk_string_unchecked("dvd", 3, 3);
x_30 = l_Lean_Name_mkStr2(x_28, x_29);
x_31 = l_Lean_Expr_isConstOf(x_27, x_30);
lean_dec(x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Meta_isInstDvdNat___redArg(x_32, x_7, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_Lean_Meta_getNatValue_x3f(x_43, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_19);
lean_dec(x_2);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*7 + 10);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_15 = x_50;
goto block_18;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_56);
lean_ctor_set(x_47, 0, x_55);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Meta_Grind_reportIssue(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_15 = x_61;
goto block_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = l_Lean_indentExpr(x_1);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_mk_string_unchecked("", 0, 0);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_Grind_reportIssue(x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_15 = x_71;
goto block_18;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_44, 1);
lean_inc(x_72);
lean_dec(x_44);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_45, 0);
x_75 = lean_ctor_get(x_19, 1);
lean_inc(x_75);
lean_dec(x_19);
x_76 = l_Int_OfNat_toOfNatExpr(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_45, 0, x_79);
lean_ctor_set(x_76, 0, x_45);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_45, 0, x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_45);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_45);
lean_dec(x_74);
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
return x_76;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_76);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_45, 0);
lean_inc(x_88);
lean_dec(x_45);
x_89 = lean_ctor_get(x_19, 1);
lean_inc(x_89);
lean_dec(x_19);
x_90 = l_Int_OfNat_toOfNatExpr(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_91);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_88);
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_99 = x_90;
} else {
 lean_dec_ref(x_90);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_44);
if (x_101 == 0)
{
return x_44;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_44, 0);
x_103 = lean_ctor_get(x_44, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_44);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Int_OfNat_toOfNatExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Int_OfNat_toOfNatExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_97; uint8_t x_98; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_97 = l_Lean_Expr_cleanupAnnotations(x_16);
x_98 = l_Lean_Expr_isApp(x_97);
if (x_98 == 0)
{
lean_dec(x_97);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_inc(x_97);
x_99 = l_Lean_Expr_appFnCleanup___redArg(x_97);
x_100 = l_Lean_Expr_isApp(x_99);
if (x_100 == 0)
{
lean_dec(x_99);
lean_dec(x_97);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_inc(x_99);
x_101 = l_Lean_Expr_appFnCleanup___redArg(x_99);
x_102 = l_Lean_Expr_isApp(x_101);
if (x_102 == 0)
{
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_97);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_inc(x_101);
x_103 = l_Lean_Expr_appFnCleanup___redArg(x_101);
x_104 = lean_mk_string_unchecked("OfNat", 5, 5);
x_105 = lean_mk_string_unchecked("ofNat", 5, 5);
x_106 = l_Lean_Name_mkStr2(x_104, x_105);
x_107 = l_Lean_Expr_isConstOf(x_103, x_106);
lean_dec(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Expr_isApp(x_103);
if (x_108 == 0)
{
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_97);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = l_Lean_Expr_appFnCleanup___redArg(x_103);
x_110 = l_Lean_Expr_isApp(x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_97);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Expr_appFnCleanup___redArg(x_109);
x_112 = l_Lean_Expr_isApp(x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_97);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_dec(x_101);
x_116 = l_Lean_Expr_appFnCleanup___redArg(x_111);
x_117 = lean_mk_string_unchecked("HMod", 4, 4);
x_118 = lean_mk_string_unchecked("hMod", 4, 4);
x_119 = l_Lean_Name_mkStr2(x_117, x_118);
x_120 = l_Lean_Expr_isConstOf(x_116, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_mk_string_unchecked("HDiv", 4, 4);
x_122 = lean_mk_string_unchecked("hDiv", 4, 4);
x_123 = l_Lean_Name_mkStr2(x_121, x_122);
x_124 = l_Lean_Expr_isConstOf(x_116, x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_mk_string_unchecked("HMul", 4, 4);
x_126 = lean_mk_string_unchecked("hMul", 4, 4);
x_127 = l_Lean_Name_mkStr2(x_125, x_126);
x_128 = l_Lean_Expr_isConstOf(x_116, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_mk_string_unchecked("HAdd", 4, 4);
x_130 = lean_mk_string_unchecked("hAdd", 4, 4);
x_131 = l_Lean_Name_mkStr2(x_129, x_130);
x_132 = l_Lean_Expr_isConstOf(x_116, x_131);
lean_dec(x_131);
lean_dec(x_116);
if (x_132 == 0)
{
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_96;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_1);
x_133 = l_Lean_Meta_isInstHAddInt___redArg(x_115, x_7, x_17);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
uint8_t x_136; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_133, 0);
lean_dec(x_137);
x_138 = lean_box(0);
lean_ctor_set(x_133, 0, x_138);
return x_133;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
lean_dec(x_133);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_133, 1);
lean_inc(x_142);
lean_dec(x_133);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_143 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_143;
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_143, 1);
x_147 = lean_ctor_get(x_143, 0);
lean_dec(x_147);
x_148 = lean_ctor_get(x_144, 0);
lean_inc(x_148);
lean_dec(x_144);
x_149 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_146);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_dec(x_148);
lean_free_object(x_143);
return x_149;
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_149);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_149, 0);
lean_dec(x_152);
x_153 = !lean_is_exclusive(x_150);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_150, 0);
lean_ctor_set_tag(x_143, 2);
lean_ctor_set(x_143, 1, x_154);
lean_ctor_set(x_143, 0, x_148);
lean_ctor_set(x_150, 0, x_143);
return x_149;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
lean_dec(x_150);
lean_ctor_set_tag(x_143, 2);
lean_ctor_set(x_143, 1, x_155);
lean_ctor_set(x_143, 0, x_148);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_143);
lean_ctor_set(x_149, 0, x_156);
return x_149;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_149, 1);
lean_inc(x_157);
lean_dec(x_149);
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_159 = x_150;
} else {
 lean_dec_ref(x_150);
 x_159 = lean_box(0);
}
lean_ctor_set_tag(x_143, 2);
lean_ctor_set(x_143, 1, x_158);
lean_ctor_set(x_143, 0, x_148);
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_143);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_157);
return x_161;
}
}
}
else
{
lean_dec(x_148);
lean_free_object(x_143);
return x_149;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_143, 1);
lean_inc(x_162);
lean_dec(x_143);
x_163 = lean_ctor_get(x_144, 0);
lean_inc(x_163);
lean_dec(x_144);
x_164 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_dec(x_163);
return x_164;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_169 = x_165;
} else {
 lean_dec_ref(x_165);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_168);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
}
else
{
lean_dec(x_163);
return x_164;
}
}
}
}
else
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_143;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_116);
lean_dec(x_1);
x_173 = l_Lean_Meta_isInstHMulInt___redArg(x_115, x_7, x_17);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_173);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_173, 0);
lean_dec(x_177);
x_178 = lean_box(0);
lean_ctor_set(x_173, 0, x_178);
return x_173;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_173, 1);
lean_inc(x_182);
lean_dec(x_173);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_183 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_183;
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_183, 1);
x_187 = lean_ctor_get(x_183, 0);
lean_dec(x_187);
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
lean_dec(x_184);
x_189 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
lean_dec(x_188);
lean_free_object(x_183);
return x_189;
}
else
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_189);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_189, 0);
lean_dec(x_192);
x_193 = !lean_is_exclusive(x_190);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_190, 0);
lean_ctor_set_tag(x_183, 3);
lean_ctor_set(x_183, 1, x_194);
lean_ctor_set(x_183, 0, x_188);
lean_ctor_set(x_190, 0, x_183);
return x_189;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_190, 0);
lean_inc(x_195);
lean_dec(x_190);
lean_ctor_set_tag(x_183, 3);
lean_ctor_set(x_183, 1, x_195);
lean_ctor_set(x_183, 0, x_188);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_183);
lean_ctor_set(x_189, 0, x_196);
return x_189;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_189, 1);
lean_inc(x_197);
lean_dec(x_189);
x_198 = lean_ctor_get(x_190, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_199 = x_190;
} else {
 lean_dec_ref(x_190);
 x_199 = lean_box(0);
}
lean_ctor_set_tag(x_183, 3);
lean_ctor_set(x_183, 1, x_198);
lean_ctor_set(x_183, 0, x_188);
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_183);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
}
}
else
{
lean_dec(x_188);
lean_free_object(x_183);
return x_189;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
lean_dec(x_183);
x_203 = lean_ctor_get(x_184, 0);
lean_inc(x_203);
lean_dec(x_184);
x_204 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_dec(x_203);
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_209 = x_205;
} else {
 lean_dec_ref(x_205);
 x_209 = lean_box(0);
}
x_210 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_208);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_210);
if (lean_is_scalar(x_207)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_207;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_206);
return x_212;
}
}
else
{
lean_dec(x_203);
return x_204;
}
}
}
}
else
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_183;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_dec(x_116);
lean_dec(x_1);
x_213 = l_Lean_Meta_isInstHDivInt___redArg(x_115, x_7, x_17);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_unbox(x_214);
lean_dec(x_214);
if (x_215 == 0)
{
uint8_t x_216; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_216 = !lean_is_exclusive(x_213);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_213, 0);
lean_dec(x_217);
x_218 = lean_box(0);
lean_ctor_set(x_213, 0, x_218);
return x_213;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
lean_dec(x_213);
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_213, 1);
lean_inc(x_222);
lean_dec(x_213);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_223 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_obj_tag(x_224) == 0)
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_223;
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_223, 1);
x_227 = lean_ctor_get(x_223, 0);
lean_dec(x_227);
x_228 = lean_ctor_get(x_224, 0);
lean_inc(x_228);
lean_dec(x_224);
x_229 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_dec(x_228);
lean_free_object(x_223);
return x_229;
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_229, 0);
lean_dec(x_232);
x_233 = !lean_is_exclusive(x_230);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_230, 0);
lean_ctor_set_tag(x_223, 4);
lean_ctor_set(x_223, 1, x_234);
lean_ctor_set(x_223, 0, x_228);
lean_ctor_set(x_230, 0, x_223);
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_230, 0);
lean_inc(x_235);
lean_dec(x_230);
lean_ctor_set_tag(x_223, 4);
lean_ctor_set(x_223, 1, x_235);
lean_ctor_set(x_223, 0, x_228);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_223);
lean_ctor_set(x_229, 0, x_236);
return x_229;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_229, 1);
lean_inc(x_237);
lean_dec(x_229);
x_238 = lean_ctor_get(x_230, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_239 = x_230;
} else {
 lean_dec_ref(x_230);
 x_239 = lean_box(0);
}
lean_ctor_set_tag(x_223, 4);
lean_ctor_set(x_223, 1, x_238);
lean_ctor_set(x_223, 0, x_228);
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_223);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_237);
return x_241;
}
}
}
else
{
lean_dec(x_228);
lean_free_object(x_223);
return x_229;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_223, 1);
lean_inc(x_242);
lean_dec(x_223);
x_243 = lean_ctor_get(x_224, 0);
lean_inc(x_243);
lean_dec(x_224);
x_244 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_dec(x_243);
return x_244;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_249 = x_245;
} else {
 lean_dec_ref(x_245);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_248);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
if (lean_is_scalar(x_247)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_247;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_246);
return x_252;
}
}
else
{
lean_dec(x_243);
return x_244;
}
}
}
}
else
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_223;
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_116);
lean_dec(x_1);
x_253 = l_Lean_Meta_isInstHModInt___redArg(x_115, x_7, x_17);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
uint8_t x_256; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_253, 0);
lean_dec(x_257);
x_258 = lean_box(0);
lean_ctor_set(x_253, 0, x_258);
return x_253;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_253, 1);
lean_inc(x_259);
lean_dec(x_253);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_253, 1);
lean_inc(x_262);
lean_dec(x_253);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_263 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_obj_tag(x_264) == 0)
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_263;
}
else
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_263, 1);
x_267 = lean_ctor_get(x_263, 0);
lean_dec(x_267);
x_268 = lean_ctor_get(x_264, 0);
lean_inc(x_268);
lean_dec(x_264);
x_269 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_266);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_dec(x_268);
lean_free_object(x_263);
return x_269;
}
else
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_269, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_270);
if (x_273 == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_270, 0);
lean_ctor_set_tag(x_263, 5);
lean_ctor_set(x_263, 1, x_274);
lean_ctor_set(x_263, 0, x_268);
lean_ctor_set(x_270, 0, x_263);
return x_269;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_270, 0);
lean_inc(x_275);
lean_dec(x_270);
lean_ctor_set_tag(x_263, 5);
lean_ctor_set(x_263, 1, x_275);
lean_ctor_set(x_263, 0, x_268);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_263);
lean_ctor_set(x_269, 0, x_276);
return x_269;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_269, 1);
lean_inc(x_277);
lean_dec(x_269);
x_278 = lean_ctor_get(x_270, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_279 = x_270;
} else {
 lean_dec_ref(x_270);
 x_279 = lean_box(0);
}
lean_ctor_set_tag(x_263, 5);
lean_ctor_set(x_263, 1, x_278);
lean_ctor_set(x_263, 0, x_268);
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_263);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_277);
return x_281;
}
}
}
else
{
lean_dec(x_268);
lean_free_object(x_263);
return x_269;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_263, 1);
lean_inc(x_282);
lean_dec(x_263);
x_283 = lean_ctor_get(x_264, 0);
lean_inc(x_283);
lean_dec(x_264);
x_284 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_282);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_dec(x_283);
return x_284;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
x_290 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_290, 0, x_283);
lean_ctor_set(x_290, 1, x_288);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_290);
if (lean_is_scalar(x_287)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_287;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_286);
return x_292;
}
}
else
{
lean_dec(x_283);
return x_284;
}
}
}
}
else
{
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_263;
}
}
}
}
}
}
}
else
{
lean_object* x_293; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_293 = l_Lean_Meta_getIntValue_x3f(x_1, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_6);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
if (lean_obj_tag(x_294) == 0)
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_293);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_293, 0);
lean_dec(x_296);
x_297 = lean_box(0);
lean_ctor_set(x_293, 0, x_297);
return x_293;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_dec(x_293);
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_293);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_293, 0);
lean_dec(x_302);
x_303 = !lean_is_exclusive(x_294);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_304 = lean_ctor_get(x_294, 0);
x_305 = lean_unsigned_to_nat(0u);
x_306 = lean_nat_to_int(x_305);
x_307 = lean_int_dec_le(x_306, x_304);
lean_dec(x_306);
if (x_307 == 0)
{
lean_object* x_308; 
lean_free_object(x_294);
lean_dec(x_304);
x_308 = lean_box(0);
lean_ctor_set(x_293, 0, x_308);
return x_293;
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = l_Int_toNat(x_304);
lean_dec(x_304);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_294, 0, x_310);
return x_293;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_311 = lean_ctor_get(x_294, 0);
lean_inc(x_311);
lean_dec(x_294);
x_312 = lean_unsigned_to_nat(0u);
x_313 = lean_nat_to_int(x_312);
x_314 = lean_int_dec_le(x_313, x_311);
lean_dec(x_313);
if (x_314 == 0)
{
lean_object* x_315; 
lean_dec(x_311);
x_315 = lean_box(0);
lean_ctor_set(x_293, 0, x_315);
return x_293;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = l_Int_toNat(x_311);
lean_dec(x_311);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_293, 0, x_318);
return x_293;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_319 = lean_ctor_get(x_293, 1);
lean_inc(x_319);
lean_dec(x_293);
x_320 = lean_ctor_get(x_294, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_321 = x_294;
} else {
 lean_dec_ref(x_294);
 x_321 = lean_box(0);
}
x_322 = lean_unsigned_to_nat(0u);
x_323 = lean_nat_to_int(x_322);
x_324 = lean_int_dec_le(x_323, x_320);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_321);
lean_dec(x_320);
x_325 = lean_box(0);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_319);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = l_Int_toNat(x_320);
lean_dec(x_320);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_327);
if (lean_is_scalar(x_321)) {
 x_329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_329 = x_321;
}
lean_ctor_set(x_329, 0, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_319);
return x_330;
}
}
}
}
else
{
uint8_t x_331; 
x_331 = !lean_is_exclusive(x_293);
if (x_331 == 0)
{
return x_293;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_293, 0);
x_333 = lean_ctor_get(x_293, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_293);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_96:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_23, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Expr_cleanupAnnotations(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_inc(x_30);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_32);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_37 = lean_mk_string_unchecked("NatCast", 7, 7);
x_38 = lean_mk_string_unchecked("natCast", 7, 7);
x_39 = l_Lean_Name_mkStr2(x_37, x_38);
x_40 = l_Lean_Expr_isConstOf(x_36, x_39);
lean_dec(x_39);
lean_dec(x_36);
if (x_40 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Lean_Expr_cleanupAnnotations(x_41);
x_43 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = l_Lean_Expr_isConstOf(x_42, x_44);
lean_dec(x_44);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_46 = lean_box(0);
lean_ctor_set(x_26, 0, x_46);
return x_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_26);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_47, x_48, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_29);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_26, 0);
x_64 = lean_ctor_get(x_26, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_26);
x_65 = l_Lean_Expr_cleanupAnnotations(x_63);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec(x_65);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_64;
goto block_14;
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
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_64;
goto block_14;
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
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_64;
goto block_14;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_72 = lean_mk_string_unchecked("NatCast", 7, 7);
x_73 = lean_mk_string_unchecked("natCast", 7, 7);
x_74 = l_Lean_Name_mkStr2(x_72, x_73);
x_75 = l_Lean_Expr_isConstOf(x_71, x_74);
lean_dec(x_74);
lean_dec(x_71);
if (x_75 == 0)
{
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_64;
goto block_14;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_dec(x_67);
x_77 = l_Lean_Expr_cleanupAnnotations(x_76);
x_78 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
x_79 = l_Lean_Name_mkStr1(x_78);
x_80 = l_Lean_Expr_isConstOf(x_77, x_79);
lean_dec(x_79);
lean_dec(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_65);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_64);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_dec(x_65);
x_84 = lean_box(0);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_83, x_84, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_64);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_86);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_94 = x_85;
} else {
 lean_dec_ref(x_85);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("runtime", 7, 7);
x_4 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("NatCast", 7, 7);
x_12 = lean_mk_string_unchecked("natCast", 7, 7);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_isAppOf(x_1, x_13);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_14, x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_8, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 10);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_30 = lean_ctor_get(x_8, 11);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_32 = lean_ctor_get(x_8, 12);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_19);
lean_ctor_set(x_33, 4, x_15);
lean_ctor_set(x_33, 5, x_23);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_25);
lean_ctor_set(x_33, 8, x_26);
lean_ctor_set(x_33, 9, x_27);
lean_ctor_set(x_33, 10, x_28);
lean_ctor_set(x_33, 11, x_30);
lean_ctor_set(x_33, 12, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*13, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*13 + 1, x_31);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_42);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_44);
x_54 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_52, x_44, x_5, x_53);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_56, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_to_int(x_61);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_62);
lean_inc(x_59);
lean_ctor_set_tag(x_54, 3);
lean_ctor_set(x_54, 1, x_59);
lean_ctor_set(x_54, 0, x_35);
x_63 = l_Int_Linear_Expr_norm(x_54);
lean_dec(x_54);
lean_ctor_set_tag(x_50, 4);
lean_ctor_set(x_50, 1, x_59);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_45, 1, x_50);
lean_ctor_set(x_45, 0, x_63);
x_64 = lean_grind_cutsat_assert_le(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_60);
return x_64;
}
else
{
uint8_t x_65; 
lean_free_object(x_54);
lean_free_object(x_50);
lean_free_object(x_45);
lean_free_object(x_35);
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_58);
if (x_65 == 0)
{
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_58, 0);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_58);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_54, 0);
x_70 = lean_ctor_get(x_54, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_54);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_69, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_to_int(x_74);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_75);
lean_inc(x_72);
x_76 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Int_Linear_Expr_norm(x_76);
lean_dec(x_76);
lean_ctor_set_tag(x_50, 4);
lean_ctor_set(x_50, 1, x_72);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_45, 1, x_50);
lean_ctor_set(x_45, 0, x_77);
x_78 = lean_grind_cutsat_assert_le(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_73);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_50);
lean_free_object(x_45);
lean_free_object(x_35);
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_81 = x_71;
} else {
 lean_dec_ref(x_71);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_50, 0);
x_84 = lean_ctor_get(x_50, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_50);
lean_inc(x_44);
x_85 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_83, x_44, x_5, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_89 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_86, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_to_int(x_92);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_93);
lean_inc(x_90);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(3, 2, 0);
} else {
 x_94 = x_88;
 lean_ctor_set_tag(x_94, 3);
}
lean_ctor_set(x_94, 0, x_35);
lean_ctor_set(x_94, 1, x_90);
x_95 = l_Int_Linear_Expr_norm(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_96, 0, x_44);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_45, 1, x_96);
lean_ctor_set(x_45, 0, x_95);
x_97 = lean_grind_cutsat_assert_le(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_91);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_88);
lean_free_object(x_45);
lean_free_object(x_35);
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_89, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_100 = x_89;
} else {
 lean_dec_ref(x_89);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_45, 0);
x_103 = lean_ctor_get(x_45, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_45);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_103);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
lean_inc(x_44);
x_109 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_106, x_44, x_5, x_107);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_110, x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_nat_to_int(x_116);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_117);
lean_inc(x_114);
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(3, 2, 0);
} else {
 x_118 = x_112;
 lean_ctor_set_tag(x_118, 3);
}
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_118, 1, x_114);
x_119 = l_Int_Linear_Expr_norm(x_118);
lean_dec(x_118);
if (lean_is_scalar(x_108)) {
 x_120 = lean_alloc_ctor(4, 2, 0);
} else {
 x_120 = x_108;
 lean_ctor_set_tag(x_120, 4);
}
lean_ctor_set(x_120, 0, x_44);
lean_ctor_set(x_120, 1, x_114);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_grind_cutsat_assert_le(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_115);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_112);
lean_dec(x_108);
lean_free_object(x_35);
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_113, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_113, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_125 = x_113;
} else {
 lean_dec_ref(x_113);
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
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_127 = lean_ctor_get(x_35, 0);
lean_inc(x_127);
lean_dec(x_35);
x_128 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_42);
lean_dec(x_1);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_box(0);
x_133 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(x_132, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_130);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
lean_inc(x_127);
x_137 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_134, x_127, x_5, x_135);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_138, x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_139);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_nat_to_int(x_144);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
lean_inc(x_142);
if (lean_is_scalar(x_140)) {
 x_147 = lean_alloc_ctor(3, 2, 0);
} else {
 x_147 = x_140;
 lean_ctor_set_tag(x_147, 3);
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
x_148 = l_Int_Linear_Expr_norm(x_147);
lean_dec(x_147);
if (lean_is_scalar(x_136)) {
 x_149 = lean_alloc_ctor(4, 2, 0);
} else {
 x_149 = x_136;
 lean_ctor_set_tag(x_149, 4);
}
lean_ctor_set(x_149, 0, x_127);
lean_ctor_set(x_149, 1, x_142);
if (lean_is_scalar(x_131)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_131;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_grind_cutsat_assert_le(x_150, x_2, x_3, x_4, x_5, x_6, x_7, x_33, x_9, x_143);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_140);
lean_dec(x_136);
lean_dec(x_131);
lean_dec(x_127);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_ctor_get(x_141, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_141, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_154 = x_141;
} else {
 lean_dec_ref(x_141);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_34);
if (x_156 == 0)
{
return x_34;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_34, 0);
x_158 = lean_ctor_get(x_34, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_34);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_10);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_8, 5);
lean_inc(x_162);
lean_dec(x_8);
x_163 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_162, x_10);
return x_163;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_1);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_inc(x_16);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_18);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = lean_mk_string_unchecked("NatCast", 7, 7);
x_24 = lean_mk_string_unchecked("natCast", 7, 7);
x_25 = l_Lean_Name_mkStr2(x_23, x_24);
x_26 = l_Lean_Expr_isConstOf(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_26 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_Expr_cleanupAnnotations(x_27);
x_29 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Expr_isConstOf(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_11);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_36, 4);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0(lean_box(0), x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_34);
x_41 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_38, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_neg(x_46);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_to_int(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_inc(x_2);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_2);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_43);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_grind_cutsat_assert_le(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
return x_42;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_42);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
lean_ctor_set(x_34, 0, x_61);
return x_34;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_34);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_dec(x_16);
x_65 = lean_ctor_get(x_62, 4);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0(lean_box(0), x_65, x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_64, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_to_int(x_71);
x_73 = lean_int_neg(x_72);
lean_dec(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_to_int(x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_inc(x_2);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_2);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_69);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
x_80 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_grind_cutsat_assert_le(x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_68, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_85 = x_68;
} else {
 lean_dec_ref(x_68);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_63);
return x_88;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Foreign(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_OfNat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Foreign(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_OfNat_instToExprExpr = _init_l_Int_OfNat_instToExprExpr();
lean_mark_persistent(l_Int_OfNat_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
