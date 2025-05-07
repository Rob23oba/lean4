// Lean compiler output
// Module: Lean.Meta.LitValues
// Imports: Lean.Meta.Basic Init.Control.Option
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
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_BitVec_toNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint16_t lean_uint16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_consumeMData(x_1);
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getRawNatValue_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getRawNatValue_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_Expr_cleanupAnnotations(x_9);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = lean_mk_string_unchecked("OfNat", 5, 5);
x_23 = lean_mk_string_unchecked("ofNat", 5, 5);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Meta_whnfD(x_26, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Expr_getAppFn(x_29);
x_32 = l_Lean_Expr_isConstOf(x_31, x_2);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = lean_box(0);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
x_35 = l_Lean_Expr_consumeMData(x_34);
lean_dec(x_34);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_27);
lean_dec(x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Expr_bvar___override(x_36);
x_38 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_37, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_37);
return x_38;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_27);
lean_dec(x_29);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Expr_fvar___override(x_39);
x_41 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_40, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_40);
return x_41;
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_27);
lean_dec(x_29);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_Expr_mvar___override(x_42);
x_44 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_43, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_43);
return x_44;
}
case 3:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_27);
lean_dec(x_29);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = l_Lean_Expr_sort___override(x_45);
x_47 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_46, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_46);
return x_47;
}
case 4:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_27);
lean_dec(x_29);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_50 = l_Lean_Expr_const___override(x_48, x_49);
x_51 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_50, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_50);
return x_51;
}
case 5:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_27);
lean_dec(x_29);
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_dec(x_35);
x_54 = l_Lean_Expr_app___override(x_52, x_53);
x_55 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_54, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_54);
return x_55;
}
case 6:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_27);
lean_dec(x_29);
x_56 = lean_ctor_get(x_35, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_35, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_35, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_60 = l_Lean_Expr_lam___override(x_56, x_57, x_58, x_59);
x_61 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_60, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_60);
return x_61;
}
case 7:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_27);
lean_dec(x_29);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_35, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_66 = l_Lean_Expr_forallE___override(x_62, x_63, x_64, x_65);
x_67 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_66, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_66);
return x_67;
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_27);
lean_dec(x_29);
x_68 = lean_ctor_get(x_35, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_35, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_35, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_35, 3);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_35, sizeof(void*)*4 + 8);
lean_dec(x_35);
x_73 = l_Lean_Expr_letE___override(x_68, x_69, x_70, x_71, x_72);
x_74 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_73, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_73);
return x_74;
}
case 9:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 0);
lean_inc(x_75);
lean_dec(x_35);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_29);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_78);
lean_ctor_set(x_27, 0, x_75);
return x_27;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_29);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_27, 0, x_81);
return x_27;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_27);
lean_dec(x_29);
x_82 = l_Lean_Expr_lit___override(x_75);
x_83 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_82, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_82);
return x_83;
}
}
case 10:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_27);
lean_dec(x_29);
x_84 = lean_ctor_get(x_35, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_35, 1);
lean_inc(x_85);
lean_dec(x_35);
x_86 = l_Lean_Expr_mdata___override(x_84, x_85);
x_87 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_86, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_86);
return x_87;
}
default: 
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_27);
lean_dec(x_29);
x_88 = lean_ctor_get(x_35, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_35, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_35, 2);
lean_inc(x_90);
lean_dec(x_35);
x_91 = l_Lean_Expr_proj___override(x_88, x_89, x_90);
x_92 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_91, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_27, 0);
x_94 = lean_ctor_get(x_27, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_27);
x_95 = l_Lean_Expr_getAppFn(x_93);
x_96 = l_Lean_Expr_isConstOf(x_95, x_2);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_17, 1);
lean_inc(x_99);
lean_dec(x_17);
x_100 = l_Lean_Expr_consumeMData(x_99);
lean_dec(x_99);
switch (lean_obj_tag(x_100)) {
case 0:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Expr_bvar___override(x_101);
x_103 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_102, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_102);
return x_103;
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
lean_dec(x_100);
x_105 = l_Lean_Expr_fvar___override(x_104);
x_106 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_105, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_105);
return x_106;
}
case 2:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_93);
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
lean_dec(x_100);
x_108 = l_Lean_Expr_mvar___override(x_107);
x_109 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_108, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_108);
return x_109;
}
case 3:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_93);
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
lean_dec(x_100);
x_111 = l_Lean_Expr_sort___override(x_110);
x_112 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_111, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_111);
return x_112;
}
case 4:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_93);
x_113 = lean_ctor_get(x_100, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_dec(x_100);
x_115 = l_Lean_Expr_const___override(x_113, x_114);
x_116 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_115, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_115);
return x_116;
}
case 5:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_93);
x_117 = lean_ctor_get(x_100, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
lean_dec(x_100);
x_119 = l_Lean_Expr_app___override(x_117, x_118);
x_120 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_119, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_119);
return x_120;
}
case 6:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_93);
x_121 = lean_ctor_get(x_100, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_100, 2);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_100, sizeof(void*)*3 + 8);
lean_dec(x_100);
x_125 = l_Lean_Expr_lam___override(x_121, x_122, x_123, x_124);
x_126 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_125, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_125);
return x_126;
}
case 7:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_93);
x_127 = lean_ctor_get(x_100, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_100, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_100, 2);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_100, sizeof(void*)*3 + 8);
lean_dec(x_100);
x_131 = l_Lean_Expr_forallE___override(x_127, x_128, x_129, x_130);
x_132 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_131, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_131);
return x_132;
}
case 8:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_93);
x_133 = lean_ctor_get(x_100, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_100, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_100, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_100, 3);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_100, sizeof(void*)*4 + 8);
lean_dec(x_100);
x_138 = l_Lean_Expr_letE___override(x_133, x_134, x_135, x_136, x_137);
x_139 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_138, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_138);
return x_139;
}
case 9:
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_100, 0);
lean_inc(x_140);
lean_dec(x_100);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_93);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_142;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_94);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_93);
x_146 = l_Lean_Expr_lit___override(x_140);
x_147 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_146, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_146);
return x_147;
}
}
case 10:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_93);
x_148 = lean_ctor_get(x_100, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_100, 1);
lean_inc(x_149);
lean_dec(x_100);
x_150 = l_Lean_Expr_mdata___override(x_148, x_149);
x_151 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_150, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_150);
return x_151;
}
default: 
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_93);
x_152 = lean_ctor_get(x_100, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_100, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_100, 2);
lean_inc(x_154);
lean_dec(x_100);
x_155 = l_Lean_Expr_proj___override(x_152, x_153, x_154);
x_156 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_155, x_3, x_4, x_5, x_6, x_94);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_155);
return x_156;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = !lean_is_exclusive(x_27);
if (x_157 == 0)
{
return x_27;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_27, 0);
x_159 = lean_ctor_get(x_27, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_27);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
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
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getOfNatValue_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getOfNatValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_consumeMData(x_1);
x_8 = l_Lean_Meta_getRawNatValue_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("Nat", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Meta_getOfNatValue_x3f(x_7, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getNatValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("Int", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_19 = l_Lean_Expr_cleanupAnnotations(x_13);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_18;
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_18;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = lean_mk_string_unchecked("Neg", 3, 3);
x_27 = lean_mk_string_unchecked("neg", 3, 3);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = l_Lean_Expr_isConstOf(x_25, x_28);
lean_dec(x_28);
lean_dec(x_25);
if (x_29 == 0)
{
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = l_Lean_Meta_getOfNatValue_x3f(x_30, x_8, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_31, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_int_neg(x_44);
lean_dec(x_44);
lean_ctor_set(x_32, 0, x_45);
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_nat_to_int(x_48);
x_50 = lean_int_neg(x_49);
lean_dec(x_49);
lean_ctor_set(x_32, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_32, 0);
lean_inc(x_52);
lean_dec(x_32);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_54 = x_31;
} else {
 lean_dec_ref(x_31);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_nat_to_int(x_55);
x_57 = lean_int_neg(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
if (lean_is_scalar(x_54)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_54;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_31);
if (x_60 == 0)
{
return x_31;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_31, 0);
x_62 = lean_ctor_get(x_31, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_31);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_10, 0);
x_67 = lean_ctor_get(x_9, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_nat_to_int(x_68);
lean_ctor_set(x_10, 0, x_69);
return x_9;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_10, 0);
x_71 = lean_ctor_get(x_9, 1);
lean_inc(x_71);
lean_dec(x_9);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_nat_to_int(x_72);
lean_ctor_set(x_10, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_10);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_10, 0);
lean_inc(x_75);
lean_dec(x_10);
x_76 = lean_ctor_get(x_9, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_77 = x_9;
} else {
 lean_dec_ref(x_9);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_9);
if (x_82 == 0)
{
return x_9;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_9, 0);
x_84 = lean_ctor_get(x_9, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_9);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getIntValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_14);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_17 = lean_mk_string_unchecked("Char", 4, 4);
x_18 = lean_mk_string_unchecked("ofNat", 5, 5);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Meta_getNatValue_x3f(x_21, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
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
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; uint32_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = l_Char_ofNat(x_33);
lean_dec(x_33);
x_35 = lean_box_uint32(x_34);
lean_ctor_set(x_23, 0, x_35);
return x_22;
}
else
{
lean_object* x_36; uint32_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Char_ofNat(x_36);
lean_dec(x_36);
x_38 = lean_box_uint32(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = l_Char_ofNat(x_41);
lean_dec(x_41);
x_44 = lean_box_uint32(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCharValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getCharValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStringValue_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("Fin", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_whnfD(x_22, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_getNatValue_x3f(x_24, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_free_object(x_17);
lean_dec(x_20);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 1)
{
lean_object* x_40; 
lean_free_object(x_27);
lean_dec(x_37);
lean_free_object(x_17);
lean_dec(x_20);
x_40 = lean_box(0);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_37, x_41);
lean_dec(x_37);
x_43 = lean_nat_add(x_42, x_41);
lean_dec(x_42);
x_44 = lean_nat_mod(x_20, x_43);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_44);
lean_ctor_set(x_17, 0, x_43);
lean_ctor_set(x_27, 0, x_17);
return x_26;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
if (x_47 == 1)
{
lean_object* x_48; 
lean_dec(x_45);
lean_free_object(x_17);
lean_dec(x_20);
x_48 = lean_box(0);
lean_ctor_set(x_26, 0, x_48);
return x_26;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_45, x_49);
lean_dec(x_45);
x_51 = lean_nat_add(x_50, x_49);
lean_dec(x_50);
x_52 = lean_nat_mod(x_20, x_51);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_52);
lean_ctor_set(x_17, 0, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_17);
lean_ctor_set(x_26, 0, x_53);
return x_26;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_dec(x_26);
x_55 = lean_ctor_get(x_27, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_56 = x_27;
} else {
 lean_dec_ref(x_27);
 x_56 = lean_box(0);
}
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_eq(x_55, x_57);
if (x_58 == 1)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_55);
lean_free_object(x_17);
lean_dec(x_20);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_55, x_61);
lean_dec(x_55);
x_63 = lean_nat_add(x_62, x_61);
lean_dec(x_62);
x_64 = lean_nat_mod(x_20, x_63);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_64);
lean_ctor_set(x_17, 0, x_63);
if (lean_is_scalar(x_56)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_56;
}
lean_ctor_set(x_65, 0, x_17);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_free_object(x_17);
lean_dec(x_20);
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
return x_26;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_26, 0);
x_69 = lean_ctor_get(x_26, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_26);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_17);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_23);
if (x_71 == 0)
{
return x_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_23, 0);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_23);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = l_Lean_Expr_appArg_x21(x_76);
lean_dec(x_76);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_Lean_Meta_whnfD(x_77, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_getNatValue_x3f(x_79, x_2, x_3, x_4, x_5, x_80);
lean_dec(x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_75);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_nat_dec_eq(x_89, x_91);
if (x_92 == 1)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_75);
x_93 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_89, x_95);
lean_dec(x_89);
x_97 = lean_nat_add(x_96, x_95);
lean_dec(x_96);
x_98 = lean_nat_mod(x_75, x_97);
lean_dec(x_75);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_90)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_90;
}
lean_ctor_set(x_100, 0, x_99);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_87);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_75);
x_102 = lean_ctor_get(x_81, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_104 = x_81;
} else {
 lean_dec_ref(x_81);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_75);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_ctor_get(x_78, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_78, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_108 = x_78;
} else {
 lean_dec_ref(x_78);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_9);
if (x_110 == 0)
{
return x_9;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_9, 0);
x_112 = lean_ctor_get(x_9, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_9);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFinValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFinValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_147; uint8_t x_148; 
lean_inc(x_1);
x_58 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_147 = l_Lean_Expr_cleanupAnnotations(x_59);
x_148 = l_Lean_Expr_isApp(x_147);
if (x_148 == 0)
{
lean_dec(x_147);
x_61 = x_2;
x_62 = x_3;
x_63 = x_4;
x_64 = x_5;
goto block_146;
}
else
{
lean_object* x_149; uint8_t x_150; 
lean_inc(x_147);
x_149 = l_Lean_Expr_appFnCleanup___redArg(x_147);
x_150 = l_Lean_Expr_isApp(x_149);
if (x_150 == 0)
{
lean_dec(x_149);
lean_dec(x_147);
x_61 = x_2;
x_62 = x_3;
x_63 = x_4;
x_64 = x_5;
goto block_146;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
x_152 = l_Lean_Expr_appFnCleanup___redArg(x_149);
x_153 = lean_mk_string_unchecked("BitVec", 6, 6);
x_154 = lean_mk_string_unchecked("ofNat", 5, 5);
lean_inc(x_153);
x_155 = l_Lean_Name_mkStr2(x_153, x_154);
x_156 = l_Lean_Expr_isConstOf(x_152, x_155);
lean_dec(x_155);
if (x_156 == 0)
{
uint8_t x_157; 
lean_dec(x_147);
x_157 = l_Lean_Expr_isApp(x_152);
if (x_157 == 0)
{
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
x_61 = x_2;
x_62 = x_3;
x_63 = x_4;
x_64 = x_5;
goto block_146;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_inc(x_152);
x_158 = l_Lean_Expr_appFnCleanup___redArg(x_152);
x_159 = lean_mk_string_unchecked("ofNatLT", 7, 7);
x_160 = l_Lean_Name_mkStr2(x_153, x_159);
x_161 = l_Lean_Expr_isConstOf(x_158, x_160);
lean_dec(x_160);
lean_dec(x_158);
if (x_161 == 0)
{
lean_dec(x_152);
lean_dec(x_151);
x_61 = x_2;
x_62 = x_3;
x_63 = x_4;
x_64 = x_5;
goto block_146;
}
else
{
lean_object* x_162; 
lean_dec(x_1);
x_162 = lean_ctor_get(x_152, 1);
lean_inc(x_162);
lean_dec(x_152);
x_7 = x_162;
x_8 = x_151;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_60;
goto block_57;
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_1);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
lean_dec(x_147);
x_7 = x_151;
x_8 = x_163;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_60;
goto block_57;
}
}
}
block_57:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Meta_getNatValue_x3f(x_7, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Meta_getNatValue_x3f(x_8, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = l_BitVec_ofNat(x_23, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_25, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = l_BitVec_ofNat(x_23, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_23);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
x_45 = l_BitVec_ofNat(x_23, x_43);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_23);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
block_146:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_mk_string_unchecked("BitVec", 6, 6);
x_66 = l_Lean_Name_mkStr1(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_67 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_66, x_61, x_62, x_63, x_64, x_60);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_dec(x_67);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
x_80 = l_Lean_Expr_appArg_x21(x_79);
lean_dec(x_79);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_81 = l_Lean_Meta_whnfD(x_80, x_61, x_62, x_63, x_64, x_76);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_getNatValue_x3f(x_82, x_61, x_62, x_63, x_64, x_83);
lean_dec(x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_free_object(x_75);
lean_dec(x_78);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_84, 0, x_88);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_84);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_84, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_85);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_85, 0);
x_96 = l_BitVec_ofNat(x_95, x_78);
lean_dec(x_78);
lean_ctor_set(x_75, 1, x_96);
lean_ctor_set(x_75, 0, x_95);
lean_ctor_set(x_85, 0, x_75);
return x_84;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
lean_dec(x_85);
x_98 = l_BitVec_ofNat(x_97, x_78);
lean_dec(x_78);
lean_ctor_set(x_75, 1, x_98);
lean_ctor_set(x_75, 0, x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_75);
lean_ctor_set(x_84, 0, x_99);
return x_84;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
lean_dec(x_84);
x_101 = lean_ctor_get(x_85, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_102 = x_85;
} else {
 lean_dec_ref(x_85);
 x_102 = lean_box(0);
}
x_103 = l_BitVec_ofNat(x_101, x_78);
lean_dec(x_78);
lean_ctor_set(x_75, 1, x_103);
lean_ctor_set(x_75, 0, x_101);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_75);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_75);
lean_dec(x_78);
x_106 = !lean_is_exclusive(x_84);
if (x_106 == 0)
{
return x_84;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_84, 0);
x_108 = lean_ctor_get(x_84, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_84);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_75);
lean_dec(x_78);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_110 = !lean_is_exclusive(x_81);
if (x_110 == 0)
{
return x_81;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_81, 0);
x_112 = lean_ctor_get(x_81, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_81);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_75, 0);
x_115 = lean_ctor_get(x_75, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_75);
x_116 = l_Lean_Expr_appArg_x21(x_115);
lean_dec(x_115);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_117 = l_Lean_Meta_whnfD(x_116, x_61, x_62, x_63, x_64, x_76);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Meta_getNatValue_x3f(x_118, x_61, x_62, x_63, x_64, x_119);
lean_dec(x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_114);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_121, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
x_130 = l_BitVec_ofNat(x_128, x_114);
lean_dec(x_114);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_131);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_127;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_126);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_114);
x_134 = lean_ctor_get(x_120, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_136 = x_120;
} else {
 lean_dec_ref(x_120);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_114);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_138 = lean_ctor_get(x_117, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_117, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_140 = x_117;
} else {
 lean_dec_ref(x_117);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_142 = !lean_is_exclusive(x_67);
if (x_142 == 0)
{
return x_67;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_67, 0);
x_144 = lean_ctor_get(x_67, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_67);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getBitVecValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getBitVecValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("UInt8", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_uint8_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_uint8_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_box(x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_32 = x_9;
} else {
 lean_dec_ref(x_9);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_uint8_of_nat(x_33);
lean_dec(x_33);
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt8Value_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUInt8Value_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("UInt16", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint16_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_uint16_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint16_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_uint16_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_box(x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint16_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_32 = x_9;
} else {
 lean_dec_ref(x_9);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_uint16_of_nat(x_33);
lean_dec(x_33);
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt16Value_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUInt16Value_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("UInt32", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_uint32_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_box_uint32(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_uint32_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_box_uint32(x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_32 = x_9;
} else {
 lean_dec_ref(x_9);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_uint32_of_nat(x_33);
lean_dec(x_33);
x_35 = lean_box_uint32(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt32Value_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUInt32Value_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("UInt64", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Meta_getOfNatValue_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_uint64_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_box_uint64(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_uint64_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_box_uint64(x_27);
lean_ctor_set(x_10, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_32 = x_9;
} else {
 lean_dec_ref(x_9);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_uint64_of_nat(x_33);
lean_dec(x_33);
x_35 = lean_box_uint64(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUInt64Value_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUInt64Value_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_getNatValue_x3f(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_getIntValue_x3f(x_9, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_17 = l_Lean_Meta_getFinValue_x3f(x_9, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_20 = l_Lean_Meta_getBitVecValue_x3f(x_9, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_inc(x_9);
x_25 = l_Lean_Meta_getStringValue_x3f(x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_free_object(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_26 = l_Lean_Meta_getCharValue_x3f(x_9, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_29 = l_Lean_Meta_getUInt8Value_x3f(x_9, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_32 = l_Lean_Meta_getUInt16Value_x3f(x_9, x_2, x_3, x_4, x_5, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_35 = l_Lean_Meta_getUInt32Value_x3f(x_9, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_9);
x_38 = l_Lean_Meta_getUInt64Value_x3f(x_9, x_2, x_3, x_4, x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_free_object(x_7);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
lean_ctor_set(x_38, 0, x_9);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_38, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_unbox_uint64(x_46);
lean_dec(x_46);
x_48 = lean_uint64_to_nat(x_47);
x_49 = l_Lean_mkRawNatLit(x_48);
x_50 = lean_mk_string_unchecked("OfNat", 5, 5);
x_51 = lean_mk_string_unchecked("ofNat", 5, 5);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Level_ofNat(x_53);
x_55 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_55);
lean_ctor_set(x_7, 0, x_54);
x_56 = l_Lean_Expr_const___override(x_52, x_7);
x_57 = lean_mk_string_unchecked("UInt64", 6, 6);
lean_inc(x_57);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_55);
x_60 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_61 = l_Lean_Name_mkStr2(x_57, x_60);
x_62 = l_Lean_Expr_const___override(x_61, x_55);
lean_inc(x_49);
x_63 = l_Lean_Expr_app___override(x_62, x_49);
x_64 = l_Lean_mkApp3(x_56, x_59, x_49, x_63);
lean_ctor_set(x_38, 0, x_64);
return x_38;
}
else
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_dec(x_38);
x_66 = lean_ctor_get(x_39, 0);
lean_inc(x_66);
lean_dec(x_39);
x_67 = lean_unbox_uint64(x_66);
lean_dec(x_66);
x_68 = lean_uint64_to_nat(x_67);
x_69 = l_Lean_mkRawNatLit(x_68);
x_70 = lean_mk_string_unchecked("OfNat", 5, 5);
x_71 = lean_mk_string_unchecked("ofNat", 5, 5);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Level_ofNat(x_73);
x_75 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_75);
lean_ctor_set(x_7, 0, x_74);
x_76 = l_Lean_Expr_const___override(x_72, x_7);
x_77 = lean_mk_string_unchecked("UInt64", 6, 6);
lean_inc(x_77);
x_78 = l_Lean_Name_mkStr1(x_77);
x_79 = l_Lean_Expr_const___override(x_78, x_75);
x_80 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_81 = l_Lean_Name_mkStr2(x_77, x_80);
x_82 = l_Lean_Expr_const___override(x_81, x_75);
lean_inc(x_69);
x_83 = l_Lean_Expr_app___override(x_82, x_69);
x_84 = l_Lean_mkApp3(x_76, x_79, x_69, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_65);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_7);
lean_dec(x_9);
x_86 = !lean_is_exclusive(x_38);
if (x_86 == 0)
{
return x_38;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_38, 0);
x_88 = lean_ctor_get(x_38, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_38);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_35);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint32_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_91 = lean_ctor_get(x_35, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_36, 0);
lean_inc(x_92);
lean_dec(x_36);
x_93 = lean_unbox_uint32(x_92);
lean_dec(x_92);
x_94 = lean_uint32_to_nat(x_93);
x_95 = l_Lean_mkRawNatLit(x_94);
x_96 = lean_mk_string_unchecked("OfNat", 5, 5);
x_97 = lean_mk_string_unchecked("ofNat", 5, 5);
x_98 = l_Lean_Name_mkStr2(x_96, x_97);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Level_ofNat(x_99);
x_101 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_101);
lean_ctor_set(x_7, 0, x_100);
x_102 = l_Lean_Expr_const___override(x_98, x_7);
x_103 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_103);
x_104 = l_Lean_Name_mkStr1(x_103);
x_105 = l_Lean_Expr_const___override(x_104, x_101);
x_106 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_107 = l_Lean_Name_mkStr2(x_103, x_106);
x_108 = l_Lean_Expr_const___override(x_107, x_101);
lean_inc(x_95);
x_109 = l_Lean_Expr_app___override(x_108, x_95);
x_110 = l_Lean_mkApp3(x_102, x_105, x_95, x_109);
lean_ctor_set(x_35, 0, x_110);
return x_35;
}
else
{
lean_object* x_111; lean_object* x_112; uint32_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_111 = lean_ctor_get(x_35, 1);
lean_inc(x_111);
lean_dec(x_35);
x_112 = lean_ctor_get(x_36, 0);
lean_inc(x_112);
lean_dec(x_36);
x_113 = lean_unbox_uint32(x_112);
lean_dec(x_112);
x_114 = lean_uint32_to_nat(x_113);
x_115 = l_Lean_mkRawNatLit(x_114);
x_116 = lean_mk_string_unchecked("OfNat", 5, 5);
x_117 = lean_mk_string_unchecked("ofNat", 5, 5);
x_118 = l_Lean_Name_mkStr2(x_116, x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Level_ofNat(x_119);
x_121 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_121);
lean_ctor_set(x_7, 0, x_120);
x_122 = l_Lean_Expr_const___override(x_118, x_7);
x_123 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_123);
x_124 = l_Lean_Name_mkStr1(x_123);
x_125 = l_Lean_Expr_const___override(x_124, x_121);
x_126 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_127 = l_Lean_Name_mkStr2(x_123, x_126);
x_128 = l_Lean_Expr_const___override(x_127, x_121);
lean_inc(x_115);
x_129 = l_Lean_Expr_app___override(x_128, x_115);
x_130 = l_Lean_mkApp3(x_122, x_125, x_115, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_111);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = !lean_is_exclusive(x_35);
if (x_132 == 0)
{
return x_35;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_35, 0);
x_134 = lean_ctor_get(x_35, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_35);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_32);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint16_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_137 = lean_ctor_get(x_32, 0);
lean_dec(x_137);
x_138 = lean_ctor_get(x_33, 0);
lean_inc(x_138);
lean_dec(x_33);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
x_140 = lean_uint16_to_nat(x_139);
x_141 = l_Lean_mkRawNatLit(x_140);
x_142 = lean_mk_string_unchecked("OfNat", 5, 5);
x_143 = lean_mk_string_unchecked("ofNat", 5, 5);
x_144 = l_Lean_Name_mkStr2(x_142, x_143);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Level_ofNat(x_145);
x_147 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_147);
lean_ctor_set(x_7, 0, x_146);
x_148 = l_Lean_Expr_const___override(x_144, x_7);
x_149 = lean_mk_string_unchecked("UInt16", 6, 6);
lean_inc(x_149);
x_150 = l_Lean_Name_mkStr1(x_149);
x_151 = l_Lean_Expr_const___override(x_150, x_147);
x_152 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_153 = l_Lean_Name_mkStr2(x_149, x_152);
x_154 = l_Lean_Expr_const___override(x_153, x_147);
lean_inc(x_141);
x_155 = l_Lean_Expr_app___override(x_154, x_141);
x_156 = l_Lean_mkApp3(x_148, x_151, x_141, x_155);
lean_ctor_set(x_32, 0, x_156);
return x_32;
}
else
{
lean_object* x_157; lean_object* x_158; uint16_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_157 = lean_ctor_get(x_32, 1);
lean_inc(x_157);
lean_dec(x_32);
x_158 = lean_ctor_get(x_33, 0);
lean_inc(x_158);
lean_dec(x_33);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
x_160 = lean_uint16_to_nat(x_159);
x_161 = l_Lean_mkRawNatLit(x_160);
x_162 = lean_mk_string_unchecked("OfNat", 5, 5);
x_163 = lean_mk_string_unchecked("ofNat", 5, 5);
x_164 = l_Lean_Name_mkStr2(x_162, x_163);
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_Lean_Level_ofNat(x_165);
x_167 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_167);
lean_ctor_set(x_7, 0, x_166);
x_168 = l_Lean_Expr_const___override(x_164, x_7);
x_169 = lean_mk_string_unchecked("UInt16", 6, 6);
lean_inc(x_169);
x_170 = l_Lean_Name_mkStr1(x_169);
x_171 = l_Lean_Expr_const___override(x_170, x_167);
x_172 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_173 = l_Lean_Name_mkStr2(x_169, x_172);
x_174 = l_Lean_Expr_const___override(x_173, x_167);
lean_inc(x_161);
x_175 = l_Lean_Expr_app___override(x_174, x_161);
x_176 = l_Lean_mkApp3(x_168, x_171, x_161, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_157);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = !lean_is_exclusive(x_32);
if (x_178 == 0)
{
return x_32;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_32, 0);
x_180 = lean_ctor_get(x_32, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_32);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_182 = !lean_is_exclusive(x_29);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_183 = lean_ctor_get(x_29, 0);
lean_dec(x_183);
x_184 = lean_ctor_get(x_30, 0);
lean_inc(x_184);
lean_dec(x_30);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
x_186 = lean_uint8_to_nat(x_185);
x_187 = l_Lean_mkRawNatLit(x_186);
x_188 = lean_mk_string_unchecked("OfNat", 5, 5);
x_189 = lean_mk_string_unchecked("ofNat", 5, 5);
x_190 = l_Lean_Name_mkStr2(x_188, x_189);
x_191 = lean_unsigned_to_nat(0u);
x_192 = l_Lean_Level_ofNat(x_191);
x_193 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_193);
lean_ctor_set(x_7, 0, x_192);
x_194 = l_Lean_Expr_const___override(x_190, x_7);
x_195 = lean_mk_string_unchecked("UInt8", 5, 5);
lean_inc(x_195);
x_196 = l_Lean_Name_mkStr1(x_195);
x_197 = l_Lean_Expr_const___override(x_196, x_193);
x_198 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_199 = l_Lean_Name_mkStr2(x_195, x_198);
x_200 = l_Lean_Expr_const___override(x_199, x_193);
lean_inc(x_187);
x_201 = l_Lean_Expr_app___override(x_200, x_187);
x_202 = l_Lean_mkApp3(x_194, x_197, x_187, x_201);
lean_ctor_set(x_29, 0, x_202);
return x_29;
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_203 = lean_ctor_get(x_29, 1);
lean_inc(x_203);
lean_dec(x_29);
x_204 = lean_ctor_get(x_30, 0);
lean_inc(x_204);
lean_dec(x_30);
x_205 = lean_unbox(x_204);
lean_dec(x_204);
x_206 = lean_uint8_to_nat(x_205);
x_207 = l_Lean_mkRawNatLit(x_206);
x_208 = lean_mk_string_unchecked("OfNat", 5, 5);
x_209 = lean_mk_string_unchecked("ofNat", 5, 5);
x_210 = l_Lean_Name_mkStr2(x_208, x_209);
x_211 = lean_unsigned_to_nat(0u);
x_212 = l_Lean_Level_ofNat(x_211);
x_213 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_213);
lean_ctor_set(x_7, 0, x_212);
x_214 = l_Lean_Expr_const___override(x_210, x_7);
x_215 = lean_mk_string_unchecked("UInt8", 5, 5);
lean_inc(x_215);
x_216 = l_Lean_Name_mkStr1(x_215);
x_217 = l_Lean_Expr_const___override(x_216, x_213);
x_218 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_219 = l_Lean_Name_mkStr2(x_215, x_218);
x_220 = l_Lean_Expr_const___override(x_219, x_213);
lean_inc(x_207);
x_221 = l_Lean_Expr_app___override(x_220, x_207);
x_222 = l_Lean_mkApp3(x_214, x_217, x_207, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_203);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_224 = !lean_is_exclusive(x_29);
if (x_224 == 0)
{
return x_29;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_29, 0);
x_226 = lean_ctor_get(x_29, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_29);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = !lean_is_exclusive(x_26);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint32_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_229 = lean_ctor_get(x_26, 0);
lean_dec(x_229);
x_230 = lean_ctor_get(x_27, 0);
lean_inc(x_230);
lean_dec(x_27);
x_231 = lean_mk_string_unchecked("Char", 4, 4);
x_232 = lean_mk_string_unchecked("ofNat", 5, 5);
x_233 = l_Lean_Name_mkStr2(x_231, x_232);
x_234 = lean_box(0);
x_235 = l_Lean_Expr_const___override(x_233, x_234);
x_236 = lean_unbox_uint32(x_230);
lean_dec(x_230);
x_237 = lean_uint32_to_nat(x_236);
x_238 = l_Lean_mkRawNatLit(x_237);
x_239 = l_Lean_Expr_app___override(x_235, x_238);
lean_ctor_set(x_26, 0, x_239);
return x_26;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint32_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_240 = lean_ctor_get(x_26, 1);
lean_inc(x_240);
lean_dec(x_26);
x_241 = lean_ctor_get(x_27, 0);
lean_inc(x_241);
lean_dec(x_27);
x_242 = lean_mk_string_unchecked("Char", 4, 4);
x_243 = lean_mk_string_unchecked("ofNat", 5, 5);
x_244 = l_Lean_Name_mkStr2(x_242, x_243);
x_245 = lean_box(0);
x_246 = l_Lean_Expr_const___override(x_244, x_245);
x_247 = lean_unbox_uint32(x_241);
lean_dec(x_241);
x_248 = lean_uint32_to_nat(x_247);
x_249 = l_Lean_mkRawNatLit(x_248);
x_250 = l_Lean_Expr_app___override(x_246, x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_240);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_252 = !lean_is_exclusive(x_26);
if (x_252 == 0)
{
return x_26;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_26, 0);
x_254 = lean_ctor_get(x_26, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_26);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_256 = lean_ctor_get(x_25, 0);
lean_inc(x_256);
lean_dec(x_25);
x_257 = l_Lean_mkStrLit(x_256);
lean_ctor_set(x_20, 0, x_257);
return x_20;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_20, 1);
lean_inc(x_258);
lean_dec(x_20);
lean_inc(x_9);
x_259 = l_Lean_Meta_getStringValue_x3f(x_9);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_260 = l_Lean_Meta_getCharValue_x3f(x_9, x_2, x_3, x_4, x_5, x_258);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_263 = l_Lean_Meta_getUInt8Value_x3f(x_9, x_2, x_3, x_4, x_5, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_266 = l_Lean_Meta_getUInt16Value_x3f(x_9, x_2, x_3, x_4, x_5, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_269 = l_Lean_Meta_getUInt32Value_x3f(x_9, x_2, x_3, x_4, x_5, x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_9);
x_272 = l_Lean_Meta_getUInt64Value_x3f(x_9, x_2, x_3, x_4, x_5, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_free_object(x_7);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_9);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint64_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_9);
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
lean_dec(x_273);
x_280 = lean_unbox_uint64(x_279);
lean_dec(x_279);
x_281 = lean_uint64_to_nat(x_280);
x_282 = l_Lean_mkRawNatLit(x_281);
x_283 = lean_mk_string_unchecked("OfNat", 5, 5);
x_284 = lean_mk_string_unchecked("ofNat", 5, 5);
x_285 = l_Lean_Name_mkStr2(x_283, x_284);
x_286 = lean_unsigned_to_nat(0u);
x_287 = l_Lean_Level_ofNat(x_286);
x_288 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_288);
lean_ctor_set(x_7, 0, x_287);
x_289 = l_Lean_Expr_const___override(x_285, x_7);
x_290 = lean_mk_string_unchecked("UInt64", 6, 6);
lean_inc(x_290);
x_291 = l_Lean_Name_mkStr1(x_290);
x_292 = l_Lean_Expr_const___override(x_291, x_288);
x_293 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_294 = l_Lean_Name_mkStr2(x_290, x_293);
x_295 = l_Lean_Expr_const___override(x_294, x_288);
lean_inc(x_282);
x_296 = l_Lean_Expr_app___override(x_295, x_282);
x_297 = l_Lean_mkApp3(x_289, x_292, x_282, x_296);
if (lean_is_scalar(x_278)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_278;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_277);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_free_object(x_7);
lean_dec(x_9);
x_299 = lean_ctor_get(x_272, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_272, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_301 = x_272;
} else {
 lean_dec_ref(x_272);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint32_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_303 = lean_ctor_get(x_269, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_304 = x_269;
} else {
 lean_dec_ref(x_269);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_270, 0);
lean_inc(x_305);
lean_dec(x_270);
x_306 = lean_unbox_uint32(x_305);
lean_dec(x_305);
x_307 = lean_uint32_to_nat(x_306);
x_308 = l_Lean_mkRawNatLit(x_307);
x_309 = lean_mk_string_unchecked("OfNat", 5, 5);
x_310 = lean_mk_string_unchecked("ofNat", 5, 5);
x_311 = l_Lean_Name_mkStr2(x_309, x_310);
x_312 = lean_unsigned_to_nat(0u);
x_313 = l_Lean_Level_ofNat(x_312);
x_314 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_314);
lean_ctor_set(x_7, 0, x_313);
x_315 = l_Lean_Expr_const___override(x_311, x_7);
x_316 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_316);
x_317 = l_Lean_Name_mkStr1(x_316);
x_318 = l_Lean_Expr_const___override(x_317, x_314);
x_319 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_320 = l_Lean_Name_mkStr2(x_316, x_319);
x_321 = l_Lean_Expr_const___override(x_320, x_314);
lean_inc(x_308);
x_322 = l_Lean_Expr_app___override(x_321, x_308);
x_323 = l_Lean_mkApp3(x_315, x_318, x_308, x_322);
if (lean_is_scalar(x_304)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_304;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_303);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_325 = lean_ctor_get(x_269, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_269, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_327 = x_269;
} else {
 lean_dec_ref(x_269);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint16_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_329 = lean_ctor_get(x_266, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_330 = x_266;
} else {
 lean_dec_ref(x_266);
 x_330 = lean_box(0);
}
x_331 = lean_ctor_get(x_267, 0);
lean_inc(x_331);
lean_dec(x_267);
x_332 = lean_unbox(x_331);
lean_dec(x_331);
x_333 = lean_uint16_to_nat(x_332);
x_334 = l_Lean_mkRawNatLit(x_333);
x_335 = lean_mk_string_unchecked("OfNat", 5, 5);
x_336 = lean_mk_string_unchecked("ofNat", 5, 5);
x_337 = l_Lean_Name_mkStr2(x_335, x_336);
x_338 = lean_unsigned_to_nat(0u);
x_339 = l_Lean_Level_ofNat(x_338);
x_340 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_340);
lean_ctor_set(x_7, 0, x_339);
x_341 = l_Lean_Expr_const___override(x_337, x_7);
x_342 = lean_mk_string_unchecked("UInt16", 6, 6);
lean_inc(x_342);
x_343 = l_Lean_Name_mkStr1(x_342);
x_344 = l_Lean_Expr_const___override(x_343, x_340);
x_345 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_346 = l_Lean_Name_mkStr2(x_342, x_345);
x_347 = l_Lean_Expr_const___override(x_346, x_340);
lean_inc(x_334);
x_348 = l_Lean_Expr_app___override(x_347, x_334);
x_349 = l_Lean_mkApp3(x_341, x_344, x_334, x_348);
if (lean_is_scalar(x_330)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_330;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_329);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_351 = lean_ctor_get(x_266, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_266, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_353 = x_266;
} else {
 lean_dec_ref(x_266);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_355 = lean_ctor_get(x_263, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_356 = x_263;
} else {
 lean_dec_ref(x_263);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_264, 0);
lean_inc(x_357);
lean_dec(x_264);
x_358 = lean_unbox(x_357);
lean_dec(x_357);
x_359 = lean_uint8_to_nat(x_358);
x_360 = l_Lean_mkRawNatLit(x_359);
x_361 = lean_mk_string_unchecked("OfNat", 5, 5);
x_362 = lean_mk_string_unchecked("ofNat", 5, 5);
x_363 = l_Lean_Name_mkStr2(x_361, x_362);
x_364 = lean_unsigned_to_nat(0u);
x_365 = l_Lean_Level_ofNat(x_364);
x_366 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_366);
lean_ctor_set(x_7, 0, x_365);
x_367 = l_Lean_Expr_const___override(x_363, x_7);
x_368 = lean_mk_string_unchecked("UInt8", 5, 5);
lean_inc(x_368);
x_369 = l_Lean_Name_mkStr1(x_368);
x_370 = l_Lean_Expr_const___override(x_369, x_366);
x_371 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_372 = l_Lean_Name_mkStr2(x_368, x_371);
x_373 = l_Lean_Expr_const___override(x_372, x_366);
lean_inc(x_360);
x_374 = l_Lean_Expr_app___override(x_373, x_360);
x_375 = l_Lean_mkApp3(x_367, x_370, x_360, x_374);
if (lean_is_scalar(x_356)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_356;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_355);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_377 = lean_ctor_get(x_263, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_263, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_379 = x_263;
} else {
 lean_dec_ref(x_263);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint32_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_381 = lean_ctor_get(x_260, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_382 = x_260;
} else {
 lean_dec_ref(x_260);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_261, 0);
lean_inc(x_383);
lean_dec(x_261);
x_384 = lean_mk_string_unchecked("Char", 4, 4);
x_385 = lean_mk_string_unchecked("ofNat", 5, 5);
x_386 = l_Lean_Name_mkStr2(x_384, x_385);
x_387 = lean_box(0);
x_388 = l_Lean_Expr_const___override(x_386, x_387);
x_389 = lean_unbox_uint32(x_383);
lean_dec(x_383);
x_390 = lean_uint32_to_nat(x_389);
x_391 = l_Lean_mkRawNatLit(x_390);
x_392 = l_Lean_Expr_app___override(x_388, x_391);
if (lean_is_scalar(x_382)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_382;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_381);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_394 = lean_ctor_get(x_260, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_260, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_396 = x_260;
} else {
 lean_dec_ref(x_260);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_398 = lean_ctor_get(x_259, 0);
lean_inc(x_398);
lean_dec(x_259);
x_399 = l_Lean_mkStrLit(x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_258);
return x_400;
}
}
}
else
{
lean_object* x_401; uint8_t x_402; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_401 = lean_ctor_get(x_21, 0);
lean_inc(x_401);
lean_dec(x_21);
x_402 = !lean_is_exclusive(x_20);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_403 = lean_ctor_get(x_20, 0);
lean_dec(x_403);
x_404 = lean_ctor_get(x_401, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
lean_dec(x_401);
x_406 = lean_mk_string_unchecked("BitVec", 6, 6);
x_407 = lean_mk_string_unchecked("ofNat", 5, 5);
x_408 = l_Lean_Name_mkStr2(x_406, x_407);
x_409 = lean_box(0);
x_410 = l_Lean_Expr_const___override(x_408, x_409);
lean_inc(x_404);
x_411 = l_Lean_mkNatLit(x_404);
x_412 = l_BitVec_toNat(x_404, x_405);
lean_dec(x_405);
lean_dec(x_404);
x_413 = l_Lean_mkNatLit(x_412);
x_414 = l_Lean_mkAppB(x_410, x_411, x_413);
lean_ctor_set(x_20, 0, x_414);
return x_20;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_415 = lean_ctor_get(x_20, 1);
lean_inc(x_415);
lean_dec(x_20);
x_416 = lean_ctor_get(x_401, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_401, 1);
lean_inc(x_417);
lean_dec(x_401);
x_418 = lean_mk_string_unchecked("BitVec", 6, 6);
x_419 = lean_mk_string_unchecked("ofNat", 5, 5);
x_420 = l_Lean_Name_mkStr2(x_418, x_419);
x_421 = lean_box(0);
x_422 = l_Lean_Expr_const___override(x_420, x_421);
lean_inc(x_416);
x_423 = l_Lean_mkNatLit(x_416);
x_424 = l_BitVec_toNat(x_416, x_417);
lean_dec(x_417);
lean_dec(x_416);
x_425 = l_Lean_mkNatLit(x_424);
x_426 = l_Lean_mkAppB(x_422, x_423, x_425);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_415);
return x_427;
}
}
}
else
{
uint8_t x_428; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_428 = !lean_is_exclusive(x_20);
if (x_428 == 0)
{
return x_20;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_20, 0);
x_430 = lean_ctor_get(x_20, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_20);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
lean_object* x_432; uint8_t x_433; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_432 = lean_ctor_get(x_18, 0);
lean_inc(x_432);
lean_dec(x_18);
x_433 = !lean_is_exclusive(x_17);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = lean_ctor_get(x_17, 0);
lean_dec(x_434);
x_435 = !lean_is_exclusive(x_432);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_436 = lean_ctor_get(x_432, 0);
x_437 = lean_ctor_get(x_432, 1);
x_438 = l_Lean_mkRawNatLit(x_437);
x_439 = lean_mk_string_unchecked("OfNat", 5, 5);
x_440 = lean_mk_string_unchecked("ofNat", 5, 5);
x_441 = l_Lean_Name_mkStr2(x_439, x_440);
x_442 = lean_unsigned_to_nat(0u);
x_443 = l_Lean_Level_ofNat(x_442);
x_444 = lean_box(0);
lean_ctor_set_tag(x_432, 1);
lean_ctor_set(x_432, 1, x_444);
lean_ctor_set(x_432, 0, x_443);
x_445 = l_Lean_Expr_const___override(x_441, x_432);
x_446 = lean_mk_string_unchecked("Fin", 3, 3);
lean_inc(x_446);
x_447 = l_Lean_Name_mkStr1(x_446);
x_448 = l_Lean_Expr_const___override(x_447, x_444);
lean_inc(x_436);
x_449 = l_Lean_mkNatLit(x_436);
lean_inc(x_449);
x_450 = l_Lean_Expr_app___override(x_448, x_449);
x_451 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_452 = l_Lean_Name_mkStr2(x_446, x_451);
x_453 = l_Lean_Expr_const___override(x_452, x_444);
x_454 = lean_mk_string_unchecked("Nat", 3, 3);
x_455 = lean_mk_string_unchecked("instNeZeroSucc", 14, 14);
x_456 = l_Lean_Name_mkStr2(x_454, x_455);
x_457 = l_Lean_Expr_const___override(x_456, x_444);
x_458 = lean_unsigned_to_nat(1u);
x_459 = lean_nat_sub(x_436, x_458);
lean_dec(x_436);
x_460 = l_Lean_mkNatLit(x_459);
x_461 = l_Lean_Expr_app___override(x_457, x_460);
lean_inc(x_438);
x_462 = l_Lean_mkApp3(x_453, x_449, x_461, x_438);
x_463 = l_Lean_mkApp3(x_445, x_450, x_438, x_462);
lean_ctor_set(x_17, 0, x_463);
return x_17;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_464 = lean_ctor_get(x_432, 0);
x_465 = lean_ctor_get(x_432, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_432);
x_466 = l_Lean_mkRawNatLit(x_465);
x_467 = lean_mk_string_unchecked("OfNat", 5, 5);
x_468 = lean_mk_string_unchecked("ofNat", 5, 5);
x_469 = l_Lean_Name_mkStr2(x_467, x_468);
x_470 = lean_unsigned_to_nat(0u);
x_471 = l_Lean_Level_ofNat(x_470);
x_472 = lean_box(0);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
x_474 = l_Lean_Expr_const___override(x_469, x_473);
x_475 = lean_mk_string_unchecked("Fin", 3, 3);
lean_inc(x_475);
x_476 = l_Lean_Name_mkStr1(x_475);
x_477 = l_Lean_Expr_const___override(x_476, x_472);
lean_inc(x_464);
x_478 = l_Lean_mkNatLit(x_464);
lean_inc(x_478);
x_479 = l_Lean_Expr_app___override(x_477, x_478);
x_480 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_481 = l_Lean_Name_mkStr2(x_475, x_480);
x_482 = l_Lean_Expr_const___override(x_481, x_472);
x_483 = lean_mk_string_unchecked("Nat", 3, 3);
x_484 = lean_mk_string_unchecked("instNeZeroSucc", 14, 14);
x_485 = l_Lean_Name_mkStr2(x_483, x_484);
x_486 = l_Lean_Expr_const___override(x_485, x_472);
x_487 = lean_unsigned_to_nat(1u);
x_488 = lean_nat_sub(x_464, x_487);
lean_dec(x_464);
x_489 = l_Lean_mkNatLit(x_488);
x_490 = l_Lean_Expr_app___override(x_486, x_489);
lean_inc(x_466);
x_491 = l_Lean_mkApp3(x_482, x_478, x_490, x_466);
x_492 = l_Lean_mkApp3(x_474, x_479, x_466, x_491);
lean_ctor_set(x_17, 0, x_492);
return x_17;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_493 = lean_ctor_get(x_17, 1);
lean_inc(x_493);
lean_dec(x_17);
x_494 = lean_ctor_get(x_432, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_432, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_496 = x_432;
} else {
 lean_dec_ref(x_432);
 x_496 = lean_box(0);
}
x_497 = l_Lean_mkRawNatLit(x_495);
x_498 = lean_mk_string_unchecked("OfNat", 5, 5);
x_499 = lean_mk_string_unchecked("ofNat", 5, 5);
x_500 = l_Lean_Name_mkStr2(x_498, x_499);
x_501 = lean_unsigned_to_nat(0u);
x_502 = l_Lean_Level_ofNat(x_501);
x_503 = lean_box(0);
if (lean_is_scalar(x_496)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_496;
 lean_ctor_set_tag(x_504, 1);
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
x_505 = l_Lean_Expr_const___override(x_500, x_504);
x_506 = lean_mk_string_unchecked("Fin", 3, 3);
lean_inc(x_506);
x_507 = l_Lean_Name_mkStr1(x_506);
x_508 = l_Lean_Expr_const___override(x_507, x_503);
lean_inc(x_494);
x_509 = l_Lean_mkNatLit(x_494);
lean_inc(x_509);
x_510 = l_Lean_Expr_app___override(x_508, x_509);
x_511 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_512 = l_Lean_Name_mkStr2(x_506, x_511);
x_513 = l_Lean_Expr_const___override(x_512, x_503);
x_514 = lean_mk_string_unchecked("Nat", 3, 3);
x_515 = lean_mk_string_unchecked("instNeZeroSucc", 14, 14);
x_516 = l_Lean_Name_mkStr2(x_514, x_515);
x_517 = l_Lean_Expr_const___override(x_516, x_503);
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_sub(x_494, x_518);
lean_dec(x_494);
x_520 = l_Lean_mkNatLit(x_519);
x_521 = l_Lean_Expr_app___override(x_517, x_520);
lean_inc(x_497);
x_522 = l_Lean_mkApp3(x_513, x_509, x_521, x_497);
x_523 = l_Lean_mkApp3(x_505, x_510, x_497, x_522);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_493);
return x_524;
}
}
}
else
{
uint8_t x_525; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_525 = !lean_is_exclusive(x_17);
if (x_525 == 0)
{
return x_17;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_17, 0);
x_527 = lean_ctor_get(x_17, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_17);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
else
{
uint8_t x_529; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_529 = !lean_is_exclusive(x_14);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_530 = lean_ctor_get(x_14, 0);
lean_dec(x_530);
x_531 = lean_ctor_get(x_15, 0);
lean_inc(x_531);
lean_dec(x_15);
x_532 = lean_unsigned_to_nat(0u);
x_533 = lean_nat_to_int(x_532);
x_534 = lean_int_dec_le(x_533, x_531);
lean_dec(x_533);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_535 = lean_mk_string_unchecked("Neg", 3, 3);
x_536 = lean_mk_string_unchecked("neg", 3, 3);
x_537 = l_Lean_Name_mkStr2(x_535, x_536);
x_538 = l_Lean_Level_ofNat(x_532);
x_539 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_539);
lean_ctor_set(x_7, 0, x_538);
x_540 = l_Lean_Expr_const___override(x_537, x_7);
x_541 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_541);
x_542 = l_Lean_Name_mkStr1(x_541);
x_543 = l_Lean_Expr_const___override(x_542, x_539);
x_544 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_545 = l_Lean_Name_mkStr2(x_541, x_544);
x_546 = l_Lean_Expr_const___override(x_545, x_539);
x_547 = lean_int_neg(x_531);
lean_dec(x_531);
x_548 = l_Int_toNat(x_547);
lean_dec(x_547);
x_549 = l_Lean_instToExprInt_mkNat(x_548);
x_550 = l_Lean_mkApp3(x_540, x_543, x_546, x_549);
lean_ctor_set(x_14, 0, x_550);
return x_14;
}
else
{
lean_object* x_551; lean_object* x_552; 
lean_free_object(x_7);
x_551 = l_Int_toNat(x_531);
lean_dec(x_531);
x_552 = l_Lean_instToExprInt_mkNat(x_551);
lean_ctor_set(x_14, 0, x_552);
return x_14;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_553 = lean_ctor_get(x_14, 1);
lean_inc(x_553);
lean_dec(x_14);
x_554 = lean_ctor_get(x_15, 0);
lean_inc(x_554);
lean_dec(x_15);
x_555 = lean_unsigned_to_nat(0u);
x_556 = lean_nat_to_int(x_555);
x_557 = lean_int_dec_le(x_556, x_554);
lean_dec(x_556);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_558 = lean_mk_string_unchecked("Neg", 3, 3);
x_559 = lean_mk_string_unchecked("neg", 3, 3);
x_560 = l_Lean_Name_mkStr2(x_558, x_559);
x_561 = l_Lean_Level_ofNat(x_555);
x_562 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_562);
lean_ctor_set(x_7, 0, x_561);
x_563 = l_Lean_Expr_const___override(x_560, x_7);
x_564 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_564);
x_565 = l_Lean_Name_mkStr1(x_564);
x_566 = l_Lean_Expr_const___override(x_565, x_562);
x_567 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_568 = l_Lean_Name_mkStr2(x_564, x_567);
x_569 = l_Lean_Expr_const___override(x_568, x_562);
x_570 = lean_int_neg(x_554);
lean_dec(x_554);
x_571 = l_Int_toNat(x_570);
lean_dec(x_570);
x_572 = l_Lean_instToExprInt_mkNat(x_571);
x_573 = l_Lean_mkApp3(x_563, x_566, x_569, x_572);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_553);
return x_574;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_free_object(x_7);
x_575 = l_Int_toNat(x_554);
lean_dec(x_554);
x_576 = l_Lean_instToExprInt_mkNat(x_575);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_553);
return x_577;
}
}
}
}
else
{
uint8_t x_578; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_578 = !lean_is_exclusive(x_14);
if (x_578 == 0)
{
return x_14;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_14, 0);
x_580 = lean_ctor_get(x_14, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_14);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_582 = !lean_is_exclusive(x_11);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_11, 0);
lean_dec(x_583);
x_584 = lean_ctor_get(x_12, 0);
lean_inc(x_584);
lean_dec(x_12);
x_585 = l_Lean_mkNatLit(x_584);
lean_ctor_set(x_11, 0, x_585);
return x_11;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_586 = lean_ctor_get(x_11, 1);
lean_inc(x_586);
lean_dec(x_11);
x_587 = lean_ctor_get(x_12, 0);
lean_inc(x_587);
lean_dec(x_12);
x_588 = l_Lean_mkNatLit(x_587);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_586);
return x_589;
}
}
}
else
{
uint8_t x_590; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_590 = !lean_is_exclusive(x_11);
if (x_590 == 0)
{
return x_11;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_11, 0);
x_592 = lean_ctor_get(x_11, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_11);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
return x_593;
}
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_7, 0);
x_595 = lean_ctor_get(x_7, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_596 = l_Lean_Meta_getNatValue_x3f(x_594, x_2, x_3, x_4, x_5, x_595);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; 
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_599 = l_Lean_Meta_getIntValue_x3f(x_594, x_2, x_3, x_4, x_5, x_598);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; 
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_602 = l_Lean_Meta_getFinValue_x3f(x_594, x_2, x_3, x_4, x_5, x_601);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; 
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_605 = l_Lean_Meta_getBitVecValue_x3f(x_594, x_2, x_3, x_4, x_5, x_604);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_608 = x_605;
} else {
 lean_dec_ref(x_605);
 x_608 = lean_box(0);
}
lean_inc(x_594);
x_609 = l_Lean_Meta_getStringValue_x3f(x_594);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; 
lean_dec(x_608);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_610 = l_Lean_Meta_getCharValue_x3f(x_594, x_2, x_3, x_4, x_5, x_607);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_613 = l_Lean_Meta_getUInt8Value_x3f(x_594, x_2, x_3, x_4, x_5, x_612);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; 
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_616 = l_Lean_Meta_getUInt16Value_x3f(x_594, x_2, x_3, x_4, x_5, x_615);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_594);
x_619 = l_Lean_Meta_getUInt32Value_x3f(x_594, x_2, x_3, x_4, x_5, x_618);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
lean_inc(x_594);
x_622 = l_Lean_Meta_getUInt64Value_x3f(x_594, x_2, x_3, x_4, x_5, x_621);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_625 = x_622;
} else {
 lean_dec_ref(x_622);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_594);
lean_ctor_set(x_626, 1, x_624);
return x_626;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint64_t x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_594);
x_627 = lean_ctor_get(x_622, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_628 = x_622;
} else {
 lean_dec_ref(x_622);
 x_628 = lean_box(0);
}
x_629 = lean_ctor_get(x_623, 0);
lean_inc(x_629);
lean_dec(x_623);
x_630 = lean_unbox_uint64(x_629);
lean_dec(x_629);
x_631 = lean_uint64_to_nat(x_630);
x_632 = l_Lean_mkRawNatLit(x_631);
x_633 = lean_mk_string_unchecked("OfNat", 5, 5);
x_634 = lean_mk_string_unchecked("ofNat", 5, 5);
x_635 = l_Lean_Name_mkStr2(x_633, x_634);
x_636 = lean_unsigned_to_nat(0u);
x_637 = l_Lean_Level_ofNat(x_636);
x_638 = lean_box(0);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
x_640 = l_Lean_Expr_const___override(x_635, x_639);
x_641 = lean_mk_string_unchecked("UInt64", 6, 6);
lean_inc(x_641);
x_642 = l_Lean_Name_mkStr1(x_641);
x_643 = l_Lean_Expr_const___override(x_642, x_638);
x_644 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_645 = l_Lean_Name_mkStr2(x_641, x_644);
x_646 = l_Lean_Expr_const___override(x_645, x_638);
lean_inc(x_632);
x_647 = l_Lean_Expr_app___override(x_646, x_632);
x_648 = l_Lean_mkApp3(x_640, x_643, x_632, x_647);
if (lean_is_scalar(x_628)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_628;
}
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_627);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_594);
x_650 = lean_ctor_get(x_622, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_622, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_652 = x_622;
} else {
 lean_dec_ref(x_622);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint32_t x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_654 = lean_ctor_get(x_619, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_655 = x_619;
} else {
 lean_dec_ref(x_619);
 x_655 = lean_box(0);
}
x_656 = lean_ctor_get(x_620, 0);
lean_inc(x_656);
lean_dec(x_620);
x_657 = lean_unbox_uint32(x_656);
lean_dec(x_656);
x_658 = lean_uint32_to_nat(x_657);
x_659 = l_Lean_mkRawNatLit(x_658);
x_660 = lean_mk_string_unchecked("OfNat", 5, 5);
x_661 = lean_mk_string_unchecked("ofNat", 5, 5);
x_662 = l_Lean_Name_mkStr2(x_660, x_661);
x_663 = lean_unsigned_to_nat(0u);
x_664 = l_Lean_Level_ofNat(x_663);
x_665 = lean_box(0);
x_666 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_666, 0, x_664);
lean_ctor_set(x_666, 1, x_665);
x_667 = l_Lean_Expr_const___override(x_662, x_666);
x_668 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_668);
x_669 = l_Lean_Name_mkStr1(x_668);
x_670 = l_Lean_Expr_const___override(x_669, x_665);
x_671 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_672 = l_Lean_Name_mkStr2(x_668, x_671);
x_673 = l_Lean_Expr_const___override(x_672, x_665);
lean_inc(x_659);
x_674 = l_Lean_Expr_app___override(x_673, x_659);
x_675 = l_Lean_mkApp3(x_667, x_670, x_659, x_674);
if (lean_is_scalar(x_655)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_655;
}
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_654);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_677 = lean_ctor_get(x_619, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_619, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_679 = x_619;
} else {
 lean_dec_ref(x_619);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint16_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_681 = lean_ctor_get(x_616, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_682 = x_616;
} else {
 lean_dec_ref(x_616);
 x_682 = lean_box(0);
}
x_683 = lean_ctor_get(x_617, 0);
lean_inc(x_683);
lean_dec(x_617);
x_684 = lean_unbox(x_683);
lean_dec(x_683);
x_685 = lean_uint16_to_nat(x_684);
x_686 = l_Lean_mkRawNatLit(x_685);
x_687 = lean_mk_string_unchecked("OfNat", 5, 5);
x_688 = lean_mk_string_unchecked("ofNat", 5, 5);
x_689 = l_Lean_Name_mkStr2(x_687, x_688);
x_690 = lean_unsigned_to_nat(0u);
x_691 = l_Lean_Level_ofNat(x_690);
x_692 = lean_box(0);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
x_694 = l_Lean_Expr_const___override(x_689, x_693);
x_695 = lean_mk_string_unchecked("UInt16", 6, 6);
lean_inc(x_695);
x_696 = l_Lean_Name_mkStr1(x_695);
x_697 = l_Lean_Expr_const___override(x_696, x_692);
x_698 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_699 = l_Lean_Name_mkStr2(x_695, x_698);
x_700 = l_Lean_Expr_const___override(x_699, x_692);
lean_inc(x_686);
x_701 = l_Lean_Expr_app___override(x_700, x_686);
x_702 = l_Lean_mkApp3(x_694, x_697, x_686, x_701);
if (lean_is_scalar(x_682)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_682;
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_681);
return x_703;
}
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_704 = lean_ctor_get(x_616, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_616, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_706 = x_616;
} else {
 lean_dec_ref(x_616);
 x_706 = lean_box(0);
}
if (lean_is_scalar(x_706)) {
 x_707 = lean_alloc_ctor(1, 2, 0);
} else {
 x_707 = x_706;
}
lean_ctor_set(x_707, 0, x_704);
lean_ctor_set(x_707, 1, x_705);
return x_707;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_708 = lean_ctor_get(x_613, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_709 = x_613;
} else {
 lean_dec_ref(x_613);
 x_709 = lean_box(0);
}
x_710 = lean_ctor_get(x_614, 0);
lean_inc(x_710);
lean_dec(x_614);
x_711 = lean_unbox(x_710);
lean_dec(x_710);
x_712 = lean_uint8_to_nat(x_711);
x_713 = l_Lean_mkRawNatLit(x_712);
x_714 = lean_mk_string_unchecked("OfNat", 5, 5);
x_715 = lean_mk_string_unchecked("ofNat", 5, 5);
x_716 = l_Lean_Name_mkStr2(x_714, x_715);
x_717 = lean_unsigned_to_nat(0u);
x_718 = l_Lean_Level_ofNat(x_717);
x_719 = lean_box(0);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
x_721 = l_Lean_Expr_const___override(x_716, x_720);
x_722 = lean_mk_string_unchecked("UInt8", 5, 5);
lean_inc(x_722);
x_723 = l_Lean_Name_mkStr1(x_722);
x_724 = l_Lean_Expr_const___override(x_723, x_719);
x_725 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_726 = l_Lean_Name_mkStr2(x_722, x_725);
x_727 = l_Lean_Expr_const___override(x_726, x_719);
lean_inc(x_713);
x_728 = l_Lean_Expr_app___override(x_727, x_713);
x_729 = l_Lean_mkApp3(x_721, x_724, x_713, x_728);
if (lean_is_scalar(x_709)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_709;
}
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_708);
return x_730;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_731 = lean_ctor_get(x_613, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_613, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_733 = x_613;
} else {
 lean_dec_ref(x_613);
 x_733 = lean_box(0);
}
if (lean_is_scalar(x_733)) {
 x_734 = lean_alloc_ctor(1, 2, 0);
} else {
 x_734 = x_733;
}
lean_ctor_set(x_734, 0, x_731);
lean_ctor_set(x_734, 1, x_732);
return x_734;
}
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; uint32_t x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_735 = lean_ctor_get(x_610, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_736 = x_610;
} else {
 lean_dec_ref(x_610);
 x_736 = lean_box(0);
}
x_737 = lean_ctor_get(x_611, 0);
lean_inc(x_737);
lean_dec(x_611);
x_738 = lean_mk_string_unchecked("Char", 4, 4);
x_739 = lean_mk_string_unchecked("ofNat", 5, 5);
x_740 = l_Lean_Name_mkStr2(x_738, x_739);
x_741 = lean_box(0);
x_742 = l_Lean_Expr_const___override(x_740, x_741);
x_743 = lean_unbox_uint32(x_737);
lean_dec(x_737);
x_744 = lean_uint32_to_nat(x_743);
x_745 = l_Lean_mkRawNatLit(x_744);
x_746 = l_Lean_Expr_app___override(x_742, x_745);
if (lean_is_scalar(x_736)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_736;
}
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_735);
return x_747;
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_748 = lean_ctor_get(x_610, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_610, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_750 = x_610;
} else {
 lean_dec_ref(x_610);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_752 = lean_ctor_get(x_609, 0);
lean_inc(x_752);
lean_dec(x_609);
x_753 = l_Lean_mkStrLit(x_752);
if (lean_is_scalar(x_608)) {
 x_754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_754 = x_608;
}
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_607);
return x_754;
}
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_755 = lean_ctor_get(x_606, 0);
lean_inc(x_755);
lean_dec(x_606);
x_756 = lean_ctor_get(x_605, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_757 = x_605;
} else {
 lean_dec_ref(x_605);
 x_757 = lean_box(0);
}
x_758 = lean_ctor_get(x_755, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_755, 1);
lean_inc(x_759);
lean_dec(x_755);
x_760 = lean_mk_string_unchecked("BitVec", 6, 6);
x_761 = lean_mk_string_unchecked("ofNat", 5, 5);
x_762 = l_Lean_Name_mkStr2(x_760, x_761);
x_763 = lean_box(0);
x_764 = l_Lean_Expr_const___override(x_762, x_763);
lean_inc(x_758);
x_765 = l_Lean_mkNatLit(x_758);
x_766 = l_BitVec_toNat(x_758, x_759);
lean_dec(x_759);
lean_dec(x_758);
x_767 = l_Lean_mkNatLit(x_766);
x_768 = l_Lean_mkAppB(x_764, x_765, x_767);
if (lean_is_scalar(x_757)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_757;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_756);
return x_769;
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_770 = lean_ctor_get(x_605, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_605, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_772 = x_605;
} else {
 lean_dec_ref(x_605);
 x_772 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_773 = lean_alloc_ctor(1, 2, 0);
} else {
 x_773 = x_772;
}
lean_ctor_set(x_773, 0, x_770);
lean_ctor_set(x_773, 1, x_771);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_774 = lean_ctor_get(x_603, 0);
lean_inc(x_774);
lean_dec(x_603);
x_775 = lean_ctor_get(x_602, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_776 = x_602;
} else {
 lean_dec_ref(x_602);
 x_776 = lean_box(0);
}
x_777 = lean_ctor_get(x_774, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_774, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_779 = x_774;
} else {
 lean_dec_ref(x_774);
 x_779 = lean_box(0);
}
x_780 = l_Lean_mkRawNatLit(x_778);
x_781 = lean_mk_string_unchecked("OfNat", 5, 5);
x_782 = lean_mk_string_unchecked("ofNat", 5, 5);
x_783 = l_Lean_Name_mkStr2(x_781, x_782);
x_784 = lean_unsigned_to_nat(0u);
x_785 = l_Lean_Level_ofNat(x_784);
x_786 = lean_box(0);
if (lean_is_scalar(x_779)) {
 x_787 = lean_alloc_ctor(1, 2, 0);
} else {
 x_787 = x_779;
 lean_ctor_set_tag(x_787, 1);
}
lean_ctor_set(x_787, 0, x_785);
lean_ctor_set(x_787, 1, x_786);
x_788 = l_Lean_Expr_const___override(x_783, x_787);
x_789 = lean_mk_string_unchecked("Fin", 3, 3);
lean_inc(x_789);
x_790 = l_Lean_Name_mkStr1(x_789);
x_791 = l_Lean_Expr_const___override(x_790, x_786);
lean_inc(x_777);
x_792 = l_Lean_mkNatLit(x_777);
lean_inc(x_792);
x_793 = l_Lean_Expr_app___override(x_791, x_792);
x_794 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_795 = l_Lean_Name_mkStr2(x_789, x_794);
x_796 = l_Lean_Expr_const___override(x_795, x_786);
x_797 = lean_mk_string_unchecked("Nat", 3, 3);
x_798 = lean_mk_string_unchecked("instNeZeroSucc", 14, 14);
x_799 = l_Lean_Name_mkStr2(x_797, x_798);
x_800 = l_Lean_Expr_const___override(x_799, x_786);
x_801 = lean_unsigned_to_nat(1u);
x_802 = lean_nat_sub(x_777, x_801);
lean_dec(x_777);
x_803 = l_Lean_mkNatLit(x_802);
x_804 = l_Lean_Expr_app___override(x_800, x_803);
lean_inc(x_780);
x_805 = l_Lean_mkApp3(x_796, x_792, x_804, x_780);
x_806 = l_Lean_mkApp3(x_788, x_793, x_780, x_805);
if (lean_is_scalar(x_776)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_776;
}
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_775);
return x_807;
}
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_808 = lean_ctor_get(x_602, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_602, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_810 = x_602;
} else {
 lean_dec_ref(x_602);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(1, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_808);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; uint8_t x_817; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_812 = lean_ctor_get(x_599, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_813 = x_599;
} else {
 lean_dec_ref(x_599);
 x_813 = lean_box(0);
}
x_814 = lean_ctor_get(x_600, 0);
lean_inc(x_814);
lean_dec(x_600);
x_815 = lean_unsigned_to_nat(0u);
x_816 = lean_nat_to_int(x_815);
x_817 = lean_int_dec_le(x_816, x_814);
lean_dec(x_816);
if (x_817 == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_818 = lean_mk_string_unchecked("Neg", 3, 3);
x_819 = lean_mk_string_unchecked("neg", 3, 3);
x_820 = l_Lean_Name_mkStr2(x_818, x_819);
x_821 = l_Lean_Level_ofNat(x_815);
x_822 = lean_box(0);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
x_824 = l_Lean_Expr_const___override(x_820, x_823);
x_825 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_825);
x_826 = l_Lean_Name_mkStr1(x_825);
x_827 = l_Lean_Expr_const___override(x_826, x_822);
x_828 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_829 = l_Lean_Name_mkStr2(x_825, x_828);
x_830 = l_Lean_Expr_const___override(x_829, x_822);
x_831 = lean_int_neg(x_814);
lean_dec(x_814);
x_832 = l_Int_toNat(x_831);
lean_dec(x_831);
x_833 = l_Lean_instToExprInt_mkNat(x_832);
x_834 = l_Lean_mkApp3(x_824, x_827, x_830, x_833);
if (lean_is_scalar(x_813)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_813;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_812);
return x_835;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = l_Int_toNat(x_814);
lean_dec(x_814);
x_837 = l_Lean_instToExprInt_mkNat(x_836);
if (lean_is_scalar(x_813)) {
 x_838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_838 = x_813;
}
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_812);
return x_838;
}
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_839 = lean_ctor_get(x_599, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_599, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_841 = x_599;
} else {
 lean_dec_ref(x_599);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_840);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_843 = lean_ctor_get(x_596, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_844 = x_596;
} else {
 lean_dec_ref(x_596);
 x_844 = lean_box(0);
}
x_845 = lean_ctor_get(x_597, 0);
lean_inc(x_845);
lean_dec(x_597);
x_846 = l_Lean_mkNatLit(x_845);
if (lean_is_scalar(x_844)) {
 x_847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_847 = x_844;
}
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_843);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_594);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_848 = lean_ctor_get(x_596, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_596, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_850 = x_596;
} else {
 lean_dec_ref(x_596);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_848);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normLitValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_normLitValue(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Meta_getNatValue_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_13 = l_Lean_Meta_getIntValue_x3f(x_8, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_16 = l_Lean_Meta_getFinValue_x3f(x_8, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_getBitVecValue_x3f(x_8, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
lean_inc(x_8);
x_24 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_free_object(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_25 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_28 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_31 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_34 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_38);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 0);
lean_dec(x_46);
x_47 = lean_box(1);
lean_ctor_set(x_37, 0, x_47);
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_box(1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_37);
if (x_51 == 0)
{
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_34, 0);
lean_dec(x_56);
x_57 = lean_box(1);
lean_ctor_set(x_34, 0, x_57);
return x_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_dec(x_34);
x_59 = lean_box(1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
return x_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_34);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_31);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_31, 0);
lean_dec(x_66);
x_67 = lean_box(1);
lean_ctor_set(x_31, 0, x_67);
return x_31;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_31, 1);
lean_inc(x_68);
lean_dec(x_31);
x_69 = lean_box(1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_31);
if (x_71 == 0)
{
return x_31;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_31, 0);
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_31);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_28);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_28, 0);
lean_dec(x_76);
x_77 = lean_box(1);
lean_ctor_set(x_28, 0, x_77);
return x_28;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_28, 1);
lean_inc(x_78);
lean_dec(x_28);
x_79 = lean_box(1);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_28);
if (x_81 == 0)
{
return x_28;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_28, 0);
x_83 = lean_ctor_get(x_28, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_28);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_25);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_25, 0);
lean_dec(x_86);
x_87 = lean_box(1);
lean_ctor_set(x_25, 0, x_87);
return x_25;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_25, 1);
lean_inc(x_88);
lean_dec(x_25);
x_89 = lean_box(1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_25);
if (x_91 == 0)
{
return x_25;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_25, 0);
x_93 = lean_ctor_get(x_25, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_25);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_box(1);
lean_ctor_set(x_19, 0, x_95);
return x_19;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
lean_dec(x_19);
lean_inc(x_8);
x_97 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_98 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_101 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_104 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
x_107 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_111);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
x_118 = lean_box(1);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_110, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_122 = x_110;
} else {
 lean_dec_ref(x_110);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_125 = x_107;
} else {
 lean_dec_ref(x_107);
 x_125 = lean_box(0);
}
x_126 = lean_box(1);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_107, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_107, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_130 = x_107;
} else {
 lean_dec_ref(x_107);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_ctor_get(x_104, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_133 = x_104;
} else {
 lean_dec_ref(x_104);
 x_133 = lean_box(0);
}
x_134 = lean_box(1);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_ctor_get(x_104, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_104, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_138 = x_104;
} else {
 lean_dec_ref(x_104);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_ctor_get(x_101, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_141 = x_101;
} else {
 lean_dec_ref(x_101);
 x_141 = lean_box(0);
}
x_142 = lean_box(1);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_101, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_101, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_146 = x_101;
} else {
 lean_dec_ref(x_101);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_99);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_98, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_149 = x_98;
} else {
 lean_dec_ref(x_98);
 x_149 = lean_box(0);
}
x_150 = lean_box(1);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_98, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_98, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_154 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_97);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = lean_box(1);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_96);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = !lean_is_exclusive(x_19);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_19, 0);
lean_dec(x_159);
x_160 = lean_box(1);
lean_ctor_set(x_19, 0, x_160);
return x_19;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_19, 1);
lean_inc(x_161);
lean_dec(x_19);
x_162 = lean_box(1);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_164 = !lean_is_exclusive(x_19);
if (x_164 == 0)
{
return x_19;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_19, 0);
x_166 = lean_ctor_get(x_19, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_19);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = !lean_is_exclusive(x_16);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_16, 0);
lean_dec(x_169);
x_170 = lean_box(1);
lean_ctor_set(x_16, 0, x_170);
return x_16;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_16, 1);
lean_inc(x_171);
lean_dec(x_16);
x_172 = lean_box(1);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_174 = !lean_is_exclusive(x_16);
if (x_174 == 0)
{
return x_16;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_16, 0);
x_176 = lean_ctor_get(x_16, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_16);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = !lean_is_exclusive(x_13);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_13, 0);
lean_dec(x_179);
x_180 = lean_box(1);
lean_ctor_set(x_13, 0, x_180);
return x_13;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_13, 1);
lean_inc(x_181);
lean_dec(x_13);
x_182 = lean_box(1);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = !lean_is_exclusive(x_13);
if (x_184 == 0)
{
return x_13;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_13, 0);
x_186 = lean_ctor_get(x_13, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_13);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = !lean_is_exclusive(x_10);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_10, 0);
lean_dec(x_189);
x_190 = lean_box(1);
lean_ctor_set(x_10, 0, x_190);
return x_10;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_10, 1);
lean_inc(x_191);
lean_dec(x_10);
x_192 = lean_box(1);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = !lean_is_exclusive(x_10);
if (x_194 == 0)
{
return x_10;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_10, 0);
x_196 = lean_ctor_get(x_10, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_10);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLitValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isLitValue(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_getNatValue_x3f(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_getIntValue_x3f(x_9, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
x_17 = l_Lean_Meta_getFinValue_x3f(x_9, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_free_object(x_7);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_9);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
x_29 = l_Lean_mkNatLit(x_28);
x_30 = l_Lean_mkNatLit(x_27);
x_31 = lean_mk_string_unchecked("LT", 2, 2);
x_32 = lean_mk_string_unchecked("lt", 2, 2);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Level_ofNat(x_34);
x_36 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_36);
lean_ctor_set(x_23, 0, x_35);
x_37 = l_Lean_Expr_const___override(x_33, x_23);
x_38 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_38);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = l_Lean_Expr_const___override(x_39, x_36);
x_41 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = l_Lean_Expr_const___override(x_42, x_36);
lean_inc(x_30);
lean_inc(x_29);
x_44 = l_Lean_mkApp4(x_37, x_40, x_43, x_29, x_30);
x_45 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = l_Lean_Expr_const___override(x_46, x_36);
x_48 = lean_mk_string_unchecked("decLt", 5, 5);
x_49 = l_Lean_Name_mkStr2(x_38, x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_36);
lean_inc(x_30);
lean_inc(x_29);
x_51 = l_Lean_mkAppB(x_50, x_29, x_30);
x_52 = lean_mk_string_unchecked("Eq", 2, 2);
x_53 = lean_mk_string_unchecked("refl", 4, 4);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = l_Lean_Level_ofNat(x_55);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_36);
lean_ctor_set(x_7, 0, x_56);
x_57 = l_Lean_Expr_const___override(x_54, x_7);
x_58 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_58);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_36);
x_61 = lean_mk_string_unchecked("true", 4, 4);
x_62 = l_Lean_Name_mkStr2(x_58, x_61);
x_63 = l_Lean_Expr_const___override(x_62, x_36);
x_64 = l_Lean_mkAppB(x_57, x_60, x_63);
x_65 = l_Lean_mkApp3(x_47, x_44, x_51, x_64);
x_66 = lean_mk_string_unchecked("Fin", 3, 3);
x_67 = lean_mk_string_unchecked("mk", 2, 2);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = l_Lean_Expr_const___override(x_68, x_36);
x_70 = l_Lean_mkApp3(x_69, x_30, x_29, x_65);
lean_ctor_set(x_17, 0, x_70);
return x_17;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_71 = lean_ctor_get(x_23, 0);
x_72 = lean_ctor_get(x_23, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_23);
x_73 = l_Lean_mkNatLit(x_72);
x_74 = l_Lean_mkNatLit(x_71);
x_75 = lean_mk_string_unchecked("LT", 2, 2);
x_76 = lean_mk_string_unchecked("lt", 2, 2);
x_77 = l_Lean_Name_mkStr2(x_75, x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Level_ofNat(x_78);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Expr_const___override(x_77, x_81);
x_83 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_83);
x_84 = l_Lean_Name_mkStr1(x_83);
x_85 = l_Lean_Expr_const___override(x_84, x_80);
x_86 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_87 = l_Lean_Name_mkStr1(x_86);
x_88 = l_Lean_Expr_const___override(x_87, x_80);
lean_inc(x_74);
lean_inc(x_73);
x_89 = l_Lean_mkApp4(x_82, x_85, x_88, x_73, x_74);
x_90 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = l_Lean_Expr_const___override(x_91, x_80);
x_93 = lean_mk_string_unchecked("decLt", 5, 5);
x_94 = l_Lean_Name_mkStr2(x_83, x_93);
x_95 = l_Lean_Expr_const___override(x_94, x_80);
lean_inc(x_74);
lean_inc(x_73);
x_96 = l_Lean_mkAppB(x_95, x_73, x_74);
x_97 = lean_mk_string_unchecked("Eq", 2, 2);
x_98 = lean_mk_string_unchecked("refl", 4, 4);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = lean_unsigned_to_nat(1u);
x_101 = l_Lean_Level_ofNat(x_100);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_80);
lean_ctor_set(x_7, 0, x_101);
x_102 = l_Lean_Expr_const___override(x_99, x_7);
x_103 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_103);
x_104 = l_Lean_Name_mkStr1(x_103);
x_105 = l_Lean_Expr_const___override(x_104, x_80);
x_106 = lean_mk_string_unchecked("true", 4, 4);
x_107 = l_Lean_Name_mkStr2(x_103, x_106);
x_108 = l_Lean_Expr_const___override(x_107, x_80);
x_109 = l_Lean_mkAppB(x_102, x_105, x_108);
x_110 = l_Lean_mkApp3(x_92, x_89, x_96, x_109);
x_111 = lean_mk_string_unchecked("Fin", 3, 3);
x_112 = lean_mk_string_unchecked("mk", 2, 2);
x_113 = l_Lean_Name_mkStr2(x_111, x_112);
x_114 = l_Lean_Expr_const___override(x_113, x_80);
x_115 = l_Lean_mkApp3(x_114, x_74, x_73, x_110);
lean_ctor_set(x_17, 0, x_115);
return x_17;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_dec(x_17);
x_117 = lean_ctor_get(x_23, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_23, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_119 = x_23;
} else {
 lean_dec_ref(x_23);
 x_119 = lean_box(0);
}
x_120 = l_Lean_mkNatLit(x_118);
x_121 = l_Lean_mkNatLit(x_117);
x_122 = lean_mk_string_unchecked("LT", 2, 2);
x_123 = lean_mk_string_unchecked("lt", 2, 2);
x_124 = l_Lean_Name_mkStr2(x_122, x_123);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lean_Level_ofNat(x_125);
x_127 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_119;
 lean_ctor_set_tag(x_128, 1);
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Expr_const___override(x_124, x_128);
x_130 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_130);
x_131 = l_Lean_Name_mkStr1(x_130);
x_132 = l_Lean_Expr_const___override(x_131, x_127);
x_133 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = l_Lean_Expr_const___override(x_134, x_127);
lean_inc(x_121);
lean_inc(x_120);
x_136 = l_Lean_mkApp4(x_129, x_132, x_135, x_120, x_121);
x_137 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_138 = l_Lean_Name_mkStr1(x_137);
x_139 = l_Lean_Expr_const___override(x_138, x_127);
x_140 = lean_mk_string_unchecked("decLt", 5, 5);
x_141 = l_Lean_Name_mkStr2(x_130, x_140);
x_142 = l_Lean_Expr_const___override(x_141, x_127);
lean_inc(x_121);
lean_inc(x_120);
x_143 = l_Lean_mkAppB(x_142, x_120, x_121);
x_144 = lean_mk_string_unchecked("Eq", 2, 2);
x_145 = lean_mk_string_unchecked("refl", 4, 4);
x_146 = l_Lean_Name_mkStr2(x_144, x_145);
x_147 = lean_unsigned_to_nat(1u);
x_148 = l_Lean_Level_ofNat(x_147);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_127);
lean_ctor_set(x_7, 0, x_148);
x_149 = l_Lean_Expr_const___override(x_146, x_7);
x_150 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_150);
x_151 = l_Lean_Name_mkStr1(x_150);
x_152 = l_Lean_Expr_const___override(x_151, x_127);
x_153 = lean_mk_string_unchecked("true", 4, 4);
x_154 = l_Lean_Name_mkStr2(x_150, x_153);
x_155 = l_Lean_Expr_const___override(x_154, x_127);
x_156 = l_Lean_mkAppB(x_149, x_152, x_155);
x_157 = l_Lean_mkApp3(x_139, x_136, x_143, x_156);
x_158 = lean_mk_string_unchecked("Fin", 3, 3);
x_159 = lean_mk_string_unchecked("mk", 2, 2);
x_160 = l_Lean_Name_mkStr2(x_158, x_159);
x_161 = l_Lean_Expr_const___override(x_160, x_127);
x_162 = l_Lean_mkApp3(x_161, x_121, x_120, x_157);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_116);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_free_object(x_7);
lean_dec(x_9);
x_164 = !lean_is_exclusive(x_17);
if (x_164 == 0)
{
return x_17;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_17, 0);
x_166 = lean_ctor_get(x_17, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_17);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = !lean_is_exclusive(x_14);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_14, 0);
lean_dec(x_169);
x_170 = lean_ctor_get(x_15, 0);
lean_inc(x_170);
lean_dec(x_15);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_to_int(x_171);
x_173 = lean_int_dec_lt(x_170, x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_mk_string_unchecked("Int", 3, 3);
x_175 = lean_mk_string_unchecked("ofNat", 5, 5);
x_176 = l_Lean_Name_mkStr2(x_174, x_175);
x_177 = lean_box(0);
x_178 = l_Lean_Expr_const___override(x_176, x_177);
x_179 = l_Int_toNat(x_170);
lean_dec(x_170);
x_180 = l_Lean_mkNatLit(x_179);
x_181 = l_Lean_Expr_app___override(x_178, x_180);
lean_ctor_set(x_14, 0, x_181);
return x_14;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_182 = lean_mk_string_unchecked("Int", 3, 3);
x_183 = lean_mk_string_unchecked("negSucc", 7, 7);
x_184 = l_Lean_Name_mkStr2(x_182, x_183);
x_185 = lean_box(0);
x_186 = l_Lean_Expr_const___override(x_184, x_185);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_nat_to_int(x_187);
x_189 = lean_int_add(x_170, x_188);
lean_dec(x_188);
lean_dec(x_170);
x_190 = lean_int_neg(x_189);
lean_dec(x_189);
x_191 = l_Int_toNat(x_190);
lean_dec(x_190);
x_192 = l_Lean_mkNatLit(x_191);
x_193 = l_Lean_Expr_app___override(x_186, x_192);
lean_ctor_set(x_14, 0, x_193);
return x_14;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_14, 1);
lean_inc(x_194);
lean_dec(x_14);
x_195 = lean_ctor_get(x_15, 0);
lean_inc(x_195);
lean_dec(x_15);
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_nat_to_int(x_196);
x_198 = lean_int_dec_lt(x_195, x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_199 = lean_mk_string_unchecked("Int", 3, 3);
x_200 = lean_mk_string_unchecked("ofNat", 5, 5);
x_201 = l_Lean_Name_mkStr2(x_199, x_200);
x_202 = lean_box(0);
x_203 = l_Lean_Expr_const___override(x_201, x_202);
x_204 = l_Int_toNat(x_195);
lean_dec(x_195);
x_205 = l_Lean_mkNatLit(x_204);
x_206 = l_Lean_Expr_app___override(x_203, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_194);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_208 = lean_mk_string_unchecked("Int", 3, 3);
x_209 = lean_mk_string_unchecked("negSucc", 7, 7);
x_210 = l_Lean_Name_mkStr2(x_208, x_209);
x_211 = lean_box(0);
x_212 = l_Lean_Expr_const___override(x_210, x_211);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_to_int(x_213);
x_215 = lean_int_add(x_195, x_214);
lean_dec(x_214);
lean_dec(x_195);
x_216 = lean_int_neg(x_215);
lean_dec(x_215);
x_217 = l_Int_toNat(x_216);
lean_dec(x_216);
x_218 = l_Lean_mkNatLit(x_217);
x_219 = l_Lean_Expr_app___override(x_212, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_194);
return x_220;
}
}
}
}
else
{
uint8_t x_221; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_14);
if (x_221 == 0)
{
return x_14;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_14, 0);
x_223 = lean_ctor_get(x_14, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_14);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_11);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_226 = lean_ctor_get(x_11, 0);
lean_dec(x_226);
x_227 = lean_ctor_get(x_12, 0);
lean_inc(x_227);
lean_dec(x_12);
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_nat_dec_eq(x_227, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_230 = lean_mk_string_unchecked("Nat", 3, 3);
x_231 = lean_mk_string_unchecked("succ", 4, 4);
x_232 = l_Lean_Name_mkStr2(x_230, x_231);
x_233 = lean_box(0);
x_234 = l_Lean_Expr_const___override(x_232, x_233);
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_sub(x_227, x_235);
lean_dec(x_227);
x_237 = l_Lean_mkNatLit(x_236);
x_238 = l_Lean_Expr_app___override(x_234, x_237);
lean_ctor_set(x_11, 0, x_238);
return x_11;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_227);
x_239 = lean_mk_string_unchecked("Nat", 3, 3);
x_240 = lean_mk_string_unchecked("zero", 4, 4);
x_241 = l_Lean_Name_mkStr2(x_239, x_240);
x_242 = lean_box(0);
x_243 = l_Lean_Expr_const___override(x_241, x_242);
lean_ctor_set(x_11, 0, x_243);
return x_11;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = lean_ctor_get(x_11, 1);
lean_inc(x_244);
lean_dec(x_11);
x_245 = lean_ctor_get(x_12, 0);
lean_inc(x_245);
lean_dec(x_12);
x_246 = lean_unsigned_to_nat(0u);
x_247 = lean_nat_dec_eq(x_245, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_248 = lean_mk_string_unchecked("Nat", 3, 3);
x_249 = lean_mk_string_unchecked("succ", 4, 4);
x_250 = l_Lean_Name_mkStr2(x_248, x_249);
x_251 = lean_box(0);
x_252 = l_Lean_Expr_const___override(x_250, x_251);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_sub(x_245, x_253);
lean_dec(x_245);
x_255 = l_Lean_mkNatLit(x_254);
x_256 = l_Lean_Expr_app___override(x_252, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_244);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_245);
x_258 = lean_mk_string_unchecked("Nat", 3, 3);
x_259 = lean_mk_string_unchecked("zero", 4, 4);
x_260 = l_Lean_Name_mkStr2(x_258, x_259);
x_261 = lean_box(0);
x_262 = l_Lean_Expr_const___override(x_260, x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_244);
return x_263;
}
}
}
}
else
{
uint8_t x_264; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_264 = !lean_is_exclusive(x_11);
if (x_264 == 0)
{
return x_11;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_11, 0);
x_266 = lean_ctor_get(x_11, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_11);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_7, 0);
x_269 = lean_ctor_get(x_7, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_270 = l_Lean_Meta_getNatValue_x3f(x_268, x_2, x_3, x_4, x_5, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_268);
x_273 = l_Lean_Meta_getIntValue_x3f(x_268, x_2, x_3, x_4, x_5, x_272);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
lean_inc(x_268);
x_276 = l_Lean_Meta_getFinValue_x3f(x_268, x_2, x_3, x_4, x_5, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_268);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_268);
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
lean_dec(x_277);
x_282 = lean_ctor_get(x_276, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_283 = x_276;
} else {
 lean_dec_ref(x_276);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_286 = x_281;
} else {
 lean_dec_ref(x_281);
 x_286 = lean_box(0);
}
x_287 = l_Lean_mkNatLit(x_285);
x_288 = l_Lean_mkNatLit(x_284);
x_289 = lean_mk_string_unchecked("LT", 2, 2);
x_290 = lean_mk_string_unchecked("lt", 2, 2);
x_291 = l_Lean_Name_mkStr2(x_289, x_290);
x_292 = lean_unsigned_to_nat(0u);
x_293 = l_Lean_Level_ofNat(x_292);
x_294 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_286;
 lean_ctor_set_tag(x_295, 1);
}
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_Lean_Expr_const___override(x_291, x_295);
x_297 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_297);
x_298 = l_Lean_Name_mkStr1(x_297);
x_299 = l_Lean_Expr_const___override(x_298, x_294);
x_300 = lean_mk_string_unchecked("instLTNat", 9, 9);
x_301 = l_Lean_Name_mkStr1(x_300);
x_302 = l_Lean_Expr_const___override(x_301, x_294);
lean_inc(x_288);
lean_inc(x_287);
x_303 = l_Lean_mkApp4(x_296, x_299, x_302, x_287, x_288);
x_304 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_305 = l_Lean_Name_mkStr1(x_304);
x_306 = l_Lean_Expr_const___override(x_305, x_294);
x_307 = lean_mk_string_unchecked("decLt", 5, 5);
x_308 = l_Lean_Name_mkStr2(x_297, x_307);
x_309 = l_Lean_Expr_const___override(x_308, x_294);
lean_inc(x_288);
lean_inc(x_287);
x_310 = l_Lean_mkAppB(x_309, x_287, x_288);
x_311 = lean_mk_string_unchecked("Eq", 2, 2);
x_312 = lean_mk_string_unchecked("refl", 4, 4);
x_313 = l_Lean_Name_mkStr2(x_311, x_312);
x_314 = lean_unsigned_to_nat(1u);
x_315 = l_Lean_Level_ofNat(x_314);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_294);
x_317 = l_Lean_Expr_const___override(x_313, x_316);
x_318 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_318);
x_319 = l_Lean_Name_mkStr1(x_318);
x_320 = l_Lean_Expr_const___override(x_319, x_294);
x_321 = lean_mk_string_unchecked("true", 4, 4);
x_322 = l_Lean_Name_mkStr2(x_318, x_321);
x_323 = l_Lean_Expr_const___override(x_322, x_294);
x_324 = l_Lean_mkAppB(x_317, x_320, x_323);
x_325 = l_Lean_mkApp3(x_306, x_303, x_310, x_324);
x_326 = lean_mk_string_unchecked("Fin", 3, 3);
x_327 = lean_mk_string_unchecked("mk", 2, 2);
x_328 = l_Lean_Name_mkStr2(x_326, x_327);
x_329 = l_Lean_Expr_const___override(x_328, x_294);
x_330 = l_Lean_mkApp3(x_329, x_288, x_287, x_325);
if (lean_is_scalar(x_283)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_283;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_282);
return x_331;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_268);
x_332 = lean_ctor_get(x_276, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_276, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_334 = x_276;
} else {
 lean_dec_ref(x_276);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_dec(x_268);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_336 = lean_ctor_get(x_273, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_337 = x_273;
} else {
 lean_dec_ref(x_273);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_274, 0);
lean_inc(x_338);
lean_dec(x_274);
x_339 = lean_unsigned_to_nat(0u);
x_340 = lean_nat_to_int(x_339);
x_341 = lean_int_dec_lt(x_338, x_340);
lean_dec(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_342 = lean_mk_string_unchecked("Int", 3, 3);
x_343 = lean_mk_string_unchecked("ofNat", 5, 5);
x_344 = l_Lean_Name_mkStr2(x_342, x_343);
x_345 = lean_box(0);
x_346 = l_Lean_Expr_const___override(x_344, x_345);
x_347 = l_Int_toNat(x_338);
lean_dec(x_338);
x_348 = l_Lean_mkNatLit(x_347);
x_349 = l_Lean_Expr_app___override(x_346, x_348);
if (lean_is_scalar(x_337)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_337;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_336);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_351 = lean_mk_string_unchecked("Int", 3, 3);
x_352 = lean_mk_string_unchecked("negSucc", 7, 7);
x_353 = l_Lean_Name_mkStr2(x_351, x_352);
x_354 = lean_box(0);
x_355 = l_Lean_Expr_const___override(x_353, x_354);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_to_int(x_356);
x_358 = lean_int_add(x_338, x_357);
lean_dec(x_357);
lean_dec(x_338);
x_359 = lean_int_neg(x_358);
lean_dec(x_358);
x_360 = l_Int_toNat(x_359);
lean_dec(x_359);
x_361 = l_Lean_mkNatLit(x_360);
x_362 = l_Lean_Expr_app___override(x_355, x_361);
if (lean_is_scalar(x_337)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_337;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_336);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_268);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_364 = lean_ctor_get(x_273, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_273, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_366 = x_273;
} else {
 lean_dec_ref(x_273);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_dec(x_268);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_368 = lean_ctor_get(x_270, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_369 = x_270;
} else {
 lean_dec_ref(x_270);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_271, 0);
lean_inc(x_370);
lean_dec(x_271);
x_371 = lean_unsigned_to_nat(0u);
x_372 = lean_nat_dec_eq(x_370, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_373 = lean_mk_string_unchecked("Nat", 3, 3);
x_374 = lean_mk_string_unchecked("succ", 4, 4);
x_375 = l_Lean_Name_mkStr2(x_373, x_374);
x_376 = lean_box(0);
x_377 = l_Lean_Expr_const___override(x_375, x_376);
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_nat_sub(x_370, x_378);
lean_dec(x_370);
x_380 = l_Lean_mkNatLit(x_379);
x_381 = l_Lean_Expr_app___override(x_377, x_380);
if (lean_is_scalar(x_369)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_369;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_368);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_370);
x_383 = lean_mk_string_unchecked("Nat", 3, 3);
x_384 = lean_mk_string_unchecked("zero", 4, 4);
x_385 = l_Lean_Name_mkStr2(x_383, x_384);
x_386 = lean_box(0);
x_387 = l_Lean_Expr_const___override(x_385, x_386);
if (lean_is_scalar(x_369)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_369;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_368);
return x_388;
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_268);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_389 = lean_ctor_get(x_270, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_270, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_391 = x_270;
} else {
 lean_dec_ref(x_270);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_litToCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_litToCtor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_9, x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_21 = l_Lean_Expr_cleanupAnnotations(x_11);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_box(0);
lean_inc(x_21);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = lean_mk_string_unchecked("List", 4, 4);
x_26 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_Expr_isConstOf(x_24, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isApp(x_24);
if (x_29 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_20;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_inc(x_24);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = lean_mk_string_unchecked("cons", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_25, x_33);
x_35 = l_Lean_Expr_isConstOf(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
if (x_35 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_20;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = lean_apply_6(x_1, x_36, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_14);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_14);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_9);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_52 = lean_ctor_get(x_38, 0);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_dec(x_21);
x_54 = lean_array_push(x_14, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_23);
lean_ctor_set(x_56, 1, x_55);
x_2 = x_56;
x_7 = x_51;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_37);
if (x_58 == 0)
{
return x_37;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_37, 0);
x_60 = lean_ctor_get(x_37, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_37);
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
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_9);
lean_ctor_set(x_62, 1, x_14);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_23);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_12);
return x_64;
}
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
if (lean_is_scalar(x_13)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_13;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_consumeMData(x_1);
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_8, x_4, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_box(0);
lean_ctor_set(x_9, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0___redArg(x_2, x_15, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_mk_empty_array_with_capacity(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Loop_forIn_loop___at___Lean_Meta_getListLitOf_x3f_spec__0___redArg(x_2, x_44, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_47);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_55 = x_45;
} else {
 lean_dec_ref(x_45);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getListLitOf_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getListLitOf_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLitOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getListLitOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getListLit_x3f___lam__0___boxed), 6, 0);
x_8 = l_Lean_Meta_getListLitOf_x3f___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getListLit_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getListLit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getListLit_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
x_8 = l_Lean_Expr_consumeMData(x_1);
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_8, x_4, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_10, x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_19 = l_Lean_Expr_cleanupAnnotations(x_13);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_18;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("List", 4, 4);
x_25 = lean_mk_string_unchecked("toArray", 7, 7);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = l_Lean_Expr_isConstOf(x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
if (x_27 == 0)
{
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Meta_getListLitOf_x3f___redArg(x_28, x_2, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_28);
return x_29;
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getArrayLitOf_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getArrayLitOf_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLitOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getArrayLitOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getListLit_x3f___lam__0___boxed), 6, 0);
x_8 = l_Lean_Meta_getArrayLitOf_x3f___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayLit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getArrayLit_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
