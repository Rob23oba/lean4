// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.String
// Imports: Lean.ToExpr Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
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
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_765_(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_174_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_644_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_842_(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_877_(lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_685_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_804_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_838_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_763_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_879_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_761_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_724_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_648_(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t l_String_decLE(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_172_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceMk___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_726_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_329_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_840_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_331_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_327_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_722_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_915_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_683_(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_176_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceNe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_802_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_881_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_800_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_687_(lean_object*);
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_919_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_917_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_reduceMk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_646_(lean_object*);
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_getStringValue_x3f(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_fromExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_fromExpr_x3f___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_fromExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_fromExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_mk_string_unchecked("HAppend", 7, 7);
x_4 = lean_mk_string_unchecked("hAppend", 7, 7);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(6u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = l_String_fromExpr_x3f___redArg(x_12, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = l_Lean_Expr_appArg_x21(x_1);
x_27 = l_String_fromExpr_x3f___redArg(x_26, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_25);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 0, x_31);
lean_ctor_set(x_27, 0, x_14);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_14);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_string_append(x_25, x_38);
lean_dec(x_38);
x_40 = l_Lean_mkStrLit(x_39);
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_40);
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_string_append(x_25, x_41);
lean_dec(x_41);
x_43 = l_Lean_mkStrLit(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_27, 0, x_44);
return x_27;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_47 = x_28;
} else {
 lean_dec_ref(x_28);
 x_47 = lean_box(0);
}
x_48 = lean_string_append(x_25, x_46);
lean_dec(x_46);
x_49 = l_Lean_mkStrLit(x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_47;
 lean_ctor_set_tag(x_50, 0);
}
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
lean_dec(x_14);
x_53 = l_Lean_Expr_appArg_x21(x_1);
x_54 = l_String_fromExpr_x3f___redArg(x_53, x_23);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_52);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
x_65 = lean_string_append(x_52, x_63);
lean_dec(x_63);
x_66 = l_Lean_mkStrLit(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_64;
 lean_ctor_set_tag(x_67, 0);
}
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceAppend___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_reduceAppend___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_reduceAppend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceAppend(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_172_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceAppend", 12, 12);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("HAppend", 7, 7);
x_6 = lean_mk_string_unchecked("hAppend", 7, 7);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(7u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
lean_inc(x_12);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_alloc_closure((void*)(l_String_reduceAppend___boxed), 9, 0);
x_24 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_22, x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_174_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceAppend", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceAppend___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_176_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceAppend", 12, 12);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceAppend___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_mk_string_unchecked("List", 4, 4);
x_9 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_8);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_mk_string_unchecked("cons", 4, 4);
x_14 = l_Lean_Name_mkStr2(x_8, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_1, x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Expr_appFn_x21(x_1);
x_21 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_getCharValue_x3f(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_35 = lean_unbox_uint32(x_33);
lean_dec(x_33);
x_36 = lean_string_push(x_2, x_35);
x_1 = x_34;
x_2 = x_36;
x_7 = x_32;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = l_Lean_mkStrLit(x_2);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_reduceMk___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("String", 6, 6);
x_8 = lean_mk_string_unchecked("mk", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appArg_x21(x_1);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(x_15, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_reduceMk(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceMk___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceMk___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_reduceMk___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_reduceMk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceMk(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_327_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceMk", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("mk", 2, 2);
x_6 = l_Lean_Name_mkStr2(x_2, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(3);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_alloc_closure((void*)(l_String_reduceMk___boxed), 9, 0);
x_15 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_13, x_14, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_329_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceMk", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceMk___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_331_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceMk", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceMk___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_4);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_String_fromExpr_x3f___redArg(x_15, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = l_Lean_Expr_appArg_x21(x_4);
x_30 = l_String_fromExpr_x3f___redArg(x_29, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_34);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_apply_2(x_3, x_28, x_39);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_41, x_5, x_6, x_7, x_8, x_38);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = l_Lean_Expr_appArg_x21(x_4);
x_45 = l_String_fromExpr_x3f___redArg(x_44, x_26);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_apply_2(x_3, x_43, x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
x_56 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_55, x_5, x_6, x_7, x_8, x_52);
return x_56;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Expr_appFn_x21(x_4);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
x_19 = l_String_fromExpr_x3f___redArg(x_18, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = l_Lean_Expr_appArg_x21(x_4);
x_33 = l_String_fromExpr_x3f___redArg(x_32, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 0, x_37);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_free_object(x_20);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_apply_2(x_3, x_31, x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_44, x_8, x_9, x_10, x_11, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
lean_dec(x_20);
x_47 = l_Lean_Expr_appArg_x21(x_4);
x_48 = l_String_fromExpr_x3f___redArg(x_47, x_29);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_apply_2(x_3, x_46, x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
x_59 = l_Lean_Meta_Simp_evalPropStep___redArg(x_4, x_58, x_8, x_9, x_10, x_11, x_55);
return x_59;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceBinPred___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_String_reduceBinPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Expr_appFn_x21(x_4);
x_11 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_12 = l_String_fromExpr_x3f___redArg(x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_26 = x_13;
} else {
 lean_dec_ref(x_13);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_appArg_x21(x_4);
x_28 = l_String_fromExpr_x3f___redArg(x_27, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_12);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_apply_2(x_3, x_25, x_38);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_mk_string_unchecked("Bool", 4, 4);
x_42 = lean_mk_string_unchecked("false", 5, 5);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Expr_const___override(x_43, x_44);
x_32 = x_45;
goto block_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_mk_string_unchecked("Bool", 4, 4);
x_47 = lean_mk_string_unchecked("true", 4, 4);
x_48 = l_Lean_Name_mkStr2(x_46, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_const___override(x_48, x_49);
x_32 = x_50;
goto block_35;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
if (lean_is_scalar(x_26)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_26;
 lean_ctor_set_tag(x_33, 0);
}
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_dec(x_12);
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_53 = x_13;
} else {
 lean_dec_ref(x_13);
 x_53 = lean_box(0);
}
x_54 = l_Lean_Expr_appArg_x21(x_4);
x_55 = l_String_fromExpr_x3f___redArg(x_54, x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_3);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_56, 0);
lean_inc(x_66);
lean_dec(x_56);
x_67 = lean_apply_2(x_3, x_52, x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_mk_string_unchecked("Bool", 4, 4);
x_70 = lean_mk_string_unchecked("false", 5, 5);
x_71 = l_Lean_Name_mkStr2(x_69, x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Expr_const___override(x_71, x_72);
x_59 = x_73;
goto block_62;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_mk_string_unchecked("Bool", 4, 4);
x_75 = lean_mk_string_unchecked("true", 4, 4);
x_76 = l_Lean_Name_mkStr2(x_74, x_75);
x_77 = lean_box(0);
x_78 = l_Lean_Expr_const___override(x_76, x_77);
x_59 = x_78;
goto block_62;
}
}
block_62:
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_53;
 lean_ctor_set_tag(x_60, 0);
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Expr_appFn_x21(x_4);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
x_19 = l_String_fromExpr_x3f___redArg(x_18, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_33 = x_20;
} else {
 lean_dec_ref(x_20);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Expr_appArg_x21(x_4);
x_35 = l_String_fromExpr_x3f___redArg(x_34, x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_19, 1, x_37);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_19);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_apply_2(x_3, x_32, x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_mk_string_unchecked("Bool", 4, 4);
x_49 = lean_mk_string_unchecked("false", 5, 5);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_Expr_const___override(x_50, x_51);
x_39 = x_52;
goto block_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_mk_string_unchecked("Bool", 4, 4);
x_54 = lean_mk_string_unchecked("true", 4, 4);
x_55 = l_Lean_Name_mkStr2(x_53, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Expr_const___override(x_55, x_56);
x_39 = x_57;
goto block_42;
}
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_33;
 lean_ctor_set_tag(x_40, 0);
}
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_dec(x_19);
x_59 = lean_ctor_get(x_20, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_60 = x_20;
} else {
 lean_dec_ref(x_20);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Expr_appArg_x21(x_4);
x_62 = l_String_fromExpr_x3f___redArg(x_61, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_3);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
lean_dec(x_63);
x_74 = lean_apply_2(x_3, x_59, x_73);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_mk_string_unchecked("Bool", 4, 4);
x_77 = lean_mk_string_unchecked("false", 5, 5);
x_78 = l_Lean_Name_mkStr2(x_76, x_77);
x_79 = lean_box(0);
x_80 = l_Lean_Expr_const___override(x_78, x_79);
x_66 = x_80;
goto block_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_mk_string_unchecked("Bool", 4, 4);
x_82 = lean_mk_string_unchecked("true", 4, 4);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_83, x_84);
x_66 = x_85;
goto block_69;
}
}
block_69:
{
lean_object* x_67; lean_object* x_68; 
if (lean_is_scalar(x_60)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_60;
 lean_ctor_set_tag(x_67, 0);
}
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_reduceBoolPred___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_reduceBoolPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_String_reduceBoolPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("LT", 2, 2);
x_8 = lean_mk_string_unchecked("lt", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_String_fromExpr_x3f___redArg(x_16, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_String_fromExpr_x3f___redArg(x_30, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_string_dec_lt(x_29, x_40);
lean_dec(x_40);
lean_dec(x_29);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = l_Lean_Expr_appArg_x21(x_1);
x_45 = l_String_fromExpr_x3f___redArg(x_44, x_27);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_string_dec_lt(x_43, x_53);
lean_dec(x_53);
lean_dec(x_43);
x_55 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_54, x_2, x_3, x_4, x_5, x_52);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceLT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_644_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LT", 2, 2);
x_6 = lean_mk_string_unchecked("lt", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_646_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_648_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceLT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceLT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("LE", 2, 2);
x_8 = lean_mk_string_unchecked("le", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_String_fromExpr_x3f___redArg(x_16, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_String_fromExpr_x3f___redArg(x_30, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_String_decLE(x_29, x_40);
lean_dec(x_40);
lean_dec(x_29);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = l_Lean_Expr_appArg_x21(x_1);
x_45 = l_String_fromExpr_x3f___redArg(x_44, x_27);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_String_decLE(x_43, x_53);
lean_dec(x_53);
lean_dec(x_43);
x_55 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_54, x_2, x_3, x_4, x_5, x_52);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceLE___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_683_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LE", 2, 2);
x_6 = lean_mk_string_unchecked("le", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_685_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_687_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceLE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceLE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("GT", 2, 2);
x_8 = lean_mk_string_unchecked("gt", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_String_fromExpr_x3f___redArg(x_16, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_String_fromExpr_x3f___redArg(x_30, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_string_dec_lt(x_40, x_29);
lean_dec(x_29);
lean_dec(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = l_Lean_Expr_appArg_x21(x_1);
x_45 = l_String_fromExpr_x3f___redArg(x_44, x_27);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_string_dec_lt(x_53, x_43);
lean_dec(x_43);
lean_dec(x_53);
x_55 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_54, x_2, x_3, x_4, x_5, x_52);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceGT___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceGT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceGT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_722_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LT", 2, 2);
x_6 = lean_mk_string_unchecked("lt", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_724_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_726_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceGT", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceGT___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_mk_string_unchecked("GE", 2, 2);
x_8 = lean_mk_string_unchecked("ge", 2, 2);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_String_fromExpr_x3f___redArg(x_16, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = l_Lean_Expr_appArg_x21(x_1);
x_31 = l_String_fromExpr_x3f___redArg(x_30, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_35);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_18);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_String_decLE(x_40, x_29);
lean_dec(x_29);
lean_dec(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = l_Lean_Expr_appArg_x21(x_1);
x_45 = l_String_fromExpr_x3f___redArg(x_44, x_27);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_String_decLE(x_53, x_43);
lean_dec(x_43);
lean_dec(x_53);
x_55 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_54, x_2, x_3, x_4, x_5, x_52);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceGE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceGE___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceGE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceGE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_761_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("LE", 2, 2);
x_6 = lean_mk_string_unchecked("le", 2, 2);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_763_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_765_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceGE", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceGE___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Eq", 2, 2);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_String_fromExpr_x3f___redArg(x_15, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_String_fromExpr_x3f___redArg(x_29, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_34);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_string_dec_eq(x_28, x_39);
lean_dec(x_39);
lean_dec(x_28);
x_41 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_40, x_2, x_3, x_4, x_5, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = l_Lean_Expr_appArg_x21(x_1);
x_44 = l_String_fromExpr_x3f___redArg(x_43, x_26);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_string_dec_eq(x_42, x_52);
lean_dec(x_52);
lean_dec(x_42);
x_54 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_53, x_2, x_3, x_4, x_5, x_51);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceEq___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_800_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Eq", 2, 2);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Name_mkStr1(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(3);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_8);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
x_20 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_18, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_802_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_804_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceEq", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Ne", 2, 2);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_1);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_String_fromExpr_x3f___redArg(x_15, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_String_fromExpr_x3f___redArg(x_29, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_34);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_17);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_string_dec_eq(x_28, x_39);
lean_dec(x_39);
lean_dec(x_28);
x_41 = l_instDecidableNot___redArg(x_40);
x_42 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_41, x_2, x_3, x_4, x_5, x_38);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = l_Lean_Expr_appArg_x21(x_1);
x_45 = l_String_fromExpr_x3f___redArg(x_44, x_26);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_string_dec_eq(x_43, x_53);
lean_dec(x_53);
lean_dec(x_43);
x_55 = l_instDecidableNot___redArg(x_54);
x_56 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_55, x_2, x_3, x_4, x_5, x_52);
return x_56;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceNe___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_838_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("Not", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("Eq", 2, 2);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Name_mkStr1(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(3);
x_17 = lean_unsigned_to_nat(5u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_array_push(x_18, x_8);
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_16);
x_23 = lean_array_push(x_22, x_16);
x_24 = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
x_25 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_4, x_23, x_24, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_840_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_842_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceNe", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_mk_string_unchecked("BEq", 3, 3);
x_4 = lean_mk_string_unchecked("beq", 3, 3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = l_String_fromExpr_x3f___redArg(x_12, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_13, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_27 = x_14;
} else {
 lean_dec_ref(x_14);
 x_27 = lean_box(0);
}
x_28 = l_Lean_Expr_appArg_x21(x_1);
x_29 = l_String_fromExpr_x3f___redArg(x_28, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_13, 1, x_31);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_free_object(x_13);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_string_dec_eq(x_26, x_39);
lean_dec(x_39);
lean_dec(x_26);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_mk_string_unchecked("Bool", 4, 4);
x_42 = lean_mk_string_unchecked("false", 5, 5);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Expr_const___override(x_43, x_44);
x_33 = x_45;
goto block_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_mk_string_unchecked("Bool", 4, 4);
x_47 = lean_mk_string_unchecked("true", 4, 4);
x_48 = l_Lean_Name_mkStr2(x_46, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_const___override(x_48, x_49);
x_33 = x_50;
goto block_36;
}
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
if (lean_is_scalar(x_27)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_27;
 lean_ctor_set_tag(x_34, 0);
}
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_dec(x_13);
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_53 = x_14;
} else {
 lean_dec_ref(x_14);
 x_53 = lean_box(0);
}
x_54 = l_Lean_Expr_appArg_x21(x_1);
x_55 = l_String_fromExpr_x3f___redArg(x_54, x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_52);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_56, 0);
lean_inc(x_66);
lean_dec(x_56);
x_67 = lean_string_dec_eq(x_52, x_66);
lean_dec(x_66);
lean_dec(x_52);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_mk_string_unchecked("Bool", 4, 4);
x_69 = lean_mk_string_unchecked("false", 5, 5);
x_70 = l_Lean_Name_mkStr2(x_68, x_69);
x_71 = lean_box(0);
x_72 = l_Lean_Expr_const___override(x_70, x_71);
x_59 = x_72;
goto block_62;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_mk_string_unchecked("Bool", 4, 4);
x_74 = lean_mk_string_unchecked("true", 4, 4);
x_75 = l_Lean_Name_mkStr2(x_73, x_74);
x_76 = lean_box(0);
x_77 = l_Lean_Expr_const___override(x_75, x_76);
x_59 = x_77;
goto block_62;
}
}
block_62:
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_53;
 lean_ctor_set_tag(x_60, 0);
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceBEq___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_reduceBEq___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_reduceBEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceBEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_877_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("BEq", 3, 3);
x_6 = lean_mk_string_unchecked("beq", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Name_mkStr1(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(3);
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
x_22 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_20, x_21, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_879_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_881_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceBEq", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceBEq___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_mk_string_unchecked("bne", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_unsigned_to_nat(4u);
x_6 = l_Lean_Expr_isAppOfArity(x_1, x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Expr_appFn_x21(x_1);
x_11 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_12 = l_String_fromExpr_x3f___redArg(x_11, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_26 = x_13;
} else {
 lean_dec_ref(x_13);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_appArg_x21(x_1);
x_28 = l_String_fromExpr_x3f___redArg(x_27, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_free_object(x_12);
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
x_45 = lean_string_dec_eq(x_25, x_44);
lean_dec(x_44);
lean_dec(x_25);
if (x_45 == 0)
{
if (x_6 == 0)
{
goto block_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_mk_string_unchecked("Bool", 4, 4);
x_47 = lean_mk_string_unchecked("true", 4, 4);
x_48 = l_Lean_Name_mkStr2(x_46, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_const___override(x_48, x_49);
x_32 = x_50;
goto block_35;
}
}
else
{
goto block_41;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
if (lean_is_scalar(x_26)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_26;
 lean_ctor_set_tag(x_33, 0);
}
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
block_41:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_mk_string_unchecked("Bool", 4, 4);
x_37 = lean_mk_string_unchecked("false", 5, 5);
x_38 = l_Lean_Name_mkStr2(x_36, x_37);
x_39 = lean_box(0);
x_40 = l_Lean_Expr_const___override(x_38, x_39);
x_32 = x_40;
goto block_35;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_dec(x_12);
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_53 = x_13;
} else {
 lean_dec_ref(x_13);
 x_53 = lean_box(0);
}
x_54 = l_Lean_Expr_appArg_x21(x_1);
x_55 = l_String_fromExpr_x3f___redArg(x_54, x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_52);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_57);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_56, 0);
lean_inc(x_72);
lean_dec(x_56);
x_73 = lean_string_dec_eq(x_52, x_72);
lean_dec(x_72);
lean_dec(x_52);
if (x_73 == 0)
{
if (x_6 == 0)
{
goto block_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_mk_string_unchecked("Bool", 4, 4);
x_75 = lean_mk_string_unchecked("true", 4, 4);
x_76 = l_Lean_Name_mkStr2(x_74, x_75);
x_77 = lean_box(0);
x_78 = l_Lean_Expr_const___override(x_76, x_77);
x_59 = x_78;
goto block_62;
}
}
else
{
goto block_68;
}
}
block_62:
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_53;
 lean_ctor_set_tag(x_60, 0);
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
block_68:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_mk_string_unchecked("Bool", 4, 4);
x_64 = lean_mk_string_unchecked("false", 5, 5);
x_65 = l_Lean_Name_mkStr2(x_63, x_64);
x_66 = lean_box(0);
x_67 = l_Lean_Expr_const___override(x_65, x_66);
x_59 = x_67;
goto block_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceBNe___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_reduceBNe___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_reduceBNe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_reduceBNe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_915_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_mk_string_unchecked("bne", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Name_mkStr1(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(3);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_8);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
x_21 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_4, x_19, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_917_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_919_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = lean_mk_string_unchecked("reduceBNe", 9, 9);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_String_reduceBNe___boxed), 9, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_4, x_8, x_7, x_1);
return x_9;
}
}
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_172_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_174_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceAppend_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_176_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_327_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_329_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceMk_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_331_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_644_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_646_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceLT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_648_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_683_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_685_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceLE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_687_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_722_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_724_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceGT_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_726_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_761_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_763_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceGE_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_765_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_800_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_802_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_804_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_838_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_840_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_842_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_877_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_879_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceBEq_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_881_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_915_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_917_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_String_reduceBNe_declare__1____x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String___hyg_919_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
